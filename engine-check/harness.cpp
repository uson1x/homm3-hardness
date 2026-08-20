/*
 * harness.cpp — drives the real VCMI combat classes on the instances used by the
 * candidate-A reductions, and prints the engine's numbers as JSON.
 *
 * Nothing here reimplements a rule. Every number printed comes out of a VCMI class
 * compiled from a local VCMI checkout, $VCMI_CHECKOUT (commit b5cee70; the public
 * anchor is vcmi/vcmi deeab240c..., byte-identical on every cited path, see ../README.md):
 *
 *   damage / kills   lib/battle/DamageCalculator.cpp   (DamageCalculator::calculateDmgRange)
 *   health pool      lib/battle/CUnitState.cpp         (CHealth via CUnitState::damage)
 *   count()          lib/battle/CUnitState.cpp         (CHealth::getCount)
 *   retaliations     lib/battle/CUnitState.cpp         (CRetaliations / ableToRetaliate)
 *   stat lookup      lib/battle/CUnitState.cpp         (getAttack/getDefense/getMinDamage/...)
 *
 * Creature statistics are supplied as bonuses, which is how the engine itself carries
 * them (lib/bonuses/BonusCache.cpp:177-205 lists the selectors used for each stat).
 * That is what lets us instantiate the arbitrary-statistic creatures the generalised
 * game allows, without inventing a creature mod.
 *
 * Input:  cases.json   Output: stdout, one JSON document.
 */

#include "StdInc.h"

#include "../lib/GameLibrary.h"
#include "../lib/IGameSettings.h"
#include "../lib/battle/BattleAttackInfo.h"
#include "../lib/battle/CBattleInfoCallback.h"
#include "../lib/battle/CUnitState.h"
#include "../lib/battle/DamageCalculator.h"
#include "../lib/CCreatureHandler.h"
#include "../lib/bonuses/Bonus.h"
#include "../lib/json/JsonNode.h"

#include "mock/BattleFake.h"
#include "mock/mock_BonusBearer.h"
#include "mock/mock_UnitEnvironment.h"
#include "mock/mock_UnitInfo.h"

#include <fstream>
#include <iomanip>
#include <iostream>
#include <memory>

using namespace ::testing;
using ::battle::CUnitStateDetached;

namespace
{

/// A creature type plus a stack size, in the terms of MODEL.md Definitions 3.1/3.2.
struct Spec
{
	std::string name;
	int attack = 10;
	int defense = 10;
	int dmgMin = 1;
	int dmgMax = 1;
	int hp = 10;
	int speed = 2;
	int count = 1;
	bool shooter = false;
	int shots = 32;
	bool noMeleePenalty = false;
	bool noRetaliation = false;
	bool blocksRetaliation = false;
	int additionalRetaliations = 0;
	bool unlimitedRetaliations = false;
	// turn-order cases only: which side the unit fights on, its slot, and its
	// current-round state flags (CUnitState.h:130-142, all public state).
	bool defenderSide = false;
	int slot = 0;
	bool waiting = false;
	bool defending = false;
};

/// A unit the engine will accept: real CUnitState over a mocked info/bonus source.
class Fake
{
public:
	explicit Fake(const Spec & spec)
		: spec(spec)
	{
		ON_CALL(info, unitBaseAmount()).WillByDefault(Return(spec.count));
		ON_CALL(info, unitId()).WillByDefault(Return(nextId++));
		ON_CALL(info, unitSide()).WillByDefault(Return(spec.defenderSide ? BattleSide::DEFENDER : BattleSide::ATTACKER));
		ON_CALL(info, unitOwner()).WillByDefault(Return(PlayerColor(spec.defenderSide ? 1 : 0)));
		ON_CALL(info, unitSlot()).WillByDefault(Return(SlotID(spec.slot)));
		// DamageCalculator asks the defender for its creature identity in three places
		// (:265, :292, :455) and dereferences unitType() to get it, so a null type
		// segfaults. We hand it a real roster entry — Archer, which carries no HATE,
		// KING or elemental special-casing — purely as an identity. Every statistic that
		// enters the formula still comes from the bonus list above, because
		// CUnitStateDetached::getAllBonuses forwards to our BonusBearerMock and never
		// consults the CCreature.
		ON_CALL(info, unitType()).WillByDefault(Return(CreatureID(CreatureID::ARCHER).toCreature()));

		ON_CALL(env, unitHasAmmoCart(_)).WillByDefault(Return(false));
		ON_CALL(env, unitEffectiveOwner(_)).WillByDefault(Return(PlayerColor(0)));

		// lib/bonuses/BonusCache.cpp:183-186 — attack and defence are PRIMARY_SKILL bonuses
		addBonus(BonusType::PRIMARY_SKILL, spec.attack, BonusSubtypeID(PrimarySkill::ATTACK));
		addBonus(BonusType::PRIMARY_SKILL, spec.defense, BonusSubtypeID(PrimarySkill::DEFENSE));
		// :180-181 — per-creature damage, min and max carried separately
		addBonus(BonusType::CREATURE_DAMAGE, spec.dmgMin, BonusCustomSubtype::creatureDamageMin);
		addBonus(BonusType::CREATURE_DAMAGE, spec.dmgMax, BonusCustomSubtype::creatureDamageMax);
		// :202 — hit points per creature
		addBonus(BonusType::STACK_HEALTH, spec.hp);
		addBonus(BonusType::STACKS_SPEED, spec.speed);

		if(spec.shooter)
		{
			addBonus(BonusType::SHOOTER, 1);
			// CUnitState::isShooter() is `shots.total() > 0` (CUnitState.cpp:735-738),
			// and CShots::total() returns 0 unless the unit also carries ammunition
			// (:CShots ctor, selector BonusType::SHOTS). The SHOOTER flag alone leaves
			// the unit a melee fighter as far as the damage formula is concerned, so a
			// shooter is only a shooter once it has shots.
			addBonus(BonusType::SHOTS, spec.shots);
		}
		if(spec.noMeleePenalty)
			addBonus(BonusType::NO_MELEE_PENALTY, 1);
		if(spec.noRetaliation)
			addBonus(BonusType::NO_RETALIATION, 1);
		if(spec.blocksRetaliation)
			addBonus(BonusType::BLOCKS_RETALIATION, 1);
		if(spec.additionalRetaliations)
			addBonus(BonusType::ADDITIONAL_RETALIATION, spec.additionalRetaliations);
		if(spec.unlimitedRetaliations)
			addBonus(BonusType::UNLIMITED_RETALIATIONS, 1);

		state = std::make_shared<CUnitStateDetached>(&info, &bonuses);
		state->localInit(&env);
		state->position = BattleHex(50);

		// Round-state flags AFTER localInit (which resets them). These are the
		// public CUnitState fields the server itself writes: doWaitAction sets
		// `waiting`, doDefendAction sets `defending`. The *consequences* — which
		// queue phase the unit lands in (CUnitState::battleQueuePhase), whether it
		// still moves this round (CUnitState::willMove) — stay engine code.
		state->waiting = spec.waiting;
		state->waitedThisTurn = spec.waiting;
		state->defending = spec.defending;
	}

	void addBonus(BonusType type, int val)
	{
		bonuses.addNewBonus(std::make_shared<Bonus>(
			BonusDuration::PERMANENT, type, BonusSource::CREATURE_ABILITY, val, BonusSourceID()));
	}

	void addBonus(BonusType type, int val, const BonusSubtypeID & subtype)
	{
		bonuses.addNewBonus(std::make_shared<Bonus>(
			BonusDuration::PERMANENT, type, BonusSource::CREATURE_ABILITY, val, BonusSourceID(), subtype));
	}

	CUnitStateDetached * unit() { return state.get(); }

	Spec spec;
	NiceMock<UnitInfoMock> info;
	NiceMock<UnitEnvironmentMock> env;
	BonusBearerMock bonuses;
	std::shared_ptr<CUnitStateDetached> state;

	static inline uint32_t nextId = 1;
};

Spec specFromJson(const JsonNode & n)
{
	Spec s;
	s.name = n["name"].isNull() ? "?" : n["name"].String();
	auto num = [&](const char * key, int fallback) {
		return n[key].isNull() ? fallback : static_cast<int>(n[key].Float());
	};
	auto flag = [&](const char * key) { return !n[key].isNull() && n[key].Bool(); };

	s.attack = num("attack", 10);
	s.defense = num("defense", 10);
	s.dmgMin = num("damage", 1);
	s.dmgMax = num("damage", 1);
	s.dmgMin = num("dmg_min", s.dmgMin);
	s.dmgMax = num("dmg_max", s.dmgMax);
	s.hp = num("hp", 10);
	s.speed = num("speed", 2);
	s.count = num("count", 1);
	s.shooter = flag("shooter");
	s.shots = num("shots", 32);
	s.noMeleePenalty = flag("no_melee_penalty");
	s.noRetaliation = flag("no_retaliation");
	s.blocksRetaliation = flag("blocks_retaliation");
	s.additionalRetaliations = num("additional_retaliation", 0);
	s.unlimitedRetaliations = flag("unlimited_retaliations");
	s.defenderSide = !n["side"].isNull() && n["side"].String() == "defender";
	s.slot = num("slot", 0);
	s.waiting = flag("waiting");
	s.defending = flag("defending");
	return s;
}

/// The battlefield callback DamageCalculator consults. For a melee attack between two
/// non-turret units on an empty field it is only asked for the defended town and the
/// obstacle list, both of which are empty here (see setupEmptyBattlefield).
class Field
{
public:
	Field()
	{
		battle.setupEmptyBattlefield();
		ON_CALL(battle, getStacksIf(_)).WillByDefault(Return(TStacks()));
		ON_CALL(battle, getTerrainType()).WillByDefault(Return(TerrainId(0)));
	}

	NiceMock<test::battle::BattleFake> battle;
};

/// Escape nothing fancy — all our strings are identifiers.
void emitDamageCase(std::ostream & out, const JsonNode & c)
{
	Spec as = specFromJson(c["attacker"]);
	Spec ds = specFromJson(c["defender"]);
	const bool shooting = !c["shooting"].isNull() && c["shooting"].Bool();

	Fake attacker(as);
	Fake defender(ds);
	Field field;

	// Optionally wound the attacker/defender first, so that the engine's own
	// count()/firstHPleft() feed the calculation (MODEL.md Definition 3.3).
	if(!c["attacker_predamage"].isNull())
	{
		int64_t amount = static_cast<int64_t>(c["attacker_predamage"].Float());
		attacker.unit()->damage(amount);
	}
	if(!c["defender_predamage"].isNull())
	{
		int64_t amount = static_cast<int64_t>(c["defender_predamage"].Float());
		defender.unit()->damage(amount);
	}

	BattleAttackInfo info(attacker.unit(), defender.unit(), 0, shooting);
	DamageEstimation est = DamageCalculator(field.battle, info).calculateDmgRange();

	out << "  {\n";
	out << "    \"id\": \"" << c["id"].String() << "\",\n";
	out << "    \"kind\": \"damage\",\n";
	out << "    \"attacker_count\": " << attacker.unit()->getCount() << ",\n";
	out << "    \"attacker_attack\": " << attacker.unit()->getAttack(shooting) << ",\n";
	out << "    \"defender_defense\": " << defender.unit()->getDefense(shooting) << ",\n";
	out << "    \"defender_count\": " << defender.unit()->getCount() << ",\n";
	out << "    \"defender_first_hp_left\": " << defender.unit()->getFirstHPleft() << ",\n";
	out << "    \"damage_min\": " << est.damage.min << ",\n";
	out << "    \"damage_max\": " << est.damage.max << ",\n";
	out << "    \"kills_min\": " << est.kills.min << ",\n";
	out << "    \"kills_max\": " << est.kills.max << "\n";
	out << "  }";
}

/// Applies a sequence of damage amounts to one stack and records the health pool after
/// each, exercising CHealth::damage / setFromTotal directly.
void emitHealthCase(std::ostream & out, const JsonNode & c)
{
	Fake stack(specFromJson(c["stack"]));

	out << "  {\n";
	out << "    \"id\": \"" << c["id"].String() << "\",\n";
	out << "    \"kind\": \"health\",\n";
	out << "    \"steps\": [\n";

	bool first = true;
	for(const auto & step : c["damage"].Vector())
	{
		int64_t amount = static_cast<int64_t>(step.Float());
		const int64_t requested = amount;
		stack.unit()->damage(amount); // amount is updated in place to what was absorbed
		if(!first)
			out << ",\n";
		first = false;
		out << "      {\"requested\": " << requested
		    << ", \"absorbed\": " << amount
		    << ", \"count\": " << stack.unit()->getCount()
		    << ", \"first_hp_left\": " << stack.unit()->getFirstHPleft()
		    << ", \"available\": " << stack.unit()->getAvailableHealth() << "}";
	}
	out << "\n    ]\n  }";
}

/// Exercises CRetaliations: how many retaliations a unit has, how they are consumed by
/// afterAttack(counter=true), and that afterNewRound restores them (MODEL.md sec. 6).
void emitRetaliationCase(std::ostream & out, const JsonNode & c)
{
	Fake stack(specFromJson(c["stack"]));

	out << "  {\n";
	out << "    \"id\": \"" << c["id"].String() << "\",\n";
	out << "    \"kind\": \"retaliation\",\n";
	out << "    \"able_initially\": " << (stack.unit()->ableToRetaliate() ? "true" : "false") << ",\n";
	out << "    \"events\": [\n";

	bool first = true;
	for(const auto & ev : c["events"].Vector())
	{
		const std::string what = ev.String();
		if(what == "retaliate")
			stack.unit()->afterAttack(false, true);
		else if(what == "attack")
			stack.unit()->afterAttack(false, false);
		else if(what == "new_round")
			stack.unit()->afterNewRound();
		else
			throw std::runtime_error("unknown retaliation event: " + what);

		if(!first)
			out << ",\n";
		first = false;
		out << "      {\"event\": \"" << what << "\", \"able\": "
		    << (stack.unit()->ableToRetaliate() ? "true" : "false") << "}";
	}
	out << "\n    ]\n  }";
}

/// Runs the engine's own turn-order machinery — CBattleInfoCallback::battleGetTurnOrder,
/// takeOneUnit, CMP_stack, CUnitState::battleQueuePhase/willMove/waited — over real
/// CUnitState units whose statistics and round-state flags come from the case. Nothing
/// about phase assignment or ordering is reimplemented; the harness only reads the queue.
void emitTurnOrderCase(std::ostream & out, const JsonNode & c)
{
	std::vector<std::unique_ptr<Fake>> fakes;
	for(const auto & u : c["units"].Vector())
		fakes.push_back(std::make_unique<Fake>(specFromJson(u)));

	// Give every unit its own hex; two units may never share one.
	for(size_t i = 0; i < fakes.size(); i++)
		fakes[i]->unit()->position = BattleHex(50 + static_cast<si16>(3 * i));

	Field field;
	// No unit is mid-activation: the queue is computed from a round boundary.
	ON_CALL(field.battle, getActiveStackID()).WillByDefault(Return(-1));
	ON_CALL(field.battle, getUnitsIf(_)).WillByDefault(Invoke(
		[&fakes](const ::battle::UnitFilter & predicate)
		{
			::battle::Units ret;
			for(const auto & f : fakes)
				if(predicate(f->state.get()))
					ret.push_back(f->state.get());
			return ret;
		}));

	std::vector<::battle::Units> turns;
	field.battle.battleGetTurnOrder(turns, 0, 1, 0, BattleSide::NONE);

	out << "  {\n";
	out << "    \"id\": \"" << c["id"].String() << "\",\n";
	out << "    \"kind\": \"turn_order\",\n";
	out << "    \"order\": [";
	bool first = true;
	if(!turns.empty())
	{
		for(const auto * u : turns.front())
		{
			for(const auto & f : fakes)
			{
				if(f->state.get() == u)
				{
					if(!first)
						out << ", ";
					first = false;
					out << "\"" << f->spec.name << "\"";
				}
			}
		}
	}
	out << "]\n  }";
}

} // namespace

int main(int argc, char ** argv)
{
	const std::string casesPath = argc > 1 ? argv[1] : "cases.json";

	// gmock prints "uninteresting call" notices to stdout, which would corrupt the
	// JSON document; the calls are expected (ON_CALL defaults are the wiring).
	::testing::FLAGS_gmock_verbose = "error";

	LIBRARY = new GameLibrary;
	LIBRARY->initializeFilesystem(false);
	LIBRARY->initializeLibrary();

	std::ifstream in(casesPath, std::ios::binary);
	if(!in)
	{
		std::cerr << "cannot open " << casesPath << "\n";
		return 2;
	}
	std::string text((std::istreambuf_iterator<char>(in)), std::istreambuf_iterator<char>());
	JsonNode root(reinterpret_cast<const std::byte *>(text.data()), text.size(), casesPath);

	std::ostream & out = std::cout;
	out << std::setprecision(17);
	out << "{\n";
	out << "  \"engine\": {\n";
	out << "    \"source\": \"/Users/ivanparfenchuk/Projects/AI/vcmi-upstream\",\n";
	out << "    \"attack_point_damage_factor\": "
	    << LIBRARY->engineSettings()->getDouble(EGameSettings::COMBAT_ATTACK_POINT_DAMAGE_FACTOR) << ",\n";
	out << "    \"attack_point_damage_factor_cap\": "
	    << LIBRARY->engineSettings()->getDouble(EGameSettings::COMBAT_ATTACK_POINT_DAMAGE_FACTOR_CAP) << ",\n";
	out << "    \"defense_point_damage_factor\": "
	    << LIBRARY->engineSettings()->getDouble(EGameSettings::COMBAT_DEFENSE_POINT_DAMAGE_FACTOR) << ",\n";
	out << "    \"defense_point_damage_factor_cap\": "
	    << LIBRARY->engineSettings()->getDouble(EGameSettings::COMBAT_DEFENSE_POINT_DAMAGE_FACTOR_CAP) << "\n";
	out << "  },\n";
	out << "  \"results\": [\n";

	bool first = true;
	for(const auto & c : root["cases"].Vector())
	{
		if(!first)
			out << ",\n";
		first = false;

		const std::string kind = c["kind"].String();
		if(kind == "damage")
			emitDamageCase(out, c);
		else if(kind == "health")
			emitHealthCase(out, c);
		else if(kind == "retaliation")
			emitRetaliationCase(out, c);
		else if(kind == "turn_order")
			emitTurnOrderCase(out, c);
		else
			throw std::runtime_error("unknown case kind: " + kind);
	}

	out << "\n  ]\n}\n";
	return 0;
}
