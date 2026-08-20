"""Executable reference implementation of the H3-det combat model.

This is a direct transcription of the rules formalised in ../MODEL.md, which in turn
cites the VCMI source tree (github.com/vcmi/vcmi; local checkout at $VCMI_CHECKOUT,
see ../README.md for the exact commits).

Scope: the deterministic fragment only (MODEL.md sec. 7). No spells, no morale, no luck,
no resurrection, no double-wide creatures, flat damage (dmg_min == dmg_max).

Key citations, repeated here so the code can be audited without the prose:

  damage formula          lib/battle/DamageCalculator.cpp:556-587
  attack/defence factors  lib/battle/DamageCalculator.cpp:210-224, 322-337
  factor constants        config/gameConfig.json:609-615
  base damage x count     lib/battle/DamageCalculator.cpp:123-131
  effective count         lib/battle/CUnitState.cpp:282-285
  health pool             lib/battle/CUnitState.cpp:183-186
  damage application      lib/battle/CUnitState.cpp:193-218, 262-273
  kill count              lib/battle/DamageCalculator.cpp:522-531
  retaliation             server/battles/BattleActionProcessor.cpp:298-334
  retaliation reset       lib/battle/CUnitState.cpp:920 via BattleInfo.cpp:663-670
  initiative order        lib/battle/BattleInfo.cpp:978-1006
  movement range == speed lib/battle/CUnitState.cpp:589-600
  walk-and-attack         server/battles/BattleActionProcessor.cpp:216-352
  DEFEND bonus            server/battles/BattleActionProcessor.cpp:168-196
  DEFEND bonus expiry     lib/battle/BattleInfo.cpp:686 (STACK_GETS_TURN)
  WAIT phase order        lib/battle/CBattleInfoCallback.cpp:495-519
"""

from __future__ import annotations

import math
from collections import deque
from dataclasses import dataclass, field, replace

# config/gameConfig.json:609-615
ATTACK_POINT_DAMAGE_FACTOR = 0.05
ATTACK_POINT_DAMAGE_FACTOR_CAP = 4.0
DEFENSE_POINT_DAMAGE_FACTOR = 0.025
DEFENSE_POINT_DAMAGE_FACTOR_CAP = 0.7


@dataclass(frozen=True)
class CreatureType:
    """MODEL.md Definition 3.1."""

    name: str
    attack: int
    defense: int
    dmg_min: int
    dmg_max: int
    hp: int
    speed: int
    value: int = 0
    shooter: bool = False
    no_melee_penalty: bool = False
    no_retaliation: bool = False
    blocks_retaliation: bool = False

    def __post_init__(self) -> None:
        if self.dmg_min != self.dmg_max:
            raise ValueError(
                f"{self.name}: H3-det requires flat damage (MODEL.md sec. 4); "
                f"got {self.dmg_min}-{self.dmg_max}"
            )
        for f in ("attack", "defense", "hp", "speed"):
            if getattr(self, f) < 0:
                raise ValueError(f"{self.name}: {f} must be non-negative")

    @property
    def damage(self) -> int:
        return self.dmg_min


class Stack:
    """MODEL.md Definition 3.2. Health is the (fullUnits, firstHPleft) pair."""

    __slots__ = ("ctype", "side", "slot", "hex", "full_units", "first_hp_left",
                 "retaliations_left", "acted", "defending", "waited")

    def __init__(self, ctype: CreatureType, count: int, side: int, slot: int, hex_: int):
        self.ctype = ctype
        self.side = side
        self.slot = slot
        self.hex = hex_
        # lib/battle/CUnitState.cpp init: a fresh stack is `count` full creatures
        self.full_units = count - 1 if count > 0 else 0
        self.first_hp_left = ctype.hp if count > 0 else 0
        self.retaliations_left = 0 if ctype.no_retaliation else 1
        self.acted = False
        # DEFEND bonus flag: set by the DEFEND action, cleared when the stack next
        # receives a turn (BonusDuration::STACK_GETS_TURN, BattleInfo.cpp:686).
        # Neither WAIT nor DEFEND touches retaliations_left.
        self.defending = False
        # WAIT flag: moves the stack's terminal action to the WAIT phase of the
        # current round (Unit.h:33-44); reset at the round boundary.
        self.waited = False

    def clone(self) -> "Stack":
        s = Stack.__new__(Stack)
        s.ctype = self.ctype
        s.side = self.side
        s.slot = self.slot
        s.hex = self.hex
        s.full_units = self.full_units
        s.first_hp_left = self.first_hp_left
        s.retaliations_left = self.retaliations_left
        s.acted = self.acted
        s.defending = self.defending
        s.waited = self.waited
        return s

    # --- health -----------------------------------------------------------

    def count(self) -> int:
        """lib/battle/CUnitState.cpp:282-285.

        The wounded top creature counts in full. This is the rule the whole
        candidate-A reduction rests on.
        """
        return self.full_units + (1 if self.first_hp_left > 0 else 0)

    def available(self) -> int:
        """lib/battle/CUnitState.cpp:183-186."""
        return self.first_hp_left + self.ctype.hp * self.full_units

    def alive(self) -> bool:
        return self.count() > 0

    def _set_from_total(self, total: int) -> None:
        """lib/battle/CUnitState.cpp:262-273."""
        hp = self.ctype.hp
        self.first_hp_left = total % hp
        self.full_units = total // hp
        if self.first_hp_left == 0 and self.full_units >= 1:
            self.first_hp_left = hp
            self.full_units -= 1

    def apply_damage(self, amount: int) -> int:
        """lib/battle/CUnitState.cpp:193-218.

        Returns the damage actually absorbed; the excess is discarded (overkill).
        """
        if amount < self.first_hp_left:
            self.first_hp_left -= amount
            return amount
        total = self.available()
        absorbed = min(amount, total)
        total -= absorbed
        if total <= 0:
            self.full_units = 0
            self.first_hp_left = 0
        else:
            self._set_from_total(total)
        return absorbed


def kills_for_damage(defender: Stack, damage: int) -> int:
    """lib/battle/DamageCalculator.cpp:522-531. Predicts kills without mutating."""
    if damage < defender.first_hp_left:
        return 0
    left = damage - defender.first_hp_left
    return min(1 + left // defender.ctype.hp, defender.count())


# --- damage ---------------------------------------------------------------


def attack_skill_factor(attack: int, defense: int) -> float:
    """lib/battle/DamageCalculator.cpp:210-224."""
    adv = attack - defense
    if adv > 0:
        return min(ATTACK_POINT_DAMAGE_FACTOR * adv, ATTACK_POINT_DAMAGE_FACTOR_CAP)
    return 0.0


def defense_skill_factor(attack: int, defense: int) -> float:
    """lib/battle/DamageCalculator.cpp:322-337."""
    adv = defense - attack
    if adv > 0:
        return min(DEFENSE_POINT_DAMAGE_FACTOR * adv, DEFENSE_POINT_DAMAGE_FACTOR_CAP)
    return 0.0


def defend_bonus(defense: int) -> int:
    """server/battles/BattleActionProcessor.cpp:168-196.

    The DEFEND action grants +20 % defence, computed as an integer bonus with a
    floor of +1, lasting until the stack next receives a turn
    (BonusDuration::STACK_GETS_TURN, removed at lib/battle/BattleInfo.cpp:686).
    """
    return max(1, defense * 20 // 100)


def compute_damage(attacker: Stack, defender: Stack, shooting: bool = False) -> int:
    """lib/battle/DamageCalculator.cpp:556-587, restricted to H3-det.

    attackFactorTotal is 1 + sum(attack factors); defenseFactorTotal is the product
    of (1 - factor); the result is floored and clamped below at 1. A defender whose
    `defending` flag is up carries the DEFEND bonus on its defence stat.
    """
    a, d = attacker.ctype, defender.ctype
    base = attacker.count() * a.damage  # :123-131

    def_eff = d.defense + (defend_bonus(d.defense) if defender.defending else 0)
    attack_total = 1.0 + attack_skill_factor(a.attack, def_eff)

    defense_factors = [defense_skill_factor(a.attack, def_eff)]
    # :385-390 melee penalty for shooters fighting in melee
    if not shooting and a.shooter and not a.no_melee_penalty:
        defense_factors.append(0.5)
    defense_total = 1.0
    for f in defense_factors:
        defense_total *= 1.0 - min(1.0, f)

    return max(1, math.floor(base * attack_total * defense_total))


# --- battlefield ----------------------------------------------------------


@dataclass
class Battlefield:
    """A hex grid in offset coordinates (MODEL.md sec. 2).

    Hex index h = x + y * width, matching lib/battle/BattleHex.h:125,133-141.
    Adjacency and distance are transcribed from BattleHex.h:147-178 and :193-207.

    height defaults to 1, in which case the grid degenerates to a single row and the
    distance formula reduces to |dx|.
    """

    width: int
    height: int = 1
    obstacles: frozenset = field(default_factory=frozenset)

    def index(self, x: int, y: int) -> int:
        if not (0 <= x < self.width and 0 <= y < self.height):
            raise ValueError(f"hex ({x},{y}) outside {self.width}x{self.height} field")
        return x + y * self.width

    def xy(self, h: int) -> tuple[int, int]:
        return h % self.width, h // self.width

    def distance(self, a: int, b: int) -> int:
        """BattleHex.h:193-207: axial x + y/2, then max or sum depending on signs."""
        x1, y1 = self.xy(a)
        x2, y2 = self.xy(b)
        ax1 = x1 + y1 // 2
        ax2 = x2 + y2 // 2
        dx = ax2 - ax1
        dy = y2 - y1
        if (dx >= 0 and dy >= 0) or (dx < 0 and dy < 0):
            return max(abs(dx), abs(dy))
        return abs(dx) + abs(dy)

    def neighbours(self, h: int):
        """BattleHex.h:147-178, the six directions in offset coordinates.

        On odd rows the diagonals shift left by one column relative to even rows.
        """
        x, y = self.xy(h)
        odd = y % 2
        for nx, ny in ((x - 1, y), (x + 1, y),
                       (x - odd, y - 1), (x + 1 - odd, y - 1),
                       (x - odd, y + 1), (x + 1 - odd, y + 1)):
            if 0 <= nx < self.width and 0 <= ny < self.height:
                yield nx + ny * self.width

    def adjacent(self, a: int, b: int) -> bool:
        return b in self.neighbours(a)


class Battle:
    """A deterministic H3-det battle. Side 0 is the player, side 1 the defence."""

    def __init__(self, field: Battlefield, stacks: list[Stack]):
        self.field = field
        self.stacks = stacks
        self.round = 0

    def clone(self) -> "Battle":
        b = Battle.__new__(Battle)
        b.field = self.field
        b.stacks = [s.clone() for s in self.stacks]
        b.round = self.round
        return b

    def living(self, side: int | None = None):
        return [s for s in self.stacks
                if s.alive() and (side is None or s.side == side)]

    # --- movement ---------------------------------------------------------

    def occupied(self, exclude: Stack | None = None) -> set[int]:
        return {s.hex for s in self.stacks if s.alive() and s is not exclude}

    def reachable(self, stack: Stack) -> set[int]:
        """BFS over free hexes, cost 1 per step, cut off at speed.

        lib/battle/CBattleInfoCallback.cpp:1411-1465 and :672-673.
        """
        blocked = self.occupied(exclude=stack) | set(self.field.obstacles)
        dist = {stack.hex: 0}
        q = deque([stack.hex])
        while q:
            cur = q.popleft()
            if dist[cur] >= stack.ctype.speed:
                continue
            for nxt in self.field.neighbours(cur):
                if nxt in blocked or nxt in dist:
                    continue
                dist[nxt] = dist[cur] + 1
                q.append(nxt)
        return set(dist)

    def attackable(self, stack: Stack) -> list[Stack]:
        """Enemies this stack can strike this turn via WALK_AND_ATTACK.

        server/battles/BattleActionProcessor.cpp:216-352: move to a hex adjacent to
        the target, then strike. So the reach is speed + 1 along free hexes.
        """
        reach = self.reachable(stack)
        out = []
        for enemy in self.living():
            if enemy.side == stack.side:
                continue
            if any(self.field.adjacent(h, enemy.hex) for h in reach):
                out.append(enemy)
        return out

    # --- combat -----------------------------------------------------------

    def attack_spots(self, attacker: Stack, defender: Stack) -> list[int]:
        """Legal approach hexes: reachable and adjacent to the defender.

        The choice of approach hex is part of the walk-and-attack action and
        changes future reachability for other stacks (a moved stack frees its
        old hex and occupies the new one), so an exact search must branch over
        it — collapsing it to one canonical hex understates achievable value.
        """
        reach = self.reachable(attacker)
        return sorted(h for h in reach if self.field.adjacent(h, defender.hex))

    def resolve_attack(self, attacker: Stack, defender: Stack,
                       dest: int | None = None) -> dict:
        """server/battles/BattleActionProcessor.cpp:298-334.

        The attacker strikes first; the defender retaliates only if it survived.
        `dest` selects the approach hex; None keeps the canonical
        closest-then-lowest choice (deterministic single-line play).
        """
        result = {"damage": 0, "kills": 0, "retaliation": 0, "retaliation_kills": 0}
        if not attacker.alive() or not defender.alive():
            return result

        # move into contact if needed
        spots = self.attack_spots(attacker, defender)
        if not spots:
            raise ValueError("resolve_attack called with an unreachable target")
        if dest is not None:
            if dest not in spots:
                raise ValueError("resolve_attack: dest is not a legal approach hex")
            attacker.hex = dest
        else:
            attacker.hex = min(spots, key=lambda h: (self.field.distance(h, attacker.hex), h))

        dmg = compute_damage(attacker, defender)
        before = defender.count()
        defender.apply_damage(dmg)
        result["damage"] = dmg
        result["kills"] = before - defender.count()

        # :326-333 retaliation, only if the defender is still alive
        if (defender.alive()
                and attacker.alive()
                and not attacker.ctype.blocks_retaliation
                and not defender.ctype.no_retaliation
                and defender.retaliations_left > 0):
            defender.retaliations_left -= 1
            rdmg = compute_damage(defender, attacker)
            rbefore = attacker.count()
            attacker.apply_damage(rdmg)
            result["retaliation"] = rdmg
            result["retaliation_kills"] = rbefore - attacker.count()
        return result

    # --- turn order -------------------------------------------------------

    def turn_order(self) -> list[Stack]:
        """lib/battle/BattleInfo.cpp:978-1006: initiative desc, then side, then slot.

        This is the NORMAL-phase order. The searchers over the attack-only
        fragment use it alone, because no searched player action is WAIT; the
        scripted policies that do wait are executed through `phased_schedule`.
        The side-then-slot tie rule is this model's simplification (MODEL.md §5
        note): the engine alternates sides on equal initiative.
        """
        return sorted(self.living(), key=lambda s: (-s.ctype.speed, s.side, s.slot))

    def wait_phase_order(self) -> list[Stack]:
        """lib/battle/CBattleInfoCallback.cpp:495-519: the WAIT phase runs in
        *increasing* speed order (same simplified tie rule as turn_order)."""
        return sorted([s for s in self.living() if s.waited],
                      key=lambda s: (s.ctype.speed, s.side, s.slot))

    def activate(self, stack: Stack) -> None:
        """The stack receives a turn: STACK_GETS_TURN bonuses expire
        (lib/battle/BattleInfo.cpp:686). Call at the start of every activation,
        including the NORMAL-phase activation at which the stack issues WAIT."""
        stack.defending = False

    def act_wait(self, stack: Stack) -> None:
        """WAIT: postpone the terminal action to the WAIT phase of this round.
        Consumes no retaliation charge and changes nothing else."""
        stack.waited = True

    def act_defend(self, stack: Stack) -> None:
        """DEFEND: end the turn in place with the +20 % (floor +1) defence bonus
        (server/battles/BattleActionProcessor.cpp:168-196, 693). Consumes no
        retaliation charge."""
        stack.defending = True

    def end_round(self) -> None:
        """lib/battle/BattleInfo.cpp:663-670 -> CUnitState.cpp:920.

        `defending` is deliberately NOT cleared here: the DEFEND bonus lasts
        until the stack's next activation (BattleInfo.cpp:686), which is in the
        next round; `activate` clears it there. `waited` is per-round phase
        membership and does reset."""
        for s in self.stacks:
            s.retaliations_left = 0 if s.ctype.no_retaliation else 1
            s.acted = False
            s.waited = False
        self.round += 1


def scripted_defence(battle: Battle, stack: Stack):
    """Policy pi from candidate-A sec. 2: strike an adjacent player stack, else pass."""
    targets = [e for e in battle.attackable(stack)
               if battle.field.adjacent(stack.hex, e.hex)]
    if not targets:
        return None
    return min(targets, key=lambda s: s.slot)


def destroyed_value(battle: Battle, initial_counts: dict[int, int]) -> int:
    """Total value of enemy creatures killed, relative to the starting counts."""
    total = 0
    for i, s in enumerate(battle.stacks):
        if s.side != 1:
            continue
        total += (initial_counts[i] - s.count()) * s.ctype.value
    return total
