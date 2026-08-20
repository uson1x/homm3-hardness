/*
 * stubs.cpp — link-time stand-ins for the two subsystems this harness never enters.
 *
 * The harness links VCMI's `vcmiMain` object files directly rather than the shipped
 * libvcmi.dylib (see CMakeLists.txt for why). One object in that set reaches outside the
 * library: AIFactory dispatches to the AI backends, which a library-only build does not
 * produce. No code path we exercise enters it — we only touch DamageCalculator,
 * CUnitState and CBattleInfoCallback — so we supply definitions that abort loudly
 * instead of pulling in the whole client.
 *
 * If either of these ever fires, the run is invalid and the report must say so.
 * (The Lua scripting module is *not* stubbed: GameLibrary::initializeLibrary constructs
 * it unconditionally, so the real vcmiLua objects are linked in.)
 */

#include "StdInc.h"

#include "../lib/callback/AIFactory.h"

#include <stdexcept>

VCMI_LIB_NAMESPACE_BEGIN

class CGlobalAI;
class CBattleGameInterface;

namespace AIFactory
{
std::shared_ptr<CGlobalAI> createAdventureAI(const std::string & name)
{
	throw std::logic_error("engine-check harness reached createAdventureAI(" + name + ")");
}

std::shared_ptr<CBattleGameInterface> createBattleAI(const std::string & name)
{
	throw std::logic_error("engine-check harness reached createBattleAI(" + name + ")");
}

bool isAvailableAdventureAI(const std::string &)
{
	return false;
}
}

VCMI_LIB_NAMESPACE_END
