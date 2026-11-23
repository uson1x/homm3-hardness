"""Replay the two plans in paper/how-the-proof-works.md on the constructed hex board."""

from crosscheck_sol import restore, with_sol_stats
from embed_lemma import build_board_lemma
from verify_x3c import build_battle

TRIPLES = [(0, 1, 2), (3, 4, 5), (0, 1, 3)]
NAMES = ["North", "South", "Middle"]


def replay(instance, targets):
    battle, _ = build_battle(instance, {i: 1 for i in range(6)})
    enemies = [s for s in battle.stacks if s.side == 1]
    for stack in battle.turn_order():
        if not stack.alive():
            continue
        battle.activate(stack)
        if stack.side == 1:
            battle.act_wait(stack)
            continue
        target = enemies[targets[stack.slot]]
        result = battle.resolve_attack(stack, target)
        print(f"{chr(65 + stack.slot)} hits {NAMES[target.slot]} for {result['damage']}. "
              f"{target.available()} HP left.")
        if not target.alive():
            entrances = set(battle.field.neighbours(target.hex)) - battle.field.obstacles
            players = {s.hex for s in battle.living(side=0)}
            assert len(entrances) == 3 and entrances <= players
            assert target.hex not in battle.occupied()
            print("  The centre is free. All three entrances are occupied.")
    for stack in battle.wait_phase_order():
        if stack.alive():
            battle.activate(stack)
            battle.act_defend(stack)
    return sum(not enemy.alive() for enemy in enemies)


def main():
    saved = with_sol_stats()
    try:
        kind, instance = build_board_lemma(6, TRIPLES)
    finally:
        restore(saved)
    assert kind == "board", kind
    for name, orders, expected in [
        ("North and South", [0, 0, 0, 1, 1, 1], 2),
        ("Commit A, B and D to Middle", [2, 2, 0, 2, 1, 1], 1),
    ]:
        print(name)
        kills = replay(instance, orders)
        assert kills == expected
        print(f"Enemies killed: {kills}\n")


if __name__ == "__main__":
    main()
