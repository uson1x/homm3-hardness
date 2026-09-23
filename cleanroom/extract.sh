#!/bin/sh
# Клин-рум выписка формулировок из paper/main.md: только метки и тела до первой пустой строки / слова Proof.
cd /Users/ivanparfenchuk/Projects/frontier-lab/.claude/worktrees/burn-2026-09-02/homm3
M=paper/main.md
O=cleanroom/statements.md
{
echo "# Формулировки из homm3/paper/main.md (клин-рум выписка, без доказательств)"; echo
echo "## §1.2 Contributions (строки 97-126)"; echo; sed -n '97,126p' $M; echo
echo "## §2.3 The problem (строки 278-310, до строки *Proof.* леммы 2.1)"; echo; sed -n '278,310p' $M; echo
echo "## §2.4 The garrison policy (строки 319-372)"; echo; sed -n '319,372p' $M; echo
for L in 385 410 441 472 477 506 625 632 635; do
  echo "## Формулировка со строки $L"; echo
  awk -v s=$L 'NR>=s { if (NR>s && $0 ~ /^[[:space:]]*$/) exit; if ($0 ~ /Proof/) exit; print }' $M
  echo
done
} > $O
wc -l $O
grep -n 'Proof' $O
