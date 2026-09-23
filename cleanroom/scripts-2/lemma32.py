"""Lemma 3.2 брутфорс (deriver-2): для mu в наборе и всех мультимножеств c_i>=1 с суммой <= 12."""
from fractions import Fraction
import itertools
def D(mu, c): return max(1, (mu * c).numerator // (mu * c).denominator)
def parts(n, mx):
    if n == 0: yield (); return
    for f in range(min(n, mx), 0, -1):
        for rest in parts(n - f, f): yield (f,) + rest
bad = 0; checked = 0
for mu in [Fraction(3,10), Fraction(35,100), Fraction(1,2), Fraction(9,10), Fraction(99,100), Fraction(1,100)]:
    for total in range(1, 13):
        for p in parts(total, total):
            checked += 1
            dsum = sum(D(mu, c) for c in p)
            if dsum >= 3:
                if not (sum(p) >= 3): bad += 1
                if sum(p) == 3 and not (len(p) == 3 and all(c == 1 for c in p)): bad += 1
            if len(p) == 3 and all(c == 1 for c in p): assert dsum == 3 and sum(p) == 3
print("Lemma 3.2: проверено %d разбиений x 6 значений mu, нарушений %d" % (checked, bad))
