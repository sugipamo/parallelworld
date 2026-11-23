import Mathlib

/-!
Γ for the self-check trial: the definitions that the claims about `pw/credal.py` are stated in.
What these definitions mean is settled by review of this file, not estimated.
-/

namespace Spec

/-- Every entry is a probability. -/
def Probs (p : List ℚ) : Prop := ∀ x ∈ p, 0 ≤ x ∧ x ≤ 1

/-- `f p = (w, π, m)`: for a non-empty list of probabilities, the lower Fréchet bound `w` is a
probability and is at most the product value `π`, which is at most the comonotone value `m`.
This is what makes the classes of copulas nest: independent and comonotone lie in `pqd`,
and `pqd` lies in `frechet`. -/
def NestedCopulaBounds (f : List ℚ → ℚ × ℚ × ℚ) : Prop :=
  ∀ p : List ℚ, p ≠ [] → Probs p →
    0 ≤ (f p).1 ∧ (f p).1 ≤ (f p).2.1 ∧ (f p).2.1 ≤ (f p).2.2 ∧ (f p).2.2 ≤ 1

/-- `f k t s = (lo, hi)`: bounds on the probability that `k` random checks all agree although the
hypothesis is false, when the agreement rate has mean `t` and concentration at least `s`.
1. `lo ≤ hi` and both are probabilities.
2. `hi` does not increase with the concentration, so the least concentration is the worst case.
3. With the uniform prior (`t = 1/2`, `s = 2`), `hi` is Laplace's `1 / (k + 1)`. -/
def AgreementBounds (f : ℕ → ℚ → ℚ → ℚ × ℚ) : Prop :=
  (∀ k t s, 0 ≤ t → t ≤ 1 → 0 < s →
      0 ≤ (f k t s).1 ∧ (f k t s).1 ≤ (f k t s).2 ∧ (f k t s).2 ≤ 1) ∧
  (∀ k t s s', 0 ≤ t → t ≤ 1 → 0 < s → s ≤ s' → (f k t s').2 ≤ (f k t s).2) ∧
  (∀ k : ℕ, (f k (1/2) 2).2 = 1 / ((k : ℚ) + 1))

end Spec
