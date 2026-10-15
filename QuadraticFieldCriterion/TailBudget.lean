import QuadraticFieldCriterion.LogChangeOfVariables

/-! # Weight lost to nonzero logarithm-tail coefficients -/

namespace ImaginaryQuadratic

/-- A nonzero coefficient of the product of logarithm tails consumes at
least the sum of their truncation orders. This bounds the approximation
weight lost in the exact row translation. -/
theorem tail_coefficient_weight_budget {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (w : Fin m → ℚ) (T e : Fin m → ℕ) {F H : ℚ} {k s : ℕ}
    (hF : 0 < F) (hT : ∀ i, F * w i ≤ v 0 * (T i : ℚ))
    (hks : k ≤ s) (hjet : v 0 * (s : ℚ) < H)
    (hne : MvPowerSeries.coeff (Finsupp.single 0 k)
      (∏ i, (truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) ^ e i) ≠ 0) :
    (∑ i, (e i : ℚ) * w i) < H / F := by
  have htail : ∀ i, VanishesBelow v (v 0 * (T i : ℚ))
      (truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) := by
    intro i α hα
    exact logTail_coeff_eq_zero_of_weight v hv _ le_rfl α hα
  have hprod := VanishesBelow.prod hv Finset.univ
    (fun i => (e i : ℚ) * (v 0 * (T i : ℚ)))
    (fun i => (truncatedLog m (T i) - LiuJiangZhang.logOneAdd m) ^ e i)
    (fun i _ => (htail i).pow hv (e i))
  have hdegree : (∑ i, (e i : ℚ) * (v 0 * (T i : ℚ))) ≤ v 0 * (k : ℚ) := by
    apply le_of_not_gt
    intro h
    exact hne (hprod _ (by simpa only [weightedDegree_single] using h))
  apply (lt_div_iff₀ hF).mpr
  calc
    _ = ∑ i, (e i : ℚ) * (F * w i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, (e i : ℚ) * (v 0 * (T i : ℚ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hT i) (Nat.cast_nonneg _))
    _ ≤ v 0 * (k : ℚ) := hdegree
    _ ≤ v 0 * (s : ℚ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hks) (hv 0)
    _ < H := hjet

end ImaginaryQuadratic
