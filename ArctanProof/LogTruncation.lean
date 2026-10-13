import ArctanProof.WeightedIndices
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

namespace ImaginaryQuadratic

/-- The finite Taylor polynomial `∑_{1≤k<T} (-1)^(k+1)t^k/k`, regarded as a
formal multivariable series. -/
noncomputable def truncatedLog (m T : ℕ) : MvPowerSeries (Fin (m + 1)) ℂ :=
  fun α => if α 0 < T then LiuJiangZhang.logOneAdd m α else 0

theorem logTail_coeff_eq_zero {m T : ℕ} (α : Fin (m + 1) →₀ ℕ) (hα : α 0 < T) :
    MvPowerSeries.coeff α (truncatedLog m T - LiuJiangZhang.logOneAdd m) = 0 := by
  rw [map_sub]
  change (if α 0 < T then LiuJiangZhang.logOneAdd m α else 0) -
    LiuJiangZhang.logOneAdd m α = 0
  simp [hα]

/-- Truncation preserves every coefficient below the truncation weight. -/
theorem logTail_coeff_eq_zero_of_weight {m T : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (hT : H ≤ v 0 * (T : ℚ)) (α : Fin (m + 1) →₀ ℕ)
    (hα : weightedDegree v α < H) :
    MvPowerSeries.coeff α (truncatedLog m T - LiuJiangZhang.logOneAdd m) = 0 := by
  apply logTail_coeff_eq_zero
  by_contra h
  have hnat : T ≤ α 0 := le_of_not_gt h
  have hrat : (T : ℚ) ≤ α 0 := by exact_mod_cast hnat
  have hterm := coordinate_le_weightedDegree v hv α 0
  have hmul := mul_le_mul_of_nonneg_left hrat (hv 0)
  linarith

/-- The ceiling choice for `T_i` supplies the required truncation weight. -/
theorem truncation_order_bound (F w v0 : ℚ) (hv0 : 0 < v0) :
    F * w ≤ v0 * (⌈F * w / v0⌉₊ : ℚ) := by
  have h := Nat.le_ceil (F * w / v0)
  have hmul := mul_le_mul_of_nonneg_left h hv0.le
  have hv0n : v0 ≠ 0 := hv0.ne'
  simpa [mul_div_cancel₀ _ hv0n, mul_comm, mul_left_comm] using hmul

end ImaginaryQuadratic
