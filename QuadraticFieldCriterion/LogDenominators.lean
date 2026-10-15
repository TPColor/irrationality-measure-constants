import QuadraticFieldCriterion.LogTruncation
import Mathlib.NumberTheory.Chebyshev

/-! # Denominators of truncated logarithms

The linear logarithmic bound below uses mathlib's elementary Chebyshev
estimate. Its larger constant is harmless in the dimension limit.
-/

namespace QuadraticField

theorem log_lcmUpto_le (n : ℕ) :
    Real.log (Nat.lcmUpto n : ℝ) ≤ (Real.log 4 + 4) * n := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

theorem exists_integer_scaled_truncatedLog_coefficient (m T : ℕ)
    (α : Fin (m + 1) →₀ ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto T : ℂ) *
      MvPowerSeries.coeff α (ImaginaryQuadratic.truncatedLog m T) = (z : ℂ) := by
  classical
  change ∃ z : ℤ, (Nat.lcmUpto T : ℂ) *
    (if α 0 < T then
      (if α = Finsupp.single 0 (α 0) then (-1 : ℂ) ^ (α 0 + 1) / (α 0 : ℂ) else 0)
      else 0) = (z : ℂ)
  by_cases hT : α 0 < T
  · rw [ite_eq_left hT]
    by_cases hα : α = Finsupp.single 0 (α 0)
    · rw [ite_eq_left hα]
      by_cases hk : α 0 = 0
      · exact ⟨0, by simp [hk]⟩
      have hd : α 0 ∣ Nat.lcmUpto T :=
        Finset.dvd_lcm (by simp [Finset.mem_Icc, Nat.one_le_iff_ne_zero, hk, hT.le])
      obtain ⟨a, ha⟩ := hd
      refine ⟨(-1 : ℤ) ^ (α 0 + 1) * (a : ℤ), ?_⟩
      rw [ha]
      push_cast
      have hk' : (α 0 : ℂ) ≠ 0 := by exact_mod_cast hk
      field_simp
    · exact ⟨0, by simp [hα]⟩
  · exact ⟨0, by simp [hT]⟩

theorem log_truncation_denominator_le {ι : Type*} [Fintype ι]
    (T d : ι → ℕ) :
    Real.log ((∏ i, (Nat.lcmUpto (T i)) ^ d i : ℕ) : ℝ) ≤
      (Real.log 4 + 4) * ∑ i, (d i : ℝ) * T i := by
  classical
  rw [Nat.cast_prod, Real.log_prod (fun i _ => by
    exact_mod_cast pow_ne_zero (d i) (Nat.lcmUpto_ne_zero (T i)))]
  simp only [Nat.cast_pow, Real.log_pow]
  calc
    _ ≤ ∑ i, (d i : ℝ) * ((Real.log 4 + 4) * T i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (log_lcmUpto_le (T i)) (Nat.cast_nonneg _))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring

/-- The ceiling truncation orders and floor degree bounds give a denominator
cost linear in the interpolation degree, uniformly over all columns. -/
theorem truncation_denominator_cost {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {H F v₀ : ℝ}
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hv₀ : 0 < v₀) :
    Real.log ((∏ i, (Nat.lcmUpto ⌈F * w i / v₀⌉₊) ^ ⌊H / w i⌋₊ : ℕ) : ℝ) ≤
      (Real.log 4 + 4) * H *
        (F * Fintype.card ι / v₀ + ∑ i, 1 / w i) := by
  have hΛ : 0 ≤ Real.log 4 + 4 := by positivity
  calc
    _ ≤ (Real.log 4 + 4) * ∑ i, (⌊H / w i⌋₊ : ℝ) * ⌈F * w i / v₀⌉₊ :=
      log_truncation_denominator_le _ _
    _ ≤ (Real.log 4 + 4) * ∑ i, H * (F / v₀ + 1 / w i) := by
      apply mul_le_mul_of_nonneg_left _ hΛ
      apply Finset.sum_le_sum
      intro i hi
      have hwi := hw i
      calc
        _ ≤ (H / w i) * (F * w i / v₀ + 1) := mul_le_mul
          (Nat.floor_le (div_nonneg hH (hw i).le))
          (Nat.ceil_lt_add_one (by positivity : 0 ≤ F * w i / v₀)).le
          (by positivity) (by positivity)
        _ = _ := by field_simp [hwi.ne']
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end QuadraticField
