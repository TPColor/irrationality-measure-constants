import QuadraticFieldCriterion.AnalyticTests
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Bounds

/-! # Entire functions attached to interpolation columns -/

namespace QuadraticField

noncomputable def entireMonomial (C : ℂ) (h d : ℕ) (z : ℂ) : ℂ :=
  C * Complex.exp ((h : ℂ) * z) * z ^ d

theorem differentiable_entireMonomial (C : ℂ) (h d : ℕ) :
    Differentiable ℂ (entireMonomial C h d) := by
  exact (differentiable_const C |>.mul
    (Complex.differentiable_exp.comp (differentiable_const (h : ℂ) |>.mul
      differentiable_id))).mul (differentiable_id.pow d)

theorem norm_entireMonomial_le {C z : ℂ} {R : ℝ} (h d : ℕ)
    (_hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖entireMonomial C h d z‖ ≤ ‖C‖ * Real.exp ((h : ℝ) * R) * R ^ d := by
  simp only [entireMonomial, norm_mul, norm_pow]
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg C)
    calc
      ‖Complex.exp ((h : ℂ) * z)‖ ≤ Real.exp ‖(h : ℂ) * z‖ :=
        Complex.norm_exp_le_exp_norm _
      _ ≤ Real.exp ((h : ℝ) * R) := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg h)
  · exact pow_le_pow_left₀ (norm_nonneg z) hz d
  · positivity
  · positivity

theorem prod_choose_le_two_pow_sum {ι : Type*} [Fintype ι]
    (l a : ι → ℕ) : (∏ i, (l i).choose (a i)) ≤ 2 ^ (∑ i, l i) := by
  calc
    _ ≤ ∏ i, 2 ^ l i := Finset.prod_le_prod (fun i _ => Nat.choose_le_two_pow _ _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

noncomputable def columnFunction {ι : Type*} [Fintype ι]
    (h : ℕ) (l a : ι → ℕ) (z : ℂ) : ℂ :=
  if ∀ i, a i ≤ l i then
    entireMonomial ((∏ i, (l i).choose (a i) : ℕ) : ℂ) h (∑ i, (l i - a i)) z
  else 0

theorem differentiable_columnFunction {ι : Type*} [Fintype ι]
    (h : ℕ) (l a : ι → ℕ) : Differentiable ℂ (columnFunction h l a) := by
  classical
  unfold columnFunction
  split
  · exact differentiable_entireMonomial _ _ _
  · exact differentiable_const _

theorem norm_columnFunction_le {ι : Type*} [Fintype ι]
    (h : ℕ) (l a : ι → ℕ) {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h l a z‖ ≤ (2 * R) ^ (∑ i, l i) * Real.exp ((h : ℝ) * R) := by
  classical
  unfold columnFunction
  split
  · have hC : ‖((∏ i, (l i).choose (a i) : ℕ) : ℂ)‖ ≤
        (2 : ℝ) ^ (∑ i, l i) := by
      rw [Complex.norm_natCast]
      exact_mod_cast prod_choose_le_two_pow_sum l a
    have hd : (∑ i, (l i - a i)) ≤ ∑ i, l i :=
      Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)
    calc
      _ ≤ ‖((∏ i, (l i).choose (a i) : ℕ) : ℂ)‖ *
          Real.exp ((h : ℝ) * R) * R ^ (∑ i, (l i - a i)) :=
        norm_entireMonomial_le h _ (by linarith) hz
      _ ≤ (2 : ℝ) ^ (∑ i, l i) * Real.exp ((h : ℝ) * R) * R ^ (∑ i, l i) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
        · exact pow_le_pow_right₀ hR hd
        · positivity
        · positivity
      _ = _ := by rw [mul_pow]; ring
  · simp only [norm_zero]
    positivity

/-- Uniform growth on the large disk, expressed in the weighted degree budget. -/
theorem norm_columnFunction_le_exp {ι : Type*} [Fintype ι]
    (h : ℕ) (l a : ι → ℕ) {R H w₀ wstar : ℝ}
    (hR : 1 ≤ R) (_hw₀ : 0 < w₀) (_hwstar : 0 < wstar)
    (hh : (h : ℝ) ≤ H / w₀) (hl : (∑ i, l i : ℕ) ≤ H / wstar)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h l a z‖ ≤ Real.exp (H * (R / w₀ + Real.log (2 * R) / wstar)) := by
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  calc
    _ ≤ (2 * R) ^ (∑ i, l i) * Real.exp ((h : ℝ) * R) :=
      norm_columnFunction_le h l a hR hz
    _ = Real.exp ((∑ i, l i : ℕ) * Real.log (2 * R) + (h : ℝ) * R) := by
      rw [Real.exp_add, Real.exp_nat_mul (Real.log (2 * R)) (∑ i, l i),
        Real.exp_log (by linarith : 0 < 2 * R)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_right hh (by linarith : 0 ≤ R)
      have h₂ := mul_le_mul_of_nonneg_right hl hlog
      calc
        _ ≤ (H / wstar) * Real.log (2 * R) + (H / w₀) * R := add_le_add h₂ h₁
        _ = _ := by ring

end QuadraticField
