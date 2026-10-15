import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Comparing determinant estimates

`D` is the normalized logarithm of the determinant, `b` is the average row
weight, and `δ` collects the finite-degree errors. A positive gap makes the
arithmetic lower bound incompatible with either analytic upper bound.
-/

namespace ImaginaryQuadratic

theorem determinant_estimates_incompatible
    {ν A η θ b c L Ear Etr Ehol δ D : ℝ}
    (hν : 1 ≤ ν) (hb0 : 0 ≤ b) (hbθ : b ≤ θ)
    (hgap : Ear + Etr + Ehol + δ < ν * (A * (1 - η) - θ) - (1 - θ))
    (hcollision : 1 + Ear + Etr + Ehol + δ < c * L)
    (hlower : -(1 - b) - Ear ≤ D)
    (hupper : D ≤ Etr + Ehol + δ +
      max (-c * L) (-ν * (A * (1 - η) - b))) : False := by
  have hweight : 0 ≤ (ν - 1) * (θ - b) :=
    mul_nonneg (sub_nonneg.mpr hν) (sub_nonneg.mpr hbθ)
  have hlow : Etr + Ehol + δ + (-c * L) < -(1 - b) - Ear := by
    nlinarith
  have hhigh : Etr + Ehol + δ + (-ν * (A * (1 - η) - b)) <
      -(1 - b) - Ear := by
    nlinarith
  rcases le_total (-c * L) (-ν * (A * (1 - η) - b)) with h | h
  · rw [max_eq_right h] at hupper
    linarith
  · rw [max_eq_left h] at hupper
    linarith

end ImaginaryQuadratic

namespace QuadraticField

/-- The finite-sum analytic estimate retains the common row-weight factor
in both alternatives. A larger collision margin absorbs that factor. -/
theorem determinant_estimates_incompatible_with_row_weight
    {ν A η θ b c L Ear Etr Ehol δ D : ℝ}
    (hν : 1 ≤ ν) (hb0 : 0 ≤ b) (hbθ : b ≤ θ)
    (hgap : Ear + Etr + Ehol + δ < ν * (A * (1 - η) - θ) - (1 - θ))
    (hcollision : 1 + Ear + Etr + Ehol + δ + ν * θ < c * L)
    (hlower : -(1 - b) - Ear ≤ D)
    (hupper : D ≤ Etr + Ehol + δ + ν * b +
      max (-c * L) (-ν * (A * (1 - η)))) : False := by
  have hweight : 0 ≤ (ν - 1) * (θ - b) :=
    mul_nonneg (sub_nonneg.mpr hν) (sub_nonneg.mpr hbθ)
  have hνb : ν * b ≤ ν * θ := mul_le_mul_of_nonneg_left hbθ (by linarith)
  have hlow : Etr + Ehol + δ + ν * b - c * L < -(1 - b) - Ear := by
    linarith
  have hhigh : Etr + Ehol + δ + ν * b - ν * (A * (1 - η)) < -(1 - b) - Ear := by
    nlinarith
  rcases le_total (-c * L) (-ν * (A * (1 - η))) with h | h
  · rw [max_eq_right h] at hupper
    linarith
  · rw [max_eq_left h] at hupper
    linarith

end QuadraticField
