import StatementDefinitions
import QuadraticFieldCriterion.QuadraticCriterionProof
import ExternalResults.LiuJiangZhangTheorem9
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Imaginary-quadratic exponential criterion

`ExponentialCriterion` is retained as an explicit hypothesis in the
specialization theorems. A general quadratic criterion specializes to it;
the norm-one condition is automatic for negative integers.
-/

namespace ImaginaryQuadratic

/-- Explicit coordinates for membership in `ℚ(i√d)` inside `ℂ`. -/
def HasRationalCoordinates (d : ℕ) (z : ℂ) : Prop :=
  ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * Complex.I * (Real.sqrt (d : ℝ) : ℂ)

/-- A nonzero real number whose exponential lies in `ℚ(i√d)` has
irrationality measure two. -/
def ExponentialCriterion : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (x : ℝ), x ≠ 0 →
    HasRationalCoordinates d
      (Complex.exp (2 * Complex.I * (Real.sqrt (d : ℝ) : ℂ) * (x : ℂ))) →
    irrationalityMeasure x = 2

theorem one_hasRationalCoordinates (d : ℕ) : HasRationalCoordinates d 1 := by
  exact ⟨1, 0, by simp⟩

/-- The imaginary-quadratic criterion follows from the general criterion.
Every negative integer is nonsquare, so no squarefreeness condition on `d` is needed. -/
theorem exponentialCriterion_of_quadraticFieldCriterion
    (criterion : ∀ (D : ℤ), ¬ IsSquare D → ∀ (x : ℝ), x ≠ 0 →
      QuadraticField.HasNormOneCoordinates D
        (Complex.exp (2 * QuadraticField.root D * (x : ℂ))) →
      Irrational x ∧ irrationalityMeasure x = 2 ∧ EventualStrictBound x) :
    ExponentialCriterion := by
  intro d hd x hx hcoordinates
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hnegative : -(d : ℤ) < 0 := by omega
  have hnonsquare : ¬ IsSquare (-(d : ℤ)) := by
    rintro ⟨a, ha⟩
    nlinarith [sq_nonneg a]
  have hroot : QuadraticField.root (-(d : ℤ)) =
      Complex.I * (Real.sqrt (d : ℝ) : ℂ) := by
    rw [QuadraticField.root, ite_eq_right (not_le.mpr hnegative)]
    simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
  have harg : 2 * QuadraticField.root (-(d : ℤ)) * (x : ℂ) =
      2 * Complex.I * (Real.sqrt (d : ℝ) : ℂ) * (x : ℂ) := by
    rw [hroot]
    ring
  obtain ⟨a, b, hab⟩ := hcoordinates
  let z : QuadraticField.Algebra (-(d : ℤ)) := ⟨a, b⟩
  have hz : QuadraticField.embedding (-(d : ℤ)) z =
      Complex.exp (2 * QuadraticField.root (-(d : ℤ)) * (x : ℂ)) := by
    rw [QuadraticField.embedding_apply, harg, hab, hroot]
    dsimp [z]
    ring
  have hnorm := QuadraticField.exponential_norm_one_of_negative hnegative x z hz
  exact (criterion (-(d : ℤ)) hnonsquare x hx
    ⟨z, hz, hnorm⟩).2.1

end ImaginaryQuadratic
