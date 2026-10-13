import StatementDefinitions
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

`ExponentialCriterion` is an explicit hypothesis of the specialization theorems.
Its derivation from `LiuJiangZhang.theorem9` is not yet implemented.
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

end ImaginaryQuadratic
