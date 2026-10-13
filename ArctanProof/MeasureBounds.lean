import StatementDefinitions
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.NormNum

open scoped ENNReal

namespace ImaginaryQuadratic

/-- Dirichlet's approximation theorem gives measure at least two for
irrational real numbers. -/
theorem two_le_irrationalityMeasure {x : ℝ} (hx : Irrational x) :
    2 ≤ irrationalityMeasure x := by
  have hinfinite : Set.Infinite
      {r : ℚ | |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ (2 : ℝ)} := by
    simpa only [Real.rpow_two] using
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have h : ENNReal.ofReal (2 : ℝ) ≤ irrationalityMeasure x :=
    le_iSup_of_le (2 : ℝ) (le_iSup_of_le hinfinite le_rfl)
  simpa using h

/-- Finite exceptional sets for every exponent above two give measure at most two. -/
theorem irrationalityMeasure_le_two_of_finite {x : ℝ}
    (hfinite : ∀ μ : ℝ, 2 < μ → Set.Finite
      {r : ℚ | |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}) :
    irrationalityMeasure x ≤ 2 := by
  apply iSup_le
  intro μ
  apply iSup_le
  intro hinfinite
  have hμ : μ ≤ 2 := by
    by_contra h
    exact hinfinite (hfinite μ (lt_of_not_ge h))
  exact (ENNReal.ofReal_le_ofReal hμ).trans (by norm_num)

theorem irrationalityMeasure_eq_two_of_finite {x : ℝ} (hx : Irrational x)
    (hfinite : ∀ μ : ℝ, 2 < μ → Set.Finite
      {r : ℚ | |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}) :
    irrationalityMeasure x = 2 :=
  le_antisymm (irrationalityMeasure_le_two_of_finite hfinite)
    (two_le_irrationalityMeasure hx)

end ImaginaryQuadratic
