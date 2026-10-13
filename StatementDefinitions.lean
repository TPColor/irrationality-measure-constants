import Mathlib.Basic.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped ENNReal

/-- The irrationality measure of `x` is the supremum of the real exponents `μ`
for which infinitely many reduced rational numbers `p/q` satisfy
`|x - p/q| < 1/q^μ`. Using `r.den` ensures the denominator is positive and the
fraction is reduced. The value lies in `ℝ≥0∞` to allow infinite measure. -/
noncomputable def irrationalityMeasure (x : ℝ) : ℝ≥0∞ :=
  ⨆ (μ : ℝ) (_ : Set.Infinite
    {r : ℚ | |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}), ENNReal.ofReal μ
