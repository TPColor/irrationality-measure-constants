import ArctanProof.Basic
import SquareRootOfRationalsProof.Basic

/-- The irrationality measure of the arctangent of every positive rational is `2`. -/
theorem arctanOfRationals
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (r : ℚ) (hr : 0 < r) :
    irrationalityMeasure (Real.arctan (r : ℝ)) = 2 :=
  ArctanProof.arctanOfRationals_of_criterion criterion r hr

/-- The irrationality measure of `sqrt(r) * π` is `2` for every positive rational `r`. -/
theorem squareRootOfRationalsTimesPi
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (r : ℚ) (hr : 0 < r) :
    irrationalityMeasure (Real.sqrt (r : ℝ) * Real.pi) = 2 :=
  SquareRootOfRationalsProof.squareRootOfRationalsTimesPi criterion r hr
