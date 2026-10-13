import ArctanProof.Basic
import SquareRootOfRationalsProof.Basic

/-- The irrationality measure of every arctangent of a positive unit fraction is `2`. -/
theorem arctanOfUnitFractions
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (n : ℕ) (hn : 0 < n) :
    irrationalityMeasure (Real.arctan (1 / (n : ℝ))) = 2 :=
  ArctanProof.arctanOfUnitFractions criterion n hn

/-- The irrationality measure of `sqrt(r) * π` is `2` for every positive rational `r`. -/
theorem squareRootOfRationalsTimesPi
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (r : ℚ) (hr : 0 < r) :
    irrationalityMeasure (Real.sqrt (r : ℝ) * Real.pi) = 2 :=
  SquareRootOfRationalsProof.squareRootOfRationalsTimesPi criterion r hr
