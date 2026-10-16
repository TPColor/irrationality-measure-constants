import QuadraticFieldCriterion.ApproximationConclusion
import QuadraticFieldCriterion.ApproximationSelection
import QuadraticFieldCriterion.ArithmeticEstimate
import QuadraticFieldCriterion.AnalyticDeterminant
import QuadraticFieldCriterion.CollisionAlternatives
import QuadraticFieldCriterion.CriterionCentres
import QuadraticFieldCriterion.DeterminantComparison
import QuadraticFieldCriterion.DegreeErrors
import QuadraticFieldCriterion.FullAnalyticEstimate
import QuadraticFieldCriterion.EstimateNormalization
import QuadraticFieldCriterion.FinalCriterion
import QuadraticFieldCriterion.DimensionLimits
import QuadraticFieldCriterion.ImaginaryQuadratic
import QuadraticFieldCriterion.InterpolationMinor
import QuadraticFieldCriterion.InterpolationEntry
import QuadraticFieldCriterion.InterpolationBudgets
import QuadraticFieldCriterion.RowTranslation
import QuadraticFieldCriterion.RowChoiceBounds
import QuadraticFieldCriterion.LogChangeOfVariables
import QuadraticFieldCriterion.LogDenominators
import QuadraticFieldCriterion.LogTruncation
import QuadraticFieldCriterion.MeasureBounds
import QuadraticFieldCriterion.NonzeroMinor
import QuadraticFieldCriterion.Parameters
import QuadraticFieldCriterion.QuadraticArithmetic
import QuadraticFieldCriterion.QuadraticCriterionProof
import QuadraticFieldCriterion.QuadraticCriterionStatement
import QuadraticFieldCriterion.QuadraticOrder
import QuadraticFieldCriterion.TruncatedInterpolation
import QuadraticFieldCriterion.TailBudget
import QuadraticFieldCriterion.SimplexCounts
import QuadraticFieldCriterion.WeightedIndices
import QuadraticFieldCriterion.WeightedPackets

/-! # Irrationality measure results for specific constant families

## Arctangent specialization

The irrationality-measure results assume `ExponentialCriterion`.
-/

namespace ArctanProof

/-- The exponential double-angle identity, with no restriction on real `t`. -/
theorem exp_two_I_arctan (t : ℝ) :
    Complex.exp (2 * Complex.I * (Real.arctan t : ℂ)) =
      (1 + (t : ℂ) * Complex.I) / (1 - (t : ℂ) * Complex.I) := by
  have hplus : 1 + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hminus : 1 - (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [Complex.ofReal_arctan, Complex.arctan]
  have hcancel : (2 : ℂ) * Complex.I * (-Complex.I / 2) = 1 := by
    field_simp
    linear_combination -Complex.I_sq
  rw [← mul_assoc, hcancel, one_mul, Complex.exp_log (div_ne_zero hplus hminus)]

/-- Rational coordinates in `ℚ(i)` for the exponential of twice an arctangent. -/
theorem exp_arctan_rational_coordinates (n : ℕ) (hn : 0 < n) :
    ImaginaryQuadratic.HasRationalCoordinates 1
      (Complex.exp (2 * Complex.I * (Real.sqrt (1 : ℝ) : ℂ) *
        (Real.arctan (1 / (n : ℝ)) : ℂ))) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hden : (n : ℂ) ^ 2 + 1 ≠ 0 := by
    have h : (0 : ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
    exact_mod_cast h.ne'
  refine ⟨((n : ℚ) ^ 2 - 1) / ((n : ℚ) ^ 2 + 1),
    (2 * (n : ℚ)) / ((n : ℚ) ^ 2 + 1), ?_⟩
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one]
  rw [exp_two_I_arctan]
  push_cast
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one]
  have hm : (n : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
  field_simp [hnC, hden, hm]
  apply Complex.ext <;> simp [pow_two] <;> ring

/-- Rational coordinates for the exponential of twice the arctangent of a rational. -/
theorem exp_arctan_rat_coordinates (r : ℚ) :
    ImaginaryQuadratic.HasRationalCoordinates 1
      (Complex.exp (2 * Complex.I * (Real.sqrt (1 : ℝ) : ℂ) *
        (Real.arctan (r : ℝ) : ℂ))) := by
  have hden : (1 : ℂ) + (r : ℂ) ^ 2 ≠ 0 := by
    have h : (0 : ℝ) < 1 + (r : ℝ) ^ 2 := by positivity
    exact_mod_cast h.ne'
  refine ⟨(1 - r ^ 2) / (1 + r ^ 2), 2 * r / (1 + r ^ 2), ?_⟩
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one]
  rw [exp_two_I_arctan]
  push_cast
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one]
  have hm : (1 : ℂ) - (r : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.re h
    simp at hi
  field_simp [hden, hm]
  apply Complex.ext <;> simp [pow_two] <;> ring

/-- The arctangent of every nonzero rational has measure two under the
imaginary-quadratic exponential criterion. -/
theorem arctanOfRationals_of_criterion
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (r : ℚ) (hr : r ≠ 0) :
    irrationalityMeasure (Real.arctan (r : ℝ)) = 2 := by
  have hx : Real.arctan (r : ℝ) ≠ 0 := by
    simpa only [ne_eq, Real.arctan_eq_zero_iff, Rat.cast_eq_zero] using hr
  apply criterion 1 (by decide) _ hx
  simpa only [Nat.cast_one] using exp_arctan_rat_coordinates r

/-- Positive unit fractions are a special case of the exponential criterion. -/
theorem arctanOfUnitFractions_of_criterion
    (criterion : ImaginaryQuadratic.ExponentialCriterion)
    (n : ℕ) (hn : 0 < n) :
    irrationalityMeasure (Real.arctan (1 / (n : ℝ))) = 2 := by
  have hx : 0 < Real.arctan (1 / (n : ℝ)) :=
    Real.arctan_pos.mpr (by positivity)
  apply criterion 1 (by decide) _ hx.ne'
  simpa only [Nat.cast_one] using exp_arctan_rational_coordinates n hn

theorem arctanOfUnitFractions
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (n : ℕ) (hn : 0 < n) :
    irrationalityMeasure (Real.arctan (1 / (n : ℝ))) = 2 :=
  arctanOfUnitFractions_of_criterion criterion n hn

end ArctanProof

/-! ## Positive rational square roots times π

The specialization uses `d = a*b` and `exp (2πia) = 1`, including nonsquarefree
`a*b`.
-/

namespace SquareRootOfRationalsProof

/-- The real square-root cancellation underlying the exponential identity. -/
theorem sqrt_mul_sqrt_div (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt ((a * b : ℕ) : ℝ) * Real.sqrt ((a : ℝ) / (b : ℝ)) = a := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [← Real.sqrt_mul (by positivity)]
  push_cast
  rw [show (a : ℝ) * b * (a / b) = a ^ 2 by field_simp]
  exact Real.sqrt_sq (by positivity)

/-- All the multiplicative interpolation centres equal one in this family. -/
theorem exp_sqrt_fraction_pi (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Complex.exp (2 * Complex.I * (Real.sqrt ((a * b : ℕ) : ℝ) : ℂ) *
      (Real.sqrt ((a : ℝ) / (b : ℝ)) * Real.pi : ℝ)) = 1 := by
  have hmul := congrArg Complex.ofReal (sqrt_mul_sqrt_div a b ha hb)
  push_cast at hmul ⊢
  have harg :
      2 * Complex.I * (Real.sqrt ((a : ℝ) * (b : ℝ)) : ℂ) *
        ((Real.sqrt ((a : ℝ) / (b : ℝ)) : ℂ) * (Real.pi : ℂ)) =
      (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    calc
      _ = 2 * Complex.I *
          ((Real.sqrt ((a : ℝ) * (b : ℝ)) : ℂ) *
            (Real.sqrt ((a : ℝ) / (b : ℝ)) : ℂ)) * (Real.pi : ℂ) := by ring
      _ = _ := by rw [hmul]; ring
  rw [harg]
  exact Complex.exp_nat_mul_two_pi_mul_I a

theorem squareRootOfFractionTimesPi_of_criterion
    (criterion : ImaginaryQuadratic.ExponentialCriterion)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    irrationalityMeasure (Real.sqrt ((a : ℝ) / (b : ℝ)) * Real.pi) = 2 := by
  apply criterion (a * b) (Nat.mul_pos ha hb)
  · exact (mul_pos (Real.sqrt_pos.mpr (by positivity)) Real.pi_pos).ne'
  · rw [exp_sqrt_fraction_pi a b ha hb]
    exact ImaginaryQuadratic.one_hasRationalCoordinates _

/-- The arbitrary positive rational formulation, using its positive reduced
numerator and denominator to choose the integer `d`. -/
theorem squareRootOfRationalsTimesPi_of_criterion
    (criterion : ImaginaryQuadratic.ExponentialCriterion)
    (r : ℚ) (hr : 0 < r) :
    irrationalityMeasure (Real.sqrt (r : ℝ) * Real.pi) = 2 := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hnumNat : 0 < r.num.natAbs := Int.natAbs_pos.mpr hnum.ne'
  have hcast : (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    simp [abs_of_pos hnum]
  rw [hcast]
  exact squareRootOfFractionTimesPi_of_criterion criterion _ _ hnumNat r.pos

theorem squareRootOfRationalsTimesPi
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (r : ℚ) (hr : 0 < r) :
    irrationalityMeasure (Real.sqrt (r : ℝ) * Real.pi) = 2 :=
  squareRootOfRationalsTimesPi_of_criterion criterion r hr

end SquareRootOfRationalsProof

/-- The irrationality measure of the arctangent of every nonzero rational is `2`. -/
theorem arctanOfRationals
    (r : ℚ) (hr : r ≠ 0) :
    irrationalityMeasure (Real.arctan (r : ℝ)) = 2 :=
  ArctanProof.arctanOfRationals_of_criterion
    (ImaginaryQuadratic.exponentialCriterion_of_quadraticFieldCriterion QuadraticField.criterion) r hr

/-- The irrationality measure of `sqrt(r) * π` is `2` for every positive rational `r`. -/
theorem squareRootOfRationalsTimesPi
    (r : ℚ) (hr : 0 < r) :
    irrationalityMeasure (Real.sqrt (r : ℝ) * Real.pi) = 2 :=
  SquareRootOfRationalsProof.squareRootOfRationalsTimesPi_of_criterion
    (ImaginaryQuadratic.exponentialCriterion_of_quadraticFieldCriterion QuadraticField.criterion) r hr
