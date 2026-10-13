import ArctanProof.ImaginaryQuadratic

/-! # Arctangent specialization

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

/-- The arctangent of every positive rational has measure two under the
imaginary-quadratic exponential criterion. -/
theorem arctanOfRationals_of_criterion
    (criterion : ImaginaryQuadratic.ExponentialCriterion) (r : ℚ) (hr : 0 < r) :
    irrationalityMeasure (Real.arctan (r : ℝ)) = 2 := by
  have hx : 0 < Real.arctan (r : ℝ) :=
    Real.arctan_pos.mpr (by exact_mod_cast hr)
  apply criterion 1 (by decide) _ hx.ne'
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
