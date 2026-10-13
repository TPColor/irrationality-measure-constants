import ArctanProof.ImaginaryQuadratic

/-! # Positive rational square roots times π

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
