import QuadraticFieldCriterion.FinalCriterion

namespace QuadraticField

/-- The quadratic field criterion, including the eventual strict bound for
unreduced rational approximations. -/
theorem criterion (D : ℤ) (hD : ¬ IsSquare D) (x : ℝ) (hx : x ≠ 0)
    (hα : HasNormOneCoordinates D (Complex.exp (2 * root D * (x : ℂ)))) :
    Irrational x ∧ irrationalityMeasure x = 2 ∧
      ImaginaryQuadratic.EventualStrictBound x := by
  have hb := approximationBound D hD x hx hα
  exact ⟨ImaginaryQuadratic.irrational_of_eventualStrictBound hb,
    ImaginaryQuadratic.irrationalityMeasure_eq_two_of_eventualStrictBound hb, hb⟩

end QuadraticField
