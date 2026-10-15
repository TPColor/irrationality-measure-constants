import ExternalResults.RepeatedFibres.AdmissibleCurveModelDegrees

/- Adapted from jdb19937/log-irrationality-measure, commit 09aeeb095cebdce6791e24eff7f16d227edcdcb6. The centres and weights are independent interpolation data. -/

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogIrrationalityMeasure.LogExponent

noncomputable section
namespace AdmissibleBlowupMargin
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LiuJiangZhang.RepeatedFibres.AdmissibleBlowupGeometry CurveNormalizationModel
variable (d : InterpolationData)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := AdmissibleCurveModel.existsModelData d C hn hm
  exact ⟨AdmissibleCurveModel.degreeData d C r⟩

end AdmissibleBlowupMargin

namespace AdmissibleBlowupGeometry
open AlgebraicGeometry
variable (d : InterpolationData)

theorem uniform_curve_margin :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (AdmissibleBlowupMargin.affineCurveDegreeData d)

end AdmissibleBlowupGeometry

end

end LiuJiangZhang.RepeatedFibres
