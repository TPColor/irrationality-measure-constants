import LogIrrationalityMeasure.Ampleness.ExceptionalCurveDegree
import ExternalResults.RepeatedFibres.AdmissibleBlowupGeometry
import ExternalResults.RepeatedFibres.BlowupCurveMargin

namespace LiuJiangZhang.RepeatedFibres
open LogIrrationalityMeasure LogIrrationalityMeasure.LogExponent
open AlgebraicGeometry CategoryTheory LogExponentSeshadri.Geometry
namespace ExceptionalCurveDegree
open LogIrrationalityMeasure.LogExponent.ExceptionalCurveDegree
noncomputable section

theorem admissible_degree_eq_neg_contactSum
    (d : InterpolationData)
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    letI := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg f hf
    ∀ (g : CurveNormalizationModel.parameterCurve f hf ⟶ AdmissibleBlowupGeometry.blowup d),
    CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g ≫
      AdmissibleBlowupGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        AdmissibleBlowupGeometry.affineChart d →
    ((eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        ((AdmissibleBlowupGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        (structureSheaf (CurveNormalizationModel.parameterCurve f hf)) : ℤ) : ℝ) =
      -((AdmissibleBlowupGeometry.scale d).radius : ℝ) *
        BlowupCurveMargin.contactSum d y x hgen htrdeg := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  intro g hgeneric
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := LiuJiangZhang.RepeatedFibres.nonconstant_coordinates z hgen htrdeg
  have h := compactIdeal_degree_eq_neg_contact_sum f hf d.curveCenters
    d.curveCenters_injective d.curveCenters_zero_ne_zero
    (AdmissibleBlowupGeometry.logCutoff d) (AdmissibleBlowupGeometry.scale d).jetPowers
    (AdmissibleBlowupGeometry.scale d).jetPowers_pos d.curveJetWeights d.curveJetWeights_pos
    (AdmissibleBlowupGeometry.scale d).radius (AdmissibleBlowupGeometry.scale d).jetPowers_eq
    (AdmissibleBlowupGeometry.logCutoff_strict d) (AdmissibleBlowupGeometry.affineChart d)
    (AdmissibleBlowupGeometry.compactificationStructureMap d)
    (AdmissibleBlowupGeometry.affineChart_over d)
    (AdmissibleBlowupGeometry.projection d) (AdmissibleBlowupGeometry.J d)
    (AdmissibleBlowupGeometry.exceptionalInclusion d)
    (AdmissibleBlowupGeometry.exceptional_presents d) g z hz hgeneric hres hfinite
  change _ = -((AdmissibleBlowupGeometry.scale d).radius : ℝ) *
    ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ)
  exact_mod_cast h


end
end ExceptionalCurveDegree
end LiuJiangZhang.RepeatedFibres
