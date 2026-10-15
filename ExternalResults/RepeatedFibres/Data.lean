import ExternalResults.RepeatedFibres.CurveBound

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogExponent
open CurveValuationCenter CurveContactFamily PersistentWeightComparison
open scoped BigOperators

/-- Interpolation data independent of any Diophantine approximation family. -/
structure InterpolationData where
  m : ℕ
  K : ℕ
  κ : ℕ
  m_pos : 1 ≤ m
  curveDegreeWeights : Fin (m + 1) → ℚ
  curveJetWeights : Fin (m + 1) → ℚ
  curveDegreeWeights_pos : ∀ i, 0 < curveDegreeWeights i
  curveJetWeights_pos : ∀ i, 0 < curveJetWeights i
  sigma : ℚ
  sigma_pos : 0 < (sigma : ℝ)
  curveCenters : Fin K → Fin (m + 1) → ℂ
  curveCenters_zero_ne_zero : ∀ j, curveCenters j 0 ≠ 0
  fibre_card : ∀ a : ℂ,
    (Finset.univ.filter (fun j => curveCenters j 0 = a)).card ≤ κ
  fibre_separated : ∀ j k, j ≠ k → curveCenters j 0 = curveCenters k 0 →
    ∀ i : Fin m, curveCenters j i.succ ≠ curveCenters k i.succ
  curve_volume : (K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
    (∏ i, (curveDegreeWeights i : ℝ)) / (∏ i, (curveJetWeights i : ℝ)) < 1
  curve_fibre_volume : (κ : ℝ) * (1 + 3 * (sigma : ℝ)) ^ m *
    (∏ i : Fin m, (curveDegreeWeights i.succ : ℝ)) /
      (∏ i : Fin m, (curveJetWeights i.succ : ℝ)) < 1
  curve_separated_weight_products : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
    ∀ i, i ≠ 0 → i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (curveJetWeights j : ℝ)) <
        ∏ j ∈ A, (curveDegreeWeights j : ℝ)
  curve_coordinate_ratio : ∀ i : Fin m,
    (1 + (sigma : ℝ)) * (curveDegreeWeights i.succ : ℝ) < curveJetWeights i.succ

namespace InterpolationData

theorem curveCenters_injective (d : InterpolationData) : Function.Injective d.curveCenters := by
  intro j k h
  by_contra hne
  exact d.fibre_separated j k hne (congrFun h 0) ⟨0, d.m_pos⟩
    (congrFun h (Fin.succ ⟨0, d.m_pos⟩))

theorem exact_weighted_curve_inequality (d : InterpolationData)
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m + 1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m + 1) → E := Fin.cases y x
    let hz := LiuJiangZhang.RepeatedFibres.nonconstant_coordinates z hgen htrdeg
    (1 + (d.sigma : ℝ)) * ∑ p ∈ places hfinite z d.curveCenters hz,
      (contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  weighted_curve_inequality y x d.curveCenters d.curveCenters_zero_ne_zero
    d.fibre_card d.fibre_separated hgen htrdeg d.curveDegreeWeights d.curveJetWeights
    d.curveDegreeWeights_pos d.curveJetWeights_pos d.sigma
    (by exact_mod_cast d.sigma_pos) d.curve_volume d.curve_fibre_volume
    d.curve_separated_weight_products d.curve_coordinate_ratio

end InterpolationData
end LiuJiangZhang.RepeatedFibres
