import LogIrrationalityMeasure.Geometry.CurveInequality
import LogIrrationalityMeasure.Geometry.CurvePrimeHeight
import LogIrrationalityMeasure.Geometry.PlaceLocalRing

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogExponent
open LogExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily
open PersistentWeightComparison
open Filter Topology
open scoped BigOperators

noncomputable section

theorem nonconstant_coordinates {E : Type*} [Field E] [Algebra ℂ E]
    {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ i, Transcendental ℂ (z i) := by
  let : Algebra.Transcendental ℂ E := trdeg_ne_zero_iff.mp
    (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

/-- Only the centres in the current fibre need ordinary auxiliary jets. -/
theorem eventually_exists_fibre_auxiliary {m K κ : ℕ}
    (c : Fin K → Fin (m + 1) → ℂ) (a : ℂ)
    (hcard : (Finset.univ.filter (fun j => c j 0 = a)).card ≤ κ)
    (w v : Fin m → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (σ : ℚ) (hσ : 0 < σ)
    (hvol : (κ : ℝ) * (1 + 3 * (σ : ℝ)) ^ m *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1) :
    ∀ᶠ N : ℕ in atTop, ∃ F : MvPolynomial (Fin m) ℂ, F ≠ 0 ∧
      WeightedSliceDegree.SupportBound (fun i => (w i : ℝ)) N F ∧
      ∀ j, c j 0 = a → OrdinaryAuxiliaryJet.formalJet (fun i => c j i.succ) F ∈
        JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1 + 3 * σ) * N) := by
  classical
  let S := Finset.univ.filter (fun j => c j 0 = a)
  let e : Fin S.card ↪o Fin K := S.orderEmbOfFin rfl
  have hvolS : (S.card : ℝ) * (1 + 3 * (σ : ℝ)) ^ m *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1 := by
    apply lt_of_le_of_lt ?_ hvol
    have hc : (S.card : ℝ) ≤ κ := by exact_mod_cast hcard
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity))
        (Finset.prod_nonneg (fun i _ => by exact_mod_cast (hw i).le)))
      (Finset.prod_nonneg (fun i _ => by exact_mod_cast (hv i).le))
  filter_upwards [OrdinaryAuxiliaryJet.eventually_exists_auxiliaryPolynomial_nat
    w v hw hv S.card (a := 1 + 3 * σ) (by positivity) (by push_cast; exact hvolS)
    (fun j i => c (e j) i.succ)] with N hN
  obtain ⟨F, hF0, hF, hjet⟩ := hN
  refine ⟨F, hF0, hF, ?_⟩
  intro j hj
  have hjS : j ∈ S := by simp [S, hj]
  obtain ⟨k, hk⟩ : ∃ k : Fin S.card, e k = j := by
    have hjrange : j ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [S.range_orderEmbOfFin rfl]
      exact hjS
    exact hjrange
  simpa only [hk] using hjet k

/-- Ordinary derivatives vanish on a curve in one fibre whenever its contact
exceeds its weighted degree. No hypothesis is imposed on jets in other fibres. -/
theorem fibre_words_vanish
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (ha : a ≠ 0) (x : Fin m → E)
    (c : Fin K → Fin (m + 1) → ℂ)
    (hc0 : ∀ j, c j 0 ≠ 0)
    (hz : ∃ i, Transcendental ℂ ((fibre a x) i))
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (σ : ℚ) (hσ : 0 < σ) (N : ℕ) (hN : 0 < N)
    (F : MvPolynomial (Fin m) ℂ)
    (hF : WeightedSliceDegree.SupportBound (fun i => (w i.succ : ℝ)) N F)
    (hjet : ∀ j, c j 0 = a → OrdinaryAuxiliaryJet.formalJet (fun i => c j i.succ) F ∈
      JetGeometry.rationalWeightedIdeal (fun i => v i.succ)
        (fun i => (hv i.succ).le) ((1 + 3 * σ) * N))
    (hexcess : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1 + (σ : ℝ)) * ∑ p ∈ places hfinite (fibre a x) c hz,
        (contact hres hfinite (fibre a x) c hz v p : ℝ)) :
    ∀ word : List (Fin m), DerivativeIdeals.wordCost (fun i => (v i.succ : ℝ)) word ≤
      (σ : ℝ) * N → MvPolynomial.aeval x (OrdinaryDerivatives.word m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcost : (word.map (fun i => v i.succ)).sum ≤ σ * N := by
    change (word.map (fun i => (v i.succ : ℝ))).sum ≤ (σ : ℝ) * N at hword
    rw [← CurveDerivativeVanishing.cast_word_cost (fun i => v i.succ) word] at hword
    exact_mod_cast hword
  have hdegree := OrdinaryDerivatives.supportBound_word
    (fun i => (w i.succ : ℝ)) (N : ℝ) F hF
    (fun i => by exact_mod_cast (hw i.succ).le) word
  have hsum : 0 ≤ ∑ p ∈ places hfinite (fibre a x) c hz,
      (contact hres hfinite (fibre a x) c hz v p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    exact_mod_cast contact_nonneg hres hfinite (fibre a x) c hc0 hz v hv p
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite x
    (fun i => w i.succ) (fun i => hw i.succ)
    (N : ℝ) ((1 + 2 * (σ : ℝ)) * N) hNR.le
    (OrdinaryDerivatives.word m word F) hdegree
    (places hfinite (fibre a x) c hz)
    (fun p => (contact hres hfinite (fibre a x) c hz v p : ℝ))
  · intro hne p hp
    let := hres p
    have hret : (1 + 2 * σ) * (N : ℚ) ≤
        (1 + 3 * σ) * N - (word.map (fun i => v i.succ)).sum := by nlinarith
    have heq := contact_fibre hres hfinite a ha x c hz v p hp
    have hlocal := PlaceCenteredBranch.ordinaryWord_field_order_lower p x _
      (fun i => centered hfinite (fibre a x) c hz p hp i.succ)
      (PlaceCenteredBranch.fibre_nonconstant x _
        (by rw [center_zero_eq hfinite a x c hz p hp]; exact nonconstant _ _ hz))
      (fun i => v i.succ) (fun i => hv i.succ) ((1 + 3 * σ) * N) F
      (hjet _ (center_zero_eq hfinite a x c hz p hp)) word hne
    rw [← heq] at hlocal
    have hcontact : 0 ≤ contact hres hfinite (fibre a x) c hz v p :=
      contact_nonneg hres hfinite (fibre a x) c hc0 hz v hv p
    have hq := (mul_le_mul_of_nonneg_left hret hcontact).trans hlocal
    have hr : (contact hres hfinite (fibre a x) c hz v p : ℝ) *
        ((1 + 2 * (σ : ℝ)) * N) ≤
        (WeightedPolynomialPole.coordinateOrder p.valuation
          (MvPolynomial.aeval x (OrdinaryDerivatives.word m word F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
          N * ((1 + (σ : ℝ)) * ∑ p ∈ places hfinite (fibre a x) c hz,
            (contact hres hfinite (fibre a x) c hz v p : ℝ)) :=
        mul_lt_mul_of_pos_left hexcess hNR
      _ = (1 + (σ : ℝ)) * (N * ∑ p ∈ places hfinite (fibre a x) c hz,
          (contact hres hfinite (fibre a x) c hz v p : ℝ)) := by ring
      _ ≤ (1 + 2 * (σ : ℝ)) * (N * ∑ p ∈ places hfinite (fibre a x) c hz,
          (contact hres hfinite (fibre a x) c hz v p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by linarith : 1 + σ ≤ 1 + 2 * σ))
          (mul_nonneg hNR.le hsum)
      _ = _ := by ring

/-- The fibre step of the curve inequality, allowing several coordinatewise
distinct centres in each exponential fibre. The volume cost is the fibre size. -/
theorem no_fibre_excess
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E] {m K κ : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (ha : a ≠ 0) (x : Fin m → E)
    (c : Fin K → Fin (m + 1) → ℂ) (hc0 : ∀ j, c j 0 ≠ 0)
    (hcard : (Finset.univ.filter (fun j => c j 0 = a)).card ≤ κ)
    (hsep : ∀ j k, j ≠ k → c j 0 = c k 0 → ∀ i : Fin m, c j i.succ ≠ c k i.succ)
    (hgen : IntermediateField.adjoin ℂ (Set.range (fibre a x)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (hz : ∃ i, Transcendental ℂ ((fibre a x) i))
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (σ : ℚ) (hσ : 0 < σ)
    (hvol : (κ : ℝ) * (1 + 3 * (σ : ℝ)) ^ m *
      (∏ i : Fin m, (w i.succ : ℝ)) / (∏ i : Fin m, (v i.succ : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin m), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m σ * (∏ j ∈ B, (v j.succ : ℝ)) <
        ∏ j ∈ A, (w j.succ : ℝ))
    (hratio : ∀ i : Fin m, (1 + (σ : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    ¬ CurveContactSum.weightedDegree hfinite (fibre a x) w <
      (1 + (σ : ℝ)) * ∑ p ∈ places hfinite (fibre a x) c hz,
        (contact hres hfinite (fibre a x) c hz v p : ℝ) := by
  classical
  intro hexcess
  have hdeg := FibreContact.weightedDegree_const hfinite a w x
  have hex : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1 + (σ : ℝ)) * ∑ p ∈ places hfinite (fibre a x) c hz,
        (contact hres hfinite (fibre a x) c hz v p : ℝ) := by
    have hd : CurveContactSum.weightedDegree hfinite (fibre a x) w = CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := hdeg
    rw [hd] at hexcess
    exact hexcess
  have haux := eventually_exists_fibre_auxiliary c a hcard
    (fun i => w i.succ) (fun i => v i.succ)
    (fun i => hw i.succ) (fun i => hv i.succ) σ hσ hvol
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniformRectangles m (fun i : Fin m => (v i.succ : ℝ))
      (fun i => by exact_mod_cast hv i.succ) ((σ : ℝ) / ((m : ℝ) + 2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := fibre_words_vanish hres hfinite a ha x c hc0 hz
    w v hw hv σ hσ N hN F hF hjet hex
  have hheight : (CurveFieldRigidity.coordinateKernel x).height ≤ (m : ℕ∞) :=
    CurvePrimeHeight.kernel_height_le x (CurveFieldRigidity.fibre_generates a x hgen) htrdeg
  obtain ⟨i, b, hib⟩ := CurveFieldRigidity.ordinary_coordinate_constant
    (m := m) (n := m) (by omega) x m le_rfl hheight
    (fun i => w i.succ) (fun i => hw i.succ)
    (fun i => (v i.succ : ℝ)) (fun i => by exact_mod_cast hv i.succ)
    σ N (by exact_mod_cast hσ) (by exact_mod_cast hN) hrectN F hF0 hF hwords hseparated
  obtain ⟨p0, hp0⟩ := CurveInequality.places_nonempty_of_excess
    hres hfinite (fibre a x) c hz w v σ hexcess
  let j0 := center hfinite (fibre a x) c hz p0 hp0
  have hj0a : c j0 0 = a := center_zero_eq hfinite a x c hz p0 hp0
  have hj0b : c j0 i.succ = b :=
    (CurveCenters.Centered.constant_coordinate ((fun k => centered hfinite (fibre a x) c hz p0 hp0 k.succ) :
      CurveCenters.Centered x (fun k => c j0 k.succ) p0) i b hib).symm
  have hcenters : ∀ p (hp : p ∈ places hfinite (fibre a x) c hz),
      center hfinite (fibre a x) c hz p hp = j0 := by
    intro p hp
    by_contra hne
    have hpa := center_zero_eq hfinite a x c hz p hp
    have hpb := (CurveCenters.Centered.constant_coordinate ((fun k => centered hfinite (fibre a x) c hz p hp k.succ) :
      CurveCenters.Centered x
        (fun k => c (center hfinite (fibre a x) c hz p hp) k.succ) p) i b hib).symm
    exact hsep _ _ hne (hpa.trans hj0a.symm) i (hpb.trans hj0b.symm)
  let S := places hfinite (fibre a x) c hz
  let μ := fun p => (contact hres hfinite (fibre a x) c hz v p : ℝ)
  have hcenter : ∀ p ∈ S, CurveCenters.Centered x (fun i => c j0 i.succ) p := by
    intro p hp k
    simpa only [hcenters p hp, fibre_succ] using
      centered hfinite (fibre a x) c hz p hp k.succ
  have hnc : ∃ k, x k ≠ algebraMap ℂ E (c j0 k.succ) :=
    PlaceCenteredBranch.fibre_nonconstant x (c j0)
      (by rw [hj0a]; exact nonconstant _ _ hz)
  obtain ⟨k, hk⟩ := hnc
  have hcoord := CoordinateContactBound.coordinate_contact_sum_le hfinite x
    (fun i => c j0 i.succ) (fun i => w i.succ) (fun i => v i.succ)
    (fun i => hw i.succ) (fun i => hv i.succ) k (sub_ne_zero.mpr hk)
    S hcenter (fun p _ => hres p) μ (by
      intro p hp
      let := hres p
      have heq := contact_fibre hres hfinite a ha x c hz v p hp
      have hcongr {a' b' : Fin m → ℂ} (hab : a' = b')
          (ha' : CurveCenters.Centered x a' p) (hna : ∃ i, x i ≠ algebraMap ℂ E (a' i))
          (hb' : CurveCenters.Centered x b' p) (hnb : ∃ i, x i ≠ algebraMap ℂ E (b' i)) :
          PlaceCenteredBranch.ordinaryContact p x a' ha' hna (fun i => v i.succ) =
            PlaceCenteredBranch.ordinaryContact p x b' hb' hnb (fun i => v i.succ) := by
        subst b'
        rfl
      exact congrArg (fun q : ℚ => (q : ℝ)) (heq.trans (hcongr
        (funext (fun i => congrArg (fun j => c j i.succ) (hcenters p hp))) _ _
        (hcenter p hp) ⟨k, hk⟩)))
  have hsum : 0 < ∑ p ∈ S, μ p := by
    have hn := CurveContactSum.weightedDegree_nonneg hfinite x (fun i => w i.succ)
    have hs : (0 : ℝ) < 1 + σ := by exact_mod_cast (by linarith : (0 : ℚ) < 1 + σ)
    exact (mul_pos_iff_of_pos_left hs).mp (lt_of_le_of_lt hn hex)
  have hwk : (0 : ℝ) < w k.succ := by exact_mod_cast hw k.succ
  have hb := mul_lt_mul_of_pos_left hex hwk
  have hr := mul_lt_mul_of_pos_right (hratio k) hsum
  nlinarith

/-- The curve inequality with bounded multiplicity of exponential fibres. -/
theorem weighted_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E] {m K κ : ℕ}
    (y : E) (x : Fin m → E) (c : Fin K → Fin (m + 1) → ℂ)
    (hc0 : ∀ j, c j 0 ≠ 0)
    (hcard : ∀ a : ℂ, (Finset.univ.filter (fun j => c j 0 = a)).card ≤ κ)
    (hsep : ∀ j k, j ≠ k → c j 0 = c k 0 → ∀ i : Fin m, c j i.succ ≠ c k i.succ)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (m + 1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (σ : ℚ) (hσ : 0 < σ)
    (hvol : (K : ℝ) * (1 + 3 * (σ : ℝ)) ^ (m + 1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hfibre : (κ : ℝ) * (1 + 3 * (σ : ℝ)) ^ m *
      (∏ i : Fin m, (w i.succ : ℝ)) / (∏ i : Fin m, (v i.succ : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m σ * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1 + (σ : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (m + 1) → E := Fin.cases y x
    let hz := LiuJiangZhang.RepeatedFibres.nonconstant_coordinates z hgen htrdeg
    (1 + (σ : ℝ)) * ∑ p ∈ places hfinite z c hz,
      (contact hres hfinite z c hz v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  dsimp only
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let z : Fin (m + 1) → E := Fin.cases y x
  have hz := LiuJiangZhang.RepeatedFibres.nonconstant_coordinates z hgen htrdeg
  change (1 + (σ : ℝ)) * ∑ p ∈ places hfinite z c hz,
    (contact hres hfinite z c hz v p : ℝ) ≤ CurveContactSum.weightedDegree hfinite z w
  by_contra h
  have hexcess := lt_of_not_ge h
  obtain ⟨p0, hp0⟩ := CurveInequality.places_nonempty_of_excess
    hres hfinite z c hz w v σ hexcess
  have hy := CurveInequality.excess_implies_zeroth_constant hres hfinite z c hc0 hz
    (CurvePrimeHeight.kernel_height_succ_le z hgen htrdeg)
    w v hw hv σ hσ hvol hseparated hexcess p0 hp0
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin K, y = algebraMap ℂ E (c j0 0) := ⟨_, hy⟩
  subst hj0
  exact no_fibre_excess hres hfinite (c j0 0) (hc0 j0) x c hc0
    (hcard _) hsep hgen htrdeg hz w v hw hv σ hσ hfibre
    (FibreWeightSeparation.positive_indices (fun i => (w i : ℝ))
      (fun i => (v i : ℝ)) (comparisonConstant m σ) hseparated)
    hratio hexcess

end
end LiuJiangZhang.RepeatedFibres
