import ExternalResults.RepeatedFibres.Packets
import ExternalResults.RepeatedFibres.Thresholds
import LogIrrationalityMeasure.Approximation.Sigma

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogExponent
open LiuJiangZhang.RepeatedFibres.AdmissibleBlowupGeometry WeightedGeometryScale
open scoped BigOperators

noncomputable section

theorem fibre_product_ratio {m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 < w i) (θ : ℚ) :
    (∏ i, (w i : ℝ)) / (∏ i, ((w i / θ : ℚ) : ℝ)) = (θ : ℝ) ^ m := by
  have hp : (∏ i, (w i : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hw i).ne')
  simp only [Rat.cast_div, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  field_simp [hp]

theorem product_ratio {m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 < w i) (w0 v0 θ : ℚ) :
    (∏ i : Fin (m + 1), ((Fin.cases w0 w i : ℚ) : ℝ)) /
      (∏ i : Fin (m + 1), ((Fin.cases v0 (fun i => w i / θ) i : ℚ) : ℝ)) =
      ((w0 : ℝ) / v0) * (θ : ℝ) ^ m := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_div_mul_comm]
  simp only [Fin.cases_zero, Fin.cases_succ, fibre_product_ratio w hw θ]

/-- Separated-weight interpolation with arbitrary bounded exponential fibres.
Both thresholds and divisibility are chosen independently of the centres. -/
theorem interpolation
    (m K κ : ℕ) (hm : 1 ≤ m)
    (w0 v0 θ : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hvolume : (K : ℚ) * (w0 / v0) * θ ^ m < 1)
    (hfibreVolume : (κ : ℚ) * θ ^ m < 1) :
    ∃ thresholds : Fin m → List ℚ → ℚ,
      ∀ w : Fin m → ℚ,
        (∀ i, 0 < w i) →
        (∀ i, thresholds i ((List.ofFn w).take i.val) < w i) →
        ∃ R : ℕ, 0 < R ∧
          ∀ (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ),
            (∀ j, y j ≠ 0) →
            (∀ z : ℂ, (Finset.univ.filter (fun j => y j = z)).card ≤ κ) →
            (∀ j k, j ≠ k → y j = y k → ∀ i, c j i ≠ c k i) →
            ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
              ∀ target : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
                ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
                  (∀ α ∈ P.support,
                    Finsupp.weight (Fin.cases w0 w) α ≤ (n * R : ℕ)) ∧
                  ∀ (j : Fin K) (α : Fin (m + 1) →₀ ℕ),
                    Finsupp.weight (Fin.cases v0 (fun i => w i / θ)) α < (n * R : ℕ) →
                    MvPowerSeries.coeff α
                      (FormalLogJet.formalJet (Fin.cases (y j) (c j)) P) = target j α := by
  classical
  obtain ⟨σ, hσ, hσvol, hσfibre, hσθ⟩ := exists_small_rational_sigma m
    ((K : ℝ) * ((w0 : ℝ) / v0) * (θ : ℝ) ^ m)
    ((κ : ℝ) * (θ : ℝ) ^ m) θ
    (by exact_mod_cast hvolume) (by exact_mod_cast hfibreVolume) (by exact_mod_cast hθ1)
  have hC : 0 < PersistentWeightComparison.comparisonConstant m σ := by
    unfold PersistentWeightComparison.comparisonConstant
    positivity
  obtain ⟨thresholds, hthresholds⟩ := exists_thresholds m w0 v0 θ
    (PersistentWeightComparison.comparisonConstant m σ) hw0 hv0 hθ hC
  refine ⟨thresholds, ?_⟩
  intro w hw hlarge
  let W : Fin (m + 1) → ℚ := Fin.cases w0 w
  let V : Fin (m + 1) → ℚ := Fin.cases v0 (fun i => w i / θ)
  have hW : ∀ i, 0 < W i := Fin.cases hw0 hw
  have hV : ∀ i, 0 < V i := Fin.cases hv0 (fun i => div_pos (hw i) hθ)
  let s := chooseScale W V hW hV
  refine ⟨s.radius, s.radius_pos, ?_⟩
  intro y c hy hcard hsep
  let d : InterpolationData := {
    m := m, K := K, κ := κ, m_pos := hm
    curveDegreeWeights := W, curveJetWeights := V
    curveDegreeWeights_pos := hW, curveJetWeights_pos := hV
    sigma := σ, sigma_pos := hσ
    curveCenters := fun (j : Fin K) (i : Fin (m + 1)) => Fin.cases (y j) (c j) i
    curveCenters_zero_ne_zero := by simpa only [Fin.cases_zero] using hy
    fibre_card := by
      intro a
      apply le_trans (Finset.card_le_card ?_) (hcard a)
      intro j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hj_eq := (Finset.mem_filter.mp hj).2
      simpa only [Fin.cases_zero] using hj_eq
    fibre_separated := by simpa only [Fin.cases_zero, Fin.cases_succ] using hsep
    curve_volume := by
      calc
        _ = (1 + 3 * (σ : ℝ)) ^ (m + 1) *
            ((K : ℝ) * ((∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)))) := by ring
        _ = (1 + 3 * (σ : ℝ)) ^ (m + 1) *
            ((K : ℝ) * ((w0 : ℝ) / v0) * (θ : ℝ) ^ m) := by
          rw [show (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) =
            ((w0 : ℝ) / v0) * (θ : ℝ) ^ m from product_ratio w hw w0 v0 θ]
          ring
        _ < 1 := hσvol
    curve_fibre_volume := by
      calc
        _ = (1 + 3 * (σ : ℝ)) ^ m *
            ((κ : ℝ) * ((∏ i : Fin m, (w i : ℝ)) /
              (∏ i : Fin m, ((w i / θ : ℚ) : ℝ)))) := by dsimp [W, V]; ring
        _ = (1 + 3 * (σ : ℝ)) ^ m * ((κ : ℝ) * (θ : ℝ) ^ m) := by
          rw [fibre_product_ratio w hw θ]
        _ < 1 := hσfibre
    curve_separated_weight_products := hthresholds w hw hlarge
    curve_coordinate_ratio := by
      intro i
      dsimp [W, V]
      rw [Rat.cast_div]
      apply (lt_div_iff₀ (show (0 : ℝ) < θ by exact_mod_cast hθ)).mpr
      have hi : (0 : ℝ) < w i := by exact_mod_cast hw i
      nlinarith [mul_lt_mul_of_pos_right hσθ hi] }
  simpa only [d, W, V, s, LiuJiangZhang.RepeatedFibres.AdmissibleBlowupGeometry.scale, Nat.cast_mul] using eventual_packets d

end
end LiuJiangZhang.RepeatedFibres
