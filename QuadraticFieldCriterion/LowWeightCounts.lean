import QuadraticFieldCriterion.CollisionAlternatives
import QuadraticFieldCriterion.SimplexRatios

/-! # The low-weight set used in the analytic alternative -/

namespace QuadraticField

noncomputable def lowWeightIndices {m : ℕ} (w : Fin m → ℚ) (H : ℚ) : Finset (Fin m → ℕ) := by
  classical
  exact (ImaginaryQuadratic.monomialIndices w H).image (fun a i => a i)

theorem mem_lowWeightIndices_iff {m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    (H : ℚ) (a : Fin m → ℕ) :
    a ∈ lowWeightIndices w H ↔ (∑ i, w i * (a i : ℚ)) ≤ H := by
  classical
  constructor
  · rintro h
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
    exact (ImaginaryQuadratic.mem_monomialIndices_iff w hw H b).mp hb
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨Finsupp.equivFunOnFinite.symm a, ?_, rfl⟩
    exact (ImaginaryQuadratic.mem_monomialIndices_iff w hw H _).mpr h

theorem card_lowWeightIndices {m : ℕ} (w : Fin m → ℚ) (H : ℚ) :
    (lowWeightIndices w H).card = (ImaginaryQuadratic.monomialIndices w H).card := by
  classical
  exact Finset.card_image_of_injective _ (fun a b hab => Finsupp.ext (congrFun hab))

theorem card_lowWeightIndices_pos {m : ℕ} (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {H : ℚ} (hH : 0 ≤ H) : 0 < (lowWeightIndices w H).card := by
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, (mem_lowWeightIndices_iff w hw H _).mpr ?_⟩
  simpa using hH

theorem weighted_collision_exponent_bound {ι : Type*} [Fintype ι] {m : ℕ}
    (a : ι → Fin m → ℕ) (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {A H : ℚ} {η ν c : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hη : 0 ≤ η) (hν : 0 ≤ ν) (hc : 0 ≤ c) :
    -ν * (∑ r, ∑ i, (w i : ℝ) * (a r i : ℝ)) - c * collisionMass a ≤
      max (-c * (η ^ 2 * (Fintype.card ι : ℝ) ^ 2 /
        (ImaginaryQuadratic.monomialIndices w (A * H)).card))
        (-ν * ((1 - η) * Fintype.card ι * ((A : ℝ) * (H : ℝ)))) := by
  classical
  have h := weight_collision_exponent_le_max a
    (fun b => ∑ i, (w i : ℝ) * (b i : ℝ)) (lowWeightIndices w (A * H))
    (fun b => Finset.sum_nonneg (fun i _ => mul_nonneg (by exact_mod_cast (hw i).le) (Nat.cast_nonneg _)))
    (show (0 : ℝ) ≤ (A : ℝ) * (H : ℝ) by exact_mod_cast mul_nonneg hA hH)
    hη hν hc
    (fun b => by
      rw [mem_lowWeightIndices_iff w hw]
      exact_mod_cast (Iff.rfl : (∑ i, w i * (b i : ℚ)) ≤ A * H ↔ (∑ i, w i * (b i : ℚ)) ≤ A * H))
    (card_lowWeightIndices_pos w hw (mul_nonneg hA hH))
  rwa [card_lowWeightIndices] at h

end QuadraticField
