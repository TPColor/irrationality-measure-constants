import QuadraticFieldCriterion.Parameters
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field

/-! # The dimension limits in the parameter choice

All constants in this file are fixed before dimension tends to infinity.
The integer part in `K = ⌊C^m⌋` is retained throughout the estimates.
-/

open Filter Topology

namespace QuadraticField

noncomputable def centreCount (C : ℝ) (m : ℕ) : ℕ := ⌊C ^ m⌋₊

noncomputable def degreeWeight (B : ℝ) (m : ℕ) : ℝ := (B ^ m)⁻¹

noncomputable def jetWeight (θ B C : ℝ) (m : ℕ) : ℝ :=
  2 * centreCount C m * θ ^ m * degreeWeight B m

theorem centreCount_ratio_tendsto {C : ℝ} (hC : 1 < C) :
    Tendsto (fun m => (centreCount C m : ℝ) / C ^ m) atTop (𝓝 1) :=
  tendsto_nat_floor_div_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hC)

theorem centreCount_pos {C : ℝ} (hC : 1 ≤ C) (m : ℕ) : 0 < centreCount C m := by
  exact Nat.floor_pos.mpr (one_le_pow₀ hC)

theorem centreCount_div_degreeWeight_tendsto {B C : ℝ}
    (hB : 0 < B) (hC : 1 < C) (hCB : C * B < 1) :
    Tendsto (fun m => (centreCount C m : ℝ) / degreeWeight B m) atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (mul_nonneg (by linarith : 0 ≤ C) hB.le) hCB
  have h := (centreCount_ratio_tendsto hC).mul hpow
  simp only [mul_zero] at h
  convert h using 1
  funext m
  dsimp [degreeWeight]
  rw [mul_pow]
  field_simp

theorem jetWeight_factorization {θ B C : ℝ} (hB : B ≠ 0) (hC : C ≠ 0) (m : ℕ) :
    jetWeight θ B C m =
      2 * ((centreCount C m : ℝ) / C ^ m) * (C * θ / B) ^ m := by
  dsimp [jetWeight, degreeWeight]
  rw [div_pow, mul_pow]
  field_simp

theorem jetWeight_tendsto_atTop {θ B C : ℝ}
    (hB : 0 < B) (hC : 1 < C) (hBCT : B < C * θ) :
    Tendsto (jetWeight θ B C) atTop atTop := by
  have hratio : 1 < C * θ / B := (one_lt_div hB).mpr hBCT
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hratio
  have hfloor : Tendsto (fun m => 2 * ((centreCount C m : ℝ) / C ^ m)) atTop (𝓝 2) := by
    simpa using (centreCount_ratio_tendsto hC).const_mul 2
  have h := hfloor.pos_mul_atTop (by norm_num : (0 : ℝ) < 2) hpow
  exact h.congr (fun m => (jetWeight_factorization hB.ne' (by linarith) m).symm)

theorem dimension_div_jetWeight_tendsto {θ B C : ℝ}
    (hB : 0 < B) (hC : 1 < C) (hBCT : B < C * θ) :
    Tendsto (fun m : ℕ => (m : ℝ) / jetWeight θ B C m) atTop (𝓝 0) := by
  have hratio : 1 < C * θ / B := (one_lt_div hB).mpr hBCT
  have hnum : Tendsto (fun m : ℕ => (m : ℝ) / (C * θ / B) ^ m) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 hratio
  have hden : Tendsto (fun m => 2 * ((centreCount C m : ℝ) / C ^ m)) atTop (𝓝 2) := by
    simpa using (centreCount_ratio_tendsto hC).const_mul 2
  have h := hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
  simp only [zero_div] at h
  convert h using 1
  funext m
  rw [jetWeight_factorization hB.ne' (by linarith) m]
  dsimp only [Pi.div_apply]
  rw [div_div, mul_comm]

theorem collisionSaving_tendsto_atTop {A B η : ℝ}
    (hA : 0 < A) (hAB : A < B) (hη : 0 < η) :
    Tendsto (fun m : ℕ => η ^ 2 * (B / A) ^ m / (2 * (m + 1))) atTop atTop := by
  have hratio : 1 < B / A := (one_lt_div hA).mpr hAB
  have hsmall : Tendsto (fun m : ℕ => (2 * ((m : ℝ) + 1)) / (B / A) ^ m)
      atTop (𝓝 0) := by
    have hn := tendsto_pow_const_div_const_pow_of_one_lt 1 hratio
    have hc := (tendsto_pow_atTop_atTop_of_one_lt hratio).const_div_atTop 1
    have h := (hn.add hc).const_mul 2
    simpa only [pow_one, zero_add, mul_zero, ← add_div, mul_div_assoc] using h
  have hpos : ∀ m : ℕ, 0 < (2 * ((m : ℝ) + 1)) / (B / A) ^ m := by
    intro m
    positivity
  have hinv := (tendsto_nhdsWithin_iff.mpr ⟨hsmall, Filter.Eventually.of_forall hpos⟩).inv_tendsto_nhdsGT_zero
  have h := hinv.const_mul_atTop (sq_pos_of_pos hη)
  convert h using 1
  funext m
  simp only [Pi.inv_apply]
  field_simp

/-- All dimension-dependent arithmetic and holomorphic errors can be made
small simultaneously, with arbitrary fixed constants in their numerators. -/
theorem dimension_error_tendsto_zero {θ B C : ℝ}
    (hB : 0 < B) (hC : 1 < C) (hCB : C * B < 1) (hBCT : B < C * θ)
    (a b d : ℝ) :
    Tendsto (fun m : ℕ => (a * m + b) / jetWeight θ B C m +
      d * ((centreCount C m : ℝ) / degreeWeight B m)) atTop (𝓝 0) := by
  have hlinear := (dimension_div_jetWeight_tendsto hB hC hBCT).const_mul a
  have hconstant := (jetWeight_tendsto_atTop hB hC hBCT).const_div_atTop b
  have hcentre := (centreCount_div_degreeWeight_tendsto hB hC hCB).const_mul d
  have h := (hlinear.add hconstant).add hcentre
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext m
  ring

/-- Choose a single finite dimension with small errors and a large collision
margin. The approximation weights and centres are chosen only afterwards. -/
theorem exists_dimension_with_margins {θ A B C η c ε : ℝ}
    (hA : 0 < A) (hAB : A < B) (hC : 1 < C)
    (hCB : C * B < 1) (hBCT : B < C * θ)
    (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) (a b d : ℝ) :
    ∃ m : ℕ, 0 < m ∧
      (a * m + b) / jetWeight θ B C m +
        d * ((centreCount C m : ℝ) / degreeWeight B m) < ε ∧
      2 < c * (η ^ 2 * (B / A) ^ m / (2 * (m + 1))) := by
  have hB : 0 < B := hA.trans hAB
  have he := dimension_error_tendsto_zero hB hC hCB hBCT a b d
  have hl := (collisionSaving_tendsto_atTop hA hAB hη).const_mul_atTop hc
  have hevent := he.eventually (gt_mem_nhds hε)
  have hlevent := hl.eventually (eventually_gt_atTop 2)
  obtain ⟨m, hm, he, hl⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hevent.and hlevent)).exists
  exact ⟨m, hm, he, hl⟩

theorem exists_dimension_with_arbitrary_margin {θ A B C η c ε : ℝ}
    (hA : 0 < A) (hAB : A < B) (hC : 1 < C)
    (hCB : C * B < 1) (hBCT : B < C * θ)
    (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) (a b d T : ℝ) :
    ∃ m : ℕ, 0 < m ∧
      (a * m + b) / jetWeight θ B C m +
        d * ((centreCount C m : ℝ) / degreeWeight B m) < ε ∧
      T < c * (η ^ 2 * (B / A) ^ m / (2 * (m + 1))) := by
  have he := dimension_error_tendsto_zero (hA.trans hAB) hC hCB hBCT a b d
  have hl := (collisionSaving_tendsto_atTop hA hAB hη).const_mul_atTop hc
  obtain ⟨m, hm, he, hl⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((he.eventually (gt_mem_nhds hε)).and (hl.eventually (eventually_gt_atTop T)))).exists
  exact ⟨m, hm, he, hl⟩

end QuadraticField
