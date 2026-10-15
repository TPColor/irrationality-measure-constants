import QuadraticFieldCriterion.SimplexCounts
import Mathlib.Algebra.BigOperators.Field

/-! # Joint row and transverse counting along admissible degrees -/

namespace QuadraticField

open Filter Topology

/-- Both counting limits hold along one progression divisible by the
interpolation modulus, even though the two sets have different dimensions. -/
theorem exists_admissible_row_transverse_ratio (m K : ℕ)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (w : Fin m → ℚ) (hw : ∀ i, 0 < w i) (R : ℕ) (hR : 0 < R) :
    ∃ L : ℕ, 0 < L ∧ R ∣ L ∧
      Tendsto (fun n : ℕ =>
        ((ImaginaryQuadratic.jetIndices K v (((n : ℚ) + 1) * (L : ℚ))).card : ℝ) /
          ((((n : ℝ) + 1) * (L : ℝ)) *
            ((ImaginaryQuadratic.monomialIndices w (((n : ℚ) + 1) * (L : ℚ))).card : ℝ)))
        atTop (𝓝 (((K : ℝ) / ((m + 1).factorial * ∏ i, (v i : ℝ))) /
          (1 / (m.factorial * ∏ i, (w i : ℝ))))) := by
  let u : Fin (m + 1) ⊕ Fin m → ℚ := Sum.elim v w
  have hu : ∀ i, 0 < u i := fun i => Sum.rec hv hw i
  obtain ⟨L, hL, step, hstep, hscale⟩ := exists_integer_weight_period u hu
  let L' := L * R
  have hL' : 0 < L' := Nat.mul_pos hL hR
  have hvscale : ∀ i, v i * ((step (Sum.inl i) * R : ℕ) : ℚ) = (L' : ℚ) := by
    intro i
    dsimp [L']
    push_cast
    rw [← mul_assoc, show v i * (step (Sum.inl i) : ℚ) = L from hscale (Sum.inl i)]
  have hwscale : ∀ i, w i * ((step (Sum.inr i) * R : ℕ) : ℚ) = (L' : ℚ) := by
    intro i
    dsimp [L']
    push_cast
    rw [← mul_assoc, show w i * (step (Sum.inr i) : ℚ) = L from hscale (Sum.inr i)]
  have hrows := strict_simplex_volume_limit v hv (fun i => step (Sum.inl i) * R)
    (fun i => Nat.mul_pos (hstep _) hR) (by exact_mod_cast hL') hvscale
  have htrans := (weighted_simplex_volume_limit w hw (fun i => step (Sum.inr i) * R)
    (fun i => Nat.mul_pos (hstep _) hR) (by exact_mod_cast hL') hwscale).comp
      (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, Rat.cast_natCast,
    Fintype.card_fin] at hrows htrans
  have hden : (1 / (m.factorial * ∏ i, (w i : ℝ))) ≠ 0 := by
    apply ne_of_gt
    exact one_div_pos.mpr (mul_pos (by positivity) (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)))
  have h := (hrows.const_mul (K : ℝ)).div htrans hden
  refine ⟨L', hL', dvd_mul_left _ _, ?_⟩
  convert h using 1
  · funext n
    simp only [Pi.div_apply]
    rw [card_jetIndices, Nat.cast_mul]
    have hH : ((n : ℝ) + 1) * (L' : ℝ) ≠ 0 := by positivity
    simp only [pow_succ]
    field_simp
  · ring_nf

theorem monomialIndices_div_weight {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) {A : ℚ} (hA : 0 < A) (H : ℚ) :
    ImaginaryQuadratic.monomialIndices (fun i => w i / A) H =
      ImaginaryQuadratic.monomialIndices w (A * H) := by
  classical
  ext a
  rw [ImaginaryQuadratic.mem_monomialIndices_iff _ (fun i => div_pos (hw i) hA),
    ImaginaryQuadratic.mem_monomialIndices_iff _ hw]
  have heq : ImaginaryQuadratic.weightedDegree (fun i => w i / A) a =
      ImaginaryQuadratic.weightedDegree w a / A := by
    simp only [ImaginaryQuadratic.weightedDegree, Finset.sum_div, div_mul_eq_mul_div]
  rw [heq, div_le_iff₀ hA, mul_comm H A]

theorem exists_collision_count_ratio (m K : ℕ) (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    {v₀ θ A : ℚ} (hv₀ : 0 < v₀) (hθ : 0 < θ) (hA : 0 < A)
    (R : ℕ) (hR : 0 < R) :
    ∃ L : ℕ, 0 < L ∧ R ∣ L ∧
      Tendsto (fun n : ℕ =>
        ((ImaginaryQuadratic.jetIndices K (Fin.cases v₀ (fun i => w i / θ))
          (((n : ℚ) + 1) * (L : ℚ))).card : ℝ) /
          ((((n : ℝ) + 1) * (L : ℝ)) *
            ((ImaginaryQuadratic.monomialIndices w (A * (((n : ℚ) + 1) * (L : ℚ)))).card : ℝ)))
        atTop (𝓝 ((K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v₀ : ℝ) * (A : ℝ) ^ m))) := by
  let v : Fin (m + 1) → ℚ := Fin.cases v₀ (fun i => w i / θ)
  have hv : ∀ i, 0 < v i := fun i => Fin.cases hv₀ (fun i => div_pos (hw i) hθ) i
  obtain ⟨L, hL, hRL, h⟩ := exists_admissible_row_transverse_ratio m K v hv
    (fun i => w i / A) (fun i => div_pos (hw i) hA) R hR
  refine ⟨L, hL, hRL, ?_⟩
  simp_rw [monomialIndices_div_weight w hw hA] at h
  have hvprod : (∏ i, (v i : ℝ)) = (v₀ : ℝ) * (∏ i, (w i : ℝ)) / (θ : ℝ) ^ m := by
    rw [Fin.prod_univ_succ]
    simp only [v, Fin.cases_zero, Fin.cases_succ, Rat.cast_div, Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hwprod : (∏ i, ((w i / A : ℚ) : ℝ)) = (∏ i, (w i : ℝ)) / (A : ℝ) ^ m := by
    simp [Rat.cast_div, Finset.prod_div_distrib]
  have hp : (∏ i, (w i : ℝ)) ≠ 0 := (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hv₀' : (v₀ : ℝ) ≠ 0 := by exact_mod_cast hv₀.ne'
  have hθ' : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  convert h using 1
  rw [hvprod, hwprod, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

end QuadraticField
