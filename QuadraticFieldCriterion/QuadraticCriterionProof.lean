import QuadraticFieldCriterion.ApproximationConclusion
import QuadraticFieldCriterion.DeterminantComparison
import QuadraticFieldCriterion.TruncatedInterpolation
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Quadratic field criterion: statement and arithmetic foundations

The criterion theorem is in `QuadraticCriterionStatement.lean`.
-/

namespace QuadraticField

/-- The root convention in the manuscript, including imaginary quadratic fields. -/
noncomputable def root (D : ℤ) : ℂ :=
  if 0 ≤ D then (Real.sqrt (D : ℝ) : ℂ)
  else Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)

theorem root_sq (D : ℤ) : root D ^ 2 = (D : ℂ) := by
  unfold root
  split_ifs with hD
  · exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ D by exact_mod_cast hD)
  · have hD' : (0 : ℝ) ≤ -(D : ℝ) := by
      have : (D : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hD
      linarith
    have hs : (Real.sqrt (-(D : ℝ)) : ℂ) ^ 2 = -(D : ℂ) := by
      exact_mod_cast Real.sq_sqrt hD'
    rw [mul_pow, Complex.I_sq, hs]
    ring

theorem root_ne_zero {D : ℤ} (hD : ¬ IsSquare D) : root D ≠ 0 := by
  intro h
  have hsq := root_sq D
  rw [h, zero_pow (by norm_num)] at hsq
  have hzero : D = 0 := by exact_mod_cast hsq.symm
  exact hD (hzero ▸ IsSquare.zero)

/-- Nonzero numerators separate every additive coordinate, even when powers
of the exponential repeat. This is the centre condition in Theorem 9. -/
theorem additive_centres_injective {D : ℤ} (hD : ¬ IsSquare D)
    (p : ℤ) (q : ℕ) (hp : p ≠ 0) (hq : 0 < q) :
    Function.Injective (fun j : ℕ => (j : ℂ) * (2 * root D * (p : ℂ) / (q : ℂ))) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc : 2 * root D * (p : ℂ) / (q : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (root_ne_zero hD)) hpC) hqC
  intro j k hjk
  exact_mod_cast mul_right_cancel₀ hc hjk

/-- Positive real quadratic fields have distinct multiplicative centres. -/
theorem multiplicative_centres_injective {D : ℤ} (hD : 0 < D)
    {x : ℝ} (hx : x ≠ 0) :
    Function.Injective (fun j : ℕ => (Complex.exp (2 * root D * (x : ℂ))) ^ j) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : Real.sqrt (D : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hDR).ne'
  have ht : 2 * Real.sqrt (D : ℝ) * x ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hs) hx
  have he : Real.exp (2 * Real.sqrt (D : ℝ) * x) ≠ 1 := by
    exact fun h => ht ((Real.exp_eq_one_iff _).mp h)
  have hα : Complex.exp (2 * root D * (x : ℂ)) =
      (Real.exp (2 * Real.sqrt (D : ℝ) * x) : ℂ) := by
    rw [root, ite_eq_left hD.le, Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  intro j k hjk
  dsimp only at hjk
  rw [hα, ← Complex.ofReal_pow, ← Complex.ofReal_pow] at hjk
  have hreal := Complex.ofReal_injective hjk
  exact pow_right_injective₀ (Real.exp_pos _) he hreal

/-- The quadratic algebra over the rationals. It is a field when `D` is nonsquare. -/
abbrev Algebra (D : ℤ) := QuadraticAlgebra ℚ (D : ℚ) 0

/-- The chosen embedding into the complex numbers. -/
noncomputable def embedding (D : ℤ) : Algebra D →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨root D, by
    simpa [pow_two] using root_sq D⟩

theorem embedding_apply (D : ℤ) (z : Algebra D) :
    embedding D z = (z.re : ℂ) + (z.im : ℂ) * root D := by
  simp [embedding, QuadraticAlgebra.lift, Algebra.smul_def]

/-- The other embedding, obtained by applying the quadratic involution. -/
noncomputable def conjugateEmbedding (D : ℤ) (z : Algebra D) : ℂ :=
  embedding D (star z)

theorem conjugateEmbedding_apply (D : ℤ) (z : Algebra D) :
    conjugateEmbedding D z = (z.re : ℂ) - (z.im : ℂ) * root D := by
  simp [conjugateEmbedding, embedding_apply, sub_eq_add_neg]

theorem conjugateEmbedding_eq_conj {D : ℤ} (hD : D < 0) (z : Algebra D) :
    conjugateEmbedding D z = star (embedding D z) := by
  have hn : ¬ 0 ≤ D := not_le.mpr hD
  simp [conjugateEmbedding_apply, embedding_apply, root, hn, sub_eq_add_neg]

theorem norm_eq (D : ℤ) (z : Algebra D) :
    QuadraticAlgebra.norm z = z.re ^ 2 - (D : ℚ) * z.im ^ 2 := by
  simp only [QuadraticAlgebra.norm_def]
  ring

/-- The product of the two embeddings is exactly the rational field norm. -/
theorem embeddings_mul (D : ℤ) (z : Algebra D) :
    embedding D z * conjugateEmbedding D z =
      ((QuadraticAlgebra.norm z : ℚ) : ℂ) := by
  rw [embedding_apply, conjugateEmbedding_apply, norm_eq]
  push_cast
  linear_combination -(z.im : ℂ) ^ 2 * root_sq D

/-- Both determinants use the same rows and columns. The second is obtained by
conjugating the algebraic entries, rather than changing the logarithm series. -/
theorem determinant_embeddings_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℤ) (M : Matrix ι ι (Algebra D)) :
    (M.map (embedding D)).det * (M.map (conjugateEmbedding D)).det =
      ((QuadraticAlgebra.norm M.det : ℚ) : ℂ) := by
  let σ : Algebra D →+* ℂ := (embedding D).toRingHom.comp (starRingEnd (Algebra D))
  have hσ : (M.map (conjugateEmbedding D)).det = conjugateEmbedding D M.det :=
    (σ.map_det M).symm
  have he : (M.map (embedding D)).det = embedding D M.det :=
    ((embedding D).map_det M).symm
  rw [he, hσ]
  exact embeddings_mul D M.det

theorem norm_ne_zero {D : ℤ} (hD : ¬ IsSquare D) {z : Algebra D}
    (hz : z ≠ 0) : QuadraticAlgebra.norm z ≠ 0 := by
  let : Fact (¬ IsSquare (D : ℚ)) :=
    ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  exact fun h => hz (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)

theorem embedding_injective {D : ℤ} (hD : ¬ IsSquare D) :
    Function.Injective (embedding D) := by
  let : Fact (¬ IsSquare (D : ℚ)) :=
    ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  exact (embedding D).injective

/-- Norm one sends an exponential parameter to its reciprocal in the other embedding. -/
theorem conjugateEmbedding_eq_inv {D : ℤ} {z : Algebra D}
    (hz : QuadraticAlgebra.norm z = 1) :
    conjugateEmbedding D z = (embedding D z)⁻¹ := by
  have h := embeddings_mul D z
  rw [hz, Rat.cast_one] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Membership in `ℚ(√D)` together with its norm-one condition. -/
def HasNormOneCoordinates (D : ℤ) (α : ℂ) : Prop :=
  ∃ z : Algebra D, embedding D z = α ∧ QuadraticAlgebra.norm z = 1

/-- A coordinate version of the membership and norm hypotheses in Theorem 1. -/
theorem hasNormOneCoordinates_iff (D : ℤ) (α : ℂ) :
    HasNormOneCoordinates D α ↔
      ∃ a b : ℚ, α = (a : ℂ) + (b : ℂ) * root D ∧
        a ^ 2 - (D : ℚ) * b ^ 2 = 1 := by
  constructor
  · rintro ⟨z, hz, hN⟩
    exact ⟨z.re, z.im, hz.symm.trans (embedding_apply D z),
      (norm_eq D z).symm.trans hN⟩
  · rintro ⟨a, b, hα, hN⟩
    exact ⟨⟨a, b⟩, (embedding_apply D ⟨a, b⟩).trans hα.symm,
      (norm_eq D ⟨a, b⟩).trans hN⟩

/-- In an imaginary quadratic field the exponential has norm one automatically. -/
theorem exponential_norm_one_of_negative {D : ℤ} (hD : D < 0) (x : ℝ)
    (z : Algebra D) (hz : embedding D z = Complex.exp (2 * root D * (x : ℂ))) :
    QuadraticAlgebra.norm z = 1 := by
  have hn : ¬ 0 ≤ D := not_le.mpr hD
  have hmod : ‖embedding D z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    simp [root, hn, Complex.mul_re, Complex.mul_im]
  have h := embeddings_mul D z
  rw [conjugateEmbedding_eq_conj hD] at h
  change embedding D z * (starRingEnd ℂ) (embedding D z) =
    ((QuadraticAlgebra.norm z : ℚ) : ℂ) at h
  rw [Complex.mul_conj', hmod] at h
  norm_num at h
  exact_mod_cast h.symm

/-- A positive integer clears both coordinates and their conjugates together. -/
theorem exists_denominator_clear (D : ℤ) (z : Algebra D) :
    ∃ s : ℕ, 0 < s ∧ ∃ a b : ℤ,
      (s : ℂ) * embedding D z = (a : ℂ) + (b : ℂ) * root D ∧
      (s : ℂ) * conjugateEmbedding D z = (a : ℂ) - (b : ℂ) * root D := by
  let a := z.re
  let b := z.im
  have ha : (a.den : ℂ) * (a : ℂ) = (a.num : ℂ) := by
    rw [Rat.cast_def]
    have hd : (a.den : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
    field_simp
  have hb : (b.den : ℂ) * (b : ℂ) = (b.num : ℂ) := by
    rw [Rat.cast_def]
    have hd : (b.den : ℂ) ≠ 0 := by exact_mod_cast b.pos.ne'
    field_simp
  refine ⟨a.den * b.den, Nat.mul_pos a.pos b.pos,
    a.num * (b.den : ℤ), b.num * (a.den : ℤ), ?_, ?_⟩
  · rw [embedding_apply]
    change ((a.den * b.den : ℕ) : ℂ) * ((a : ℂ) + (b : ℂ) * root D) = _
    push_cast
    linear_combination (b.den : ℂ) * ha + (a.den : ℂ) * root D * hb
  · rw [conjugateEmbedding_apply]
    change ((a.den * b.den : ℕ) : ℂ) * ((a : ℂ) - (b : ℂ) * root D) = _
    push_cast
    linear_combination (b.den : ℂ) * ha - (a.den : ℂ) * root D * hb

/-- The algebraic integer norm in equation (3.1) cannot vanish. -/
theorem integer_norm_ne_zero {D a b : ℤ} (hD : ¬ IsSquare D)
    (hab : a ≠ 0 ∨ b ≠ 0) : a ^ 2 - D * b ^ 2 ≠ 0 := by
  let z : Algebra D := ⟨(a : ℚ), (b : ℚ)⟩
  have hz : z ≠ 0 := by
    intro h
    have ha : a = 0 := by
      have := congrArg QuadraticAlgebra.re h
      change (a : ℚ) = 0 at this
      exact_mod_cast this
    have hb : b = 0 := by
      have := congrArg QuadraticAlgebra.im h
      change (b : ℚ) = 0 at this
      exact_mod_cast this
    rcases hab with hab | hab <;> contradiction
  have hn := norm_ne_zero hD hz
  rw [norm_eq] at hn
  change (a : ℚ) ^ 2 - (D : ℚ) * (b : ℚ) ^ 2 ≠ 0 at hn
  exact_mod_cast hn

/-- The product of the two absolute values has the discrete lower bound (3.1).
This applies equally to real and imaginary quadratic fields. -/
theorem one_le_product_norm {D a b : ℤ} (hD : ¬ IsSquare D)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    1 ≤ ‖(a : ℂ) + (b : ℂ) * root D‖ *
      ‖(a : ℂ) - (b : ℂ) * root D‖ := by
  have hprod : ((a : ℂ) + (b : ℂ) * root D) *
      ((a : ℂ) - (b : ℂ) * root D) = ((a ^ 2 - D * b ^ 2 : ℤ) : ℂ) := by
    push_cast
    linear_combination -(b : ℂ) ^ 2 * root_sq D
  rw [← norm_mul, hprod]
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  have h := Int.one_le_abs (integer_norm_ne_zero hD hab)
  exact_mod_cast h

/-- Taking logarithms of the denominator-cleared norm bound gives the
averaged arithmetic cost; the scaling factor occurs twice in the norm. -/
theorem averaged_log_lower_bound {S : ℝ} {Δplus Δminus : ℂ}
    (hS : 0 < S) (hp : Δplus ≠ 0) (hm : Δminus ≠ 0)
    (hN : 1 ≤ S ^ 2 * (‖Δplus‖ * ‖Δminus‖)) :
    -Real.log S ≤ (Real.log ‖Δplus‖ + Real.log ‖Δminus‖) / 2 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hN
  rw [Real.log_one, Real.log_mul (pow_ne_zero _ hS.ne')
    (mul_ne_zero (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hm)),
    Real.log_pow, Real.log_mul (norm_ne_zero_iff.mpr hp)
      (norm_ne_zero_iff.mpr hm)] at h
  norm_num at h
  linarith

/-- Proposition 6 uses the average of the two normalized logarithms.
Both embeddings have the same upper bound, so averaging loses no exponent. -/
theorem conjugate_determinant_estimates_incompatible
    {ν A η θ b c L Ear Etr Ehol δ Dplus Dminus : ℝ}
    (hν : 1 ≤ ν) (hb0 : 0 ≤ b) (hbθ : b ≤ θ)
    (hgap : Ear + Etr + Ehol + δ < ν * (A * (1 - η) - θ) - (1 - θ))
    (hcollision : 1 + Ear + Etr + Ehol + δ < c * L)
    (hlower : -(1 - b) - Ear ≤ (Dplus + Dminus) / 2)
    (hplus : Dplus ≤ Etr + Ehol + δ +
      max (-c * L) (-ν * (A * (1 - η) - b)))
    (hminus : Dminus ≤ Etr + Ehol + δ +
      max (-c * L) (-ν * (A * (1 - η) - b))) : False := by
  apply ImaginaryQuadratic.determinant_estimates_incompatible
    hν hb0 hbθ hgap hcollision hlower
  linarith

end QuadraticField
