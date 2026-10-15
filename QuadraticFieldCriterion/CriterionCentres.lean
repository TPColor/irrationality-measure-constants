import QuadraticFieldCriterion.InterpolationEntry
import QuadraticFieldCriterion.ApproximationSelection

/-! # The quadratic centres attached to rational approximations -/

namespace QuadraticField

theorem exists_integerOrder_denominator {D : ℤ} (hD : ¬ IsSquare D) (α : Algebra D) :
    ∃ s : ℕ, 0 < s ∧ (s : Algebra D) * α ∈ integerOrder D := by
  obtain ⟨s, hs, a, b, hplus, hminus⟩ := exists_denominator_clear D α
  refine ⟨s, hs, (mem_integerOrder_iff D _).mpr ⟨a, b, ?_⟩⟩
  apply embedding_injective hD
  rw [map_mul, map_natCast]
  simpa only [embedding_apply, Rat.cast_intCast] using hplus

noncomputable def powerCentres {D : ℤ} (α : Algebra D) (K : ℕ) : Fin K → Algebra D :=
  fun j => α ^ (j : ℕ)

noncomputable def rationalCentres (D : ℤ) {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ)
    (K : ℕ) : Fin K → Fin m → Algebra D :=
  fun j i => (j : Algebra D) * quadraticGenerator D * (p i : Algebra D) / (q i : Algebra D)

theorem powerCentres_cleared {D : ℤ} (α : Algebra D) (s K : ℕ)
    (hα : (s : Algebra D) * α ∈ integerOrder D) :
    ∀ j, ((s ^ K : ℕ) : Algebra D) * powerCentres α K j ∈ integerOrder D := by
  intro j
  rw [Nat.cast_pow]
  exact cleared_powers_mem_integerOrder D α s K j hα j.isLt.le

theorem rationalCentres_cleared {D : ℤ} (hD : ¬ IsSquare D) {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 0 < q i) (K : ℕ) :
    ∀ j i, (q i : Algebra D) * rationalCentres D p q K j i ∈ integerOrder D :=
  fun j i => additive_centre_cleared hD j (p i) (q i) (hq i)

theorem embedding_powerCentres {D : ℤ} (α : Algebra D) (K : ℕ) (ω : ℂ)
    (hα : embedding D α = Complex.exp ω) :
    ∀ j, embedding D (powerCentres α K j) = (Complex.exp ω) ^ (j : ℕ) := by
  intro j
  simp only [powerCentres, map_pow, hα]

theorem conjugateEmbedding_powerCentres {D : ℤ} (α : Algebra D) (K : ℕ) (ω : ℂ)
    (hα : embedding D α = Complex.exp ω) (hN : QuadraticAlgebra.norm α = 1) :
    ∀ j, conjugateEmbedding D (powerCentres α K j) = (Complex.exp (-ω)) ^ (j : ℕ) := by
  intro j
  have hc : conjugateEmbedding D α = Complex.exp (-ω) := by
    rw [conjugateEmbedding_eq_inv hN, hα, Complex.exp_neg]
  change embedding D (star (α ^ (j : ℕ))) = _
  rw [star_pow, map_pow]
  exact congrArg (fun z : ℂ => z ^ (j : ℕ)) hc

theorem embedding_rationalCentres {D : ℤ} (hD : ¬ IsSquare D) {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ)
    (K : ℕ) (j : Fin K) (i : Fin m) :
    embedding D (rationalCentres D p q K j i) =
      (j : ℂ) * (2 * root D) * (p i : ℂ) / (q i : ℂ) := by
  let : Fact (¬ IsSquare (D : ℚ)) := ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  simp only [rationalCentres, map_div₀, map_mul, map_natCast, map_intCast,
    embedding_quadraticGenerator]

theorem embedding_rationalCentres_injective {D : ℤ} (hD : ¬ IsSquare D) {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hp : ∀ i, p i ≠ 0) (hq : ∀ i, 0 < q i)
    (K : ℕ) (i : Fin m) :
    Function.Injective (fun j => embedding D (rationalCentres D p q K j i)) := by
  intro j k hjk
  have h := additive_centres_injective hD (p i) (q i) (hp i) (hq i)
  apply Fin.ext
  apply h
  simp only [embedding_rationalCentres hD] at hjk
  convert hjk using 1 <;> ring

noncomputable def approximationCentreError (γ : ℂ) (x : ℝ) (p : ℤ) (q j : ℕ) : ℂ :=
  (j : ℂ) * γ * (((p : ℝ) / (q : ℝ) - x : ℝ) : ℂ)

theorem embedding_rationalCentres_eq_translated {D : ℤ} (hD : ¬ IsSquare D) {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (K : ℕ) (x : ℝ) (j : Fin K) (i : Fin m) :
    embedding D (rationalCentres D p q K j i) =
      (j : ℂ) * (2 * root D * (x : ℂ)) +
        approximationCentreError (2 * root D) x (p i) (q i) j := by
  rw [embedding_rationalCentres hD]
  simp only [approximationCentreError, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_intCast, Complex.ofReal_natCast]
  ring

theorem approximationCentreError_bound {x ν : ℝ} {p : ℤ} {q j K : ℕ}
    (γ : ℂ) (hq : 0 < q) (hj : j ≤ K) (hν : 0 ≤ ν)
    (herr : |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) :
    ‖approximationCentreError γ x p q j‖ ≤
      (K : ℝ) * ‖γ‖ * Real.exp ν * Real.exp (-ν * (⌈Real.log (q : ℝ)⌉ : ℤ)) :=
  centre_error_le_exp_weight γ hq hj hν herr

theorem approximationCentreError_neg (γ : ℂ) (x : ℝ) (p : ℤ) (q j : ℕ) :
    approximationCentreError (-γ) x p q j = -approximationCentreError γ x p q j := by
  unfold approximationCentreError
  ring

theorem conjugateEmbedding_rationalCentres_eq_translated {D : ℤ} (hD : ¬ IsSquare D) {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (K : ℕ) (x : ℝ) (j : Fin K) (i : Fin m) :
    conjugateEmbedding D (rationalCentres D p q K j i) =
      (j : ℂ) * (-(2 * root D * (x : ℂ))) +
        approximationCentreError (-(2 * root D)) x (p i) (q i) j := by
  let : Fact (¬ IsSquare (D : ℚ)) := ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  let σ : Algebra D →+* ℂ := (embedding D).toRingHom.comp (starRingEnd (Algebra D))
  change σ ((j : Algebra D) * quadraticGenerator D * (p i : Algebra D) / (q i : Algebra D)) = _
  rw [map_div₀, map_mul, map_mul, map_natCast, map_intCast, map_natCast]
  change (j : ℂ) * conjugateEmbedding D (quadraticGenerator D) * (p i : ℂ) / (q i : ℂ) = _
  rw [conjugateEmbedding_quadraticGenerator]
  simp only [approximationCentreError, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_intCast, Complex.ofReal_natCast]
  ring

end QuadraticField
