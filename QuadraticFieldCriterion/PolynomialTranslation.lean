import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Nat.Choose.Sum

/-! # Coefficients of translated transverse monomials -/

namespace QuadraticField

open MvPolynomial

theorem shifted_monomial_expansion {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (l : σ → ℕ) (c : σ → R) :
    (∏ i, (X i + C (c i)) ^ l i : MvPolynomial σ R) =
      ∑ a : ∀ i, Fin (l i + 1), monomial (Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)))
        (∏ i, ((l i).choose (a i : ℕ) : R) * c i ^ (l i - (a i : ℕ))) := by
  classical
  have hbinom : (∏ i, (X i + C (c i)) ^ l i : MvPolynomial σ R) =
      ∏ i, ∑ a : Fin (l i + 1), X i ^ (a : ℕ) * C (c i) ^ (l i - (a : ℕ)) *
        ((l i).choose (a : ℕ) : MvPolynomial σ R) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [add_pow]
    exact (Fin.sum_univ_eq_sum_range (fun a => X i ^ a * C (c i) ^ (l i - a) *
      ((l i).choose a : MvPolynomial σ R)) (l i + 1)).symm
  rw [hbinom, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  change _ = C (∏ i, ((l i).choose (a i : ℕ) : R) * c i ^ (l i - (a i : ℕ))) *
    ∏ i, X i ^ (a i : ℕ)
  simp only [map_prod, map_mul, map_pow, map_natCast,
    Finset.prod_mul_distrib]
  ring

theorem coeff_shifted_monomial {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (l : σ → ℕ) (c : σ → R) (β : σ →₀ ℕ) :
    (∏ i, (X i + C (c i)) ^ l i : MvPolynomial σ R).coeff β =
      if ∀ i, β i ≤ l i then ∏ i, ((l i).choose (β i) : R) * c i ^ (l i - β i) else 0 := by
  classical
  rw [shifted_monomial_expansion, coeff_sum]
  simp only [coeff_monomial]
  by_cases hβ : ∀ i, β i ≤ l i
  · rw [ite_eq_left hβ]
    let aβ : ∀ i, Fin (l i + 1) := fun i => ⟨β i, Nat.lt_succ_of_le (hβ i)⟩
    rw [Finset.sum_eq_single aβ]
    · have h : Finsupp.equivFunOnFinite.symm (fun i => (aβ i : ℕ)) = β := by ext i; rfl
      simp only [h, ite_true]
      rfl
    · intro a ha hne
      apply ite_eq_right
      intro h
      apply hne
      funext i
      apply Fin.ext
      exact congrArg (fun x : σ →₀ ℕ => x i) h
    · simp
  · rw [ite_eq_right hβ]
    apply Finset.sum_eq_zero
    intro a ha
    apply ite_eq_right
    intro h
    apply hβ
    intro i
    have hi := congrArg (fun x : σ →₀ ℕ => x i) h
    exact hi ▸ Nat.le_of_lt_succ (a i).isLt

theorem translated_product_expansion {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (B z : R) (l : σ → ℕ) (d : σ → R) :
    (C B * ∏ i, (X i + C (z + d i)) ^ l i : MvPolynomial σ R) =
      ∑ a : ∀ i, Fin (l i + 1),
        C (B * (∏ i, ((l i).choose (a i : ℕ) : R)) * z ^ (∑ i : σ, (l i - (a i : ℕ)))) *
          ∏ i, (X i + C (d i)) ^ (a i : ℕ) := by
  classical
  let φ : MvPolynomial σ R →+* MvPolynomial σ R :=
    eval₂Hom C (fun i => X i + C (d i))
  have h := congrArg φ (shifted_monomial_expansion l (fun _ => z))
  simp only [φ, map_prod, map_pow, map_add, eval₂Hom_X', eval₂Hom_C, map_sum,
    eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)] at h
  have hl : (∏ i, (X i + C (z + d i)) ^ l i : MvPolynomial σ R) =
      ∏ i, (X i + C (d i) + C z) ^ l i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [map_add]
    congr 1
    ring
  rw [hl, h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change C B * ((∏ i, C (((l i).choose (a i : ℕ) : R) * z ^ (l i - (a i : ℕ)))) *
    ∏ i, (X i + C (d i)) ^ (a i : ℕ)) = _
  simp only [map_mul, map_pow, map_prod, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

theorem coeff_translated_product {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (B z : R) (l : σ → ℕ) (d : σ → R) (β : σ →₀ ℕ) :
    (C B * ∏ i, (X i + C (z + d i)) ^ l i : MvPolynomial σ R).coeff β =
      ∑ a : ∀ i, Fin (l i + 1),
        (B * (∏ i, ((l i).choose (a i : ℕ) : R)) * z ^ (∑ i : σ, (l i - (a i : ℕ)))) *
          (if ∀ i, β i ≤ (a i : ℕ) then
            ∏ i, ((a i : ℕ).choose (β i) : R) * d i ^ ((a i : ℕ) - β i) else 0) := by
  rw [translated_product_expansion, coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [coeff_C_mul, coeff_shifted_monomial]

end QuadraticField
