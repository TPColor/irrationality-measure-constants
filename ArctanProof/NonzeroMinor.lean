import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Basic.Complex.Basic

/-! # Selecting a nonzero square minor

The rectangular determinant expansion below is the form needed to pass from
surjectivity of the interpolation matrix to a minor containing every row.
-/

namespace ImaginaryQuadratic

theorem det_rectangular_mul {ι κ R : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [CommRing R]
    (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).det = ∑ f : ι → κ,
      (∏ i : ι, B (f i) i) * (A.submatrix id f).det := by
  classical
  calc
    (A * B).det = ∑ f : ι → κ, ∑ σ : Equiv.Perm ι,
        (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq]
      ring

theorem exists_nonzero_minor_of_right_inverse {ι κ R : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [CommRing R] [Nontrivial R]
    (A : Matrix ι κ R) (B : Matrix κ ι R) (hAB : A * B = 1) :
    ∃ f : ι → κ, (A.submatrix id f).det ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hd := det_rectangular_mul A B
  simp [hAB, h] at hd

/-- Surjectivity on the row coefficient space supplies a minor with every row. -/
theorem exists_nonzero_minor_of_surjective {ι κ R : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [CommRing R] [Nontrivial R]
    (A : Matrix ι κ R) (hA : Function.Surjective A.mulVec) :
    ∃ f : ι → κ, (A.submatrix id f).det ≠ 0 := by
  classical
  choose v hv using fun j : ι => hA (fun i => if i = j then 1 else 0)
  let B : Matrix κ ι R := fun k j => v j k
  have hAB : A * B = 1 := by
    ext i j
    have h := congrFun (hv j) i
    change (∑ k, A i k * v j k) = if i = j then 1 else 0
    simpa only [Matrix.mulVec, dotProduct] using h
  exact exists_nonzero_minor_of_right_inverse A B hAB

/-- The finite monomial matrix of a surjective polynomial interpolation map
has a nonzero square minor. No arbitrary preimage coefficients occur in that
minor: its columns are individual monomials with coefficient one. -/
theorem exists_nonzero_monomial_minor {σ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S : Finset (σ →₀ ℕ))
    (L : MvPolynomial σ ℂ →ₗ[ℂ] (ι → ℂ))
    (hL : ∀ target : ι → ℂ, ∃ P : MvPolynomial σ ℂ,
      P.support ⊆ S ∧ L P = target) :
    ∃ f : ι → {α // α ∈ S},
      (Matrix.of (fun i j => L (MvPolynomial.monomial (f j).val 1) i)).det ≠ 0 := by
  classical
  let A : Matrix ι {α // α ∈ S} ℂ :=
    fun i α => L (MvPolynomial.monomial α.val 1) i
  have hA : Function.Surjective A.mulVec := by
    intro target
    obtain ⟨P, hsupport, hP⟩ := hL target
    refine ⟨fun α => P.coeff α.val, ?_⟩
    have hexpand : (∑ α ∈ S, MvPolynomial.monomial α (P.coeff α)) = P := by
      calc
        _ = ∑ α ∈ P.support, MvPolynomial.monomial α (P.coeff α) := by
          apply (Finset.sum_subset hsupport ?_).symm
          intro α hα hnot
          rw [MvPolynomial.notMem_support_iff.mp hnot, MvPolynomial.monomial_zero]
        _ = P := MvPolynomial.support_sum_monomial_coeff P
    have hlinear : ∀ i, L P i =
        ∑ α ∈ S, P.coeff α * L (MvPolynomial.monomial α 1) i := by
      intro i
      conv_lhs => rw [← hexpand, map_sum]
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro α hα
      have hm : MvPolynomial.monomial α (P.coeff α) =
          P.coeff α • MvPolynomial.monomial α 1 := by
        simp [MvPolynomial.smul_monomial]
      rw [hm, map_smul]
      rfl
    ext i
    rw [← hP, hlinear]
    change (∑ α : {α // α ∈ S},
      L (MvPolynomial.monomial α.val 1) i * P.coeff α.val) = _
    calc
      _ = ∑ α : {α // α ∈ S},
          P.coeff α.val * L (MvPolynomial.monomial α.val 1) i := by
        apply Finset.sum_congr rfl
        intro α hα
        exact mul_comm _ _
      _ = _ := Finset.sum_coe_sort S
        (fun α => P.coeff α * L (MvPolynomial.monomial α 1) i)
  obtain ⟨f, hf⟩ := exists_nonzero_minor_of_surjective A hA
  exact ⟨f, hf⟩

end ImaginaryQuadratic
