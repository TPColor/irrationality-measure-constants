import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # The combinatorial saving from repeated Taylor indices

A nonzero coefficient determinant has distinct Taylor degrees within each
transverse-index group. Distinct nonnegative integers have sum at least
`n(n-1)/2`; summing this fact over the groups gives the quadratic saving.
-/

namespace QuadraticField

theorem twice_sum_degrees_ge_card (s : Finset ℕ) :
    (s.card : ℝ) * (s.card - 1) ≤ 2 * ∑ k ∈ s, (k : ℝ) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | @insert a s ha ih =>
    have hnot : a ∉ s := fun h => (ha a h).false
    have hcard : s.card ≤ a := by
      calc
        s.card ≤ (Finset.range a).card :=
          Finset.card_le_card (fun k hk => Finset.mem_range.mpr (ha k hk))
        _ = a := Finset.card_range a
    have hcardR : (s.card : ℝ) ≤ a := by exact_mod_cast hcard
    simp only [Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot,
      Nat.cast_add, Nat.cast_one]
    nlinarith

theorem twice_sum_degrees_of_injOn {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (hd : Set.InjOn d s) :
    (s.card : ℝ) * (s.card - 1) ≤ 2 * ∑ i ∈ s, (d i : ℝ) := by
  classical
  have h := twice_sum_degrees_ge_card (s.image d)
  rw [Finset.card_image_of_injOn hd, Finset.sum_image hd] at h
  exact h

/-- Equal transverse indices and equal Taylor degrees give identical
coefficient rows. Such a choice contributes zero to the determinant. -/
theorem coefficient_det_eq_zero_of_repeated_pair {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ) (d : ι → ℕ)
    (coeff : κ → ℕ → ι → ℂ) {i j : ι} (hij : i ≠ j)
    (ha : a i = a j) (hd : d i = d j) :
    (Matrix.of (fun r c => coeff (a r) (d r) c)).det = 0 := by
  apply Matrix.det_zero_of_row_eq hij
  funext c
  simp [ha, hd]

/-- Consequently, Taylor degrees are injective inside every group in a
nonzero determinant term. -/
theorem degrees_injective_on_fibre {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → κ) (d : ι → ℕ)
    (coeff : κ → ℕ → ι → ℂ)
    (hne : (Matrix.of (fun r c => coeff (a r) (d r) c)).det ≠ 0) (k : κ) :
    Set.InjOn d {i | a i = k} := by
  intro i hi j hj hd
  by_contra hij
  exact hne (coefficient_det_eq_zero_of_repeated_pair a d coeff hij (hi.trans hj.symm) hd)

/-- The total Taylor degree is at least the sum of the triangular costs
inside the transverse-index groups. -/
theorem twice_sum_degrees_ge_fibre_squares {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (a : ι → κ) (d : ι → ℕ)
    (hinj : ∀ k, Set.InjOn d {i | a i = k}) :
    (∑ k ∈ Finset.univ.image a,
      (((Finset.univ.filter (fun i => a i = k)).card : ℝ) ^ 2)) - Fintype.card ι ≤
      2 * ∑ i, (d i : ℝ) := by
  classical
  let s := Finset.univ.image a
  let n : κ → ℕ := fun k => (Finset.univ.filter (fun i => a i = k)).card
  have hgroup : ∀ k ∈ s, (n k : ℝ) * (n k - 1) ≤
      2 * ∑ i ∈ Finset.univ.filter (fun i => a i = k), (d i : ℝ) := by
    intro k hk
    apply twice_sum_degrees_of_injOn
    intro i hi j hj hd
    exact hinj k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hd
  have hsum := Finset.sum_le_sum hgroup
  have hcount : ∑ k ∈ s, (n k : ℝ) = Fintype.card ι := by
    have h := Finset.card_eq_sum_card_image a (Finset.univ : Finset ι)
    exact_mod_cast h.symm
  have hdegrees : (∑ k ∈ s, ∑ i ∈ Finset.univ.filter (fun i => a i = k),
      (d i : ℝ)) = ∑ i, (d i : ℝ) := by
    exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem a hi) _
  simp only [← Finset.mul_sum] at hsum
  rw [hdegrees] at hsum
  have halgebra : (∑ k ∈ s, (n k : ℝ) * (n k - 1)) =
      (∑ k ∈ s, (n k : ℝ) ^ 2) - Fintype.card ι := by
    simp_rw [mul_sub, mul_one, ← pow_two]
    rw [Finset.sum_sub_distrib, hcount]
  rw [halgebra] at hsum
  exact hsum

end QuadraticField
