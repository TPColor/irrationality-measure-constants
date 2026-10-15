import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Extending finite coordinate boxes by zero -/

namespace QuadraticField

theorem sum_fin_pi_eq_box {σ R : Type*} [Fintype σ] [DecidableEq σ] [AddCommMonoid R]
    (l : σ → ℕ) (f : (σ → ℕ) → R) :
    (∑ a : ∀ i, Fin (l i + 1), f (fun i => (a i : ℕ))) =
      ∑ a ∈ Fintype.piFinset (fun i => Finset.range (l i + 1)), f a := by
  classical
  apply Finset.sum_bij (fun a _ => fun i => (a i : ℕ))
  · intro a ha
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (a i).isLt)
  · intro a ha b hb hab
    funext i
    exact Fin.ext (congrFun hab i)
  · intro b hb
    let a : ∀ i, Fin (l i + 1) := fun i =>
      ⟨b i, Finset.mem_range.mp (Fintype.mem_piFinset.mp hb i)⟩
    exact ⟨a, Finset.mem_univ _, rfl⟩
  · intro a ha
    rfl

theorem sum_fin_pi_extend {σ R : Type*} [Fintype σ] [DecidableEq σ] [AddCommMonoid R]
    (l N : σ → ℕ) (hle : ∀ i, l i ≤ N i) (f : (σ → ℕ) → R)
    (hzero : ∀ a, ¬ (∀ i, a i ≤ l i) → f a = 0) :
    (∑ a : ∀ i, Fin (l i + 1), f (fun i => (a i : ℕ))) =
      ∑ a : ∀ i, Fin (N i + 1), f (fun i => (a i : ℕ)) := by
  classical
  rw [sum_fin_pi_eq_box, sum_fin_pi_eq_box]
  apply Finset.sum_subset
  · intro a ha
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_range.mpr ((Finset.mem_range.mp (Fintype.mem_piFinset.mp ha i)).trans_le
      (Nat.add_le_add_right (hle i) 1))
  · intro a ha hnot
    apply hzero
    intro h
    apply hnot
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (Nat.lt_succ_of_le (h i)))

end QuadraticField
