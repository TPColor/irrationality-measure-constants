import LogIrrationalityMeasure.Approximation.WeightSeparation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogExponent LogExponentApprox
open scoped BigOperators

noncomputable section

def weightSequence {m : ℕ} (w : Fin m → ℚ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else if h : n - 1 < m then (w ⟨n - 1, h⟩ : ℝ) else 1

@[simp] theorem weightSequence_zero {m : ℕ} (w : Fin m → ℚ) : weightSequence w 0 = 1 := by
  simp [weightSequence]

@[simp] theorem weightSequence_succ {m : ℕ} (w : Fin m → ℚ) (i : Fin m) :
    weightSequence w (i.val + 1) = (w i : ℝ) := by
  simp [weightSequence, i.isLt]

theorem weightSequence_prefix {m : ℕ} (w : Fin m → ℚ) (i : ℕ) (hi : i ≤ m) :
    (∏ j ∈ Finset.range (i + 1), weightSequence w j) =
      ((((List.ofFn w).take i).prod : ℚ) : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have him : i < m := by omega
    rw [Finset.prod_range_succ, ih (by omega),
      List.prod_take_succ _ i (by simpa using him)]
    simp only [Rat.cast_mul, List.getElem_ofFn]
    rw [show weightSequence w (i + 1) = (w ⟨i, him⟩ : ℝ) by
      exact weightSequence_succ w ⟨i, him⟩]

/-- Successive thresholds depend on the preceding weights only. -/
theorem exists_thresholds (m : ℕ) (w0 v0 θ : ℚ) (C : ℝ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ) (hC : 0 < C) :
    ∃ thresholds : Fin m → List ℚ → ℚ,
      ∀ w : Fin m → ℚ,
        (∀ i, 0 < w i) →
        (∀ i, thresholds i ((List.ofFn w).take i.val) < w i) →
        ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
          ∀ i, i ≠ 0 → i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
          C *
              (∏ j ∈ B, ((Fin.cases v0 (fun i => w i / θ) j : ℚ) : ℝ)) <
            ∏ j ∈ A, ((Fin.cases w0 w j : ℚ) : ℝ) := by
  classical
  let D : ℝ := weightSeparationFactor m C w0 v0 θ
  have hD : 0 < D := weightSeparationFactor_pos m C w0 v0 θ hC
  obtain ⟨d, hd⟩ := exists_rat_gt D
  refine ⟨fun _ history => max 1 (d * history.prod), ?_⟩
  intro w hw hgrowth A B hcard i hi hiA hiB hhigh
  have hw1 (i : Fin m) : (1 : ℚ) < w i :=
    lt_of_le_of_lt (le_max_left _ _) (hgrowth i)
  have hx : ∀ n, 1 ≤ weightSequence w n := by
    intro n
    unfold weightSequence
    split_ifs
    · exact le_rfl
    · exact_mod_cast (hw1 _).le
    · exact le_rfl
  have hg : SeparatedWeightGrowth m D (weightSequence w) := by
    intro n hn hnm
    have hindex : n - 1 < m := by omega
    let j : Fin m := ⟨n - 1, hindex⟩
    have hj : j.val + 1 = n := by dsimp [j]; omega
    have hprefix := weightSequence_prefix w j.val (Nat.le_of_lt j.isLt)
    have hprod : 0 < (((List.ofFn w).take j.val).prod : ℚ) :=
      List.prod_pos (fun r hr => by
        have hr' := List.mem_of_mem_take hr
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr'
        exact hw k)
    have hlt : d * ((List.ofFn w).take j.val).prod < w j :=
      lt_of_le_of_lt (le_max_right _ _) (hgrowth j)
    rw [← hj, hprefix, weightSequence_succ]
    have hltR : (d : ℝ) * ((((List.ofFn w).take j.val).prod : ℚ) : ℝ) < w j := by
      exact_mod_cast hlt
    exact lt_trans (mul_lt_mul_of_pos_right hd (by exact_mod_cast hprod)) hltR
  let e : Fin (m + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hbound (S : Finset (Fin (m + 1))) : S.map e ⊆ Finset.range (m + 1) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨k, hkB, rfl⟩ := Finset.mem_map.mp hjB
    by_contra hnot
    have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
    have hne : i ≠ k := fun h => hiB (h.symm ▸ hkB)
    have hkA := (hhigh k (lt_of_le_of_ne hik hne)).mpr hkB
    exact hjA (Finset.mem_map.mpr ⟨k, hkA, rfl⟩)
  have hn : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have h := geometric_weight_products_separated m C w0 v0 θ (weightSequence w)
    hC (by exact_mod_cast hw0) (by exact_mod_cast hv0) (by exact_mod_cast hθ)
    (weightSequence_zero w) hx hg (A.map e) (B.map e)
    (by simpa using hcard) (hbound A) (hbound B) i.val hn
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩)
    (by
      intro hmem
      obtain ⟨a, haB, hai⟩ := Finset.mem_map.mp hmem
      have hai' : a = i := Fin.ext hai
      exact hiB (hai' ▸ haB)) hbelow
  have hdeg (j : Fin (m + 1)) :
      geometricDegreeWeight w0 (weightSequence w) j.val = ((Fin.cases w0 w j : ℚ) : ℝ) := by
    cases j using Fin.cases <;> simp [geometricDegreeWeight]
  have hjet (j : Fin (m + 1)) :
      geometricJetWeight v0 θ (weightSequence w) j.val =
        ((Fin.cases v0 (fun i => w i / θ) j : ℚ) : ℝ) := by
    cases j using Fin.cases <;> simp [geometricJetWeight]
  simpa only [Finset.prod_map, e, Function.Embedding.coeFn_mk, hdeg, hjet] using h

end
end LiuJiangZhang.RepeatedFibres
