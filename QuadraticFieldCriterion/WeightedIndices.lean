import ExternalResults.LiuJiangZhangTheorem9
import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity

namespace ImaginaryQuadratic

/-- Weighted degree of a monomial, with rational weights. -/
def weightedDegree {σ : Type*} [Fintype σ] (w : σ → ℚ) (α : σ →₀ ℕ) : ℚ :=
  ∑ i : σ, w i * (α i : ℚ)

theorem coordinate_le_weightedDegree {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 ≤ w i) (α : σ →₀ ℕ) (i : σ) :
    w i * (α i : ℚ) ≤ weightedDegree w α := by
  classical
  exact Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (Nat.cast_nonneg _))
    (Finset.mem_univ i)

/-- The finite-degree source and retained coefficient packets are finite sets. -/
theorem finite_weightedDegree_le {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (H : ℚ) :
    Set.Finite {α : σ →₀ ℕ | weightedDegree w α ≤ H} := by
  classical
  let cap : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => ⌊H / w i⌋₊)
  refine (Set.finite_Icc (0 : σ →₀ ℕ) cap).subset ?_
  intro α hα
  refine ⟨by exact fun i => Nat.zero_le _, ?_⟩
  intro i
  change α i ≤ ⌊H / w i⌋₊
  apply Nat.le_floor
  apply (le_div_iff₀ (hw i)).mpr
  have h := (coordinate_le_weightedDegree w (fun j => (hw j).le) α i).trans hα
  simpa [mul_comm] using h

theorem finite_weightedDegree_lt {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (H : ℚ) :
    Set.Finite {α : σ →₀ ℕ | weightedDegree w α < H} :=
  (finite_weightedDegree_le w hw H).subset
    (fun α h => (show weightedDegree w α < H from h).le)

/-- The explicit finite box used for monomial and row indexing. -/
noncomputable def weightBox {σ : Type*} [Fintype σ] (w : σ → ℚ) (H : ℚ) :
    Finset (σ →₀ ℕ) := by
  classical
  exact Finset.Icc 0 (Finsupp.equivFunOnFinite.symm (fun i => ⌊H / w i⌋₊))

theorem mem_weightBox_of_weight_le {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) {H : ℚ} {α : σ →₀ ℕ}
    (hα : weightedDegree w α ≤ H) : α ∈ weightBox w H := by
  classical
  apply Finset.mem_Icc.mpr
  refine ⟨by exact fun i => Nat.zero_le _, ?_⟩
  intro i
  change α i ≤ ⌊H / w i⌋₊
  apply Nat.le_floor
  apply (le_div_iff₀ (hw i)).mpr
  have h := (coordinate_le_weightedDegree w (fun j => (hw j).le) α i).trans hα
  simpa [mul_comm] using h

noncomputable def monomialIndices {σ : Type*} [Fintype σ] (w : σ → ℚ) (H : ℚ) :
    Finset (σ →₀ ℕ) := by
  classical
  exact (weightBox w H).filter (fun α => weightedDegree w α ≤ H)

theorem mem_monomialIndices_iff {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (H : ℚ) (α : σ →₀ ℕ) :
    α ∈ monomialIndices w H ↔ weightedDegree w α ≤ H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_weightBox_of_weight_le w hw h, h⟩

noncomputable def jetIndices {σ : Type*} [Fintype σ] (K : ℕ)
    (v : σ → ℚ) (H : ℚ) : Finset (Fin K × (σ →₀ ℕ)) := by
  classical
  exact (Finset.univ ×ˢ weightBox v H).filter
    (fun ρ => weightedDegree v ρ.2 < H)

theorem mem_jetIndices_iff {σ : Type*} [Fintype σ]
    (K : ℕ) (v : σ → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (ρ : Fin K × (σ →₀ ℕ)) :
    ρ ∈ jetIndices K v H ↔ weightedDegree v ρ.2 < H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_univ _, mem_weightBox_of_weight_le v hv h.le⟩, h⟩

end ImaginaryQuadratic
