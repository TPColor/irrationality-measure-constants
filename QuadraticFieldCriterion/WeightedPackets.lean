import QuadraticFieldCriterion.WeightedIndices
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Tactic.Linarith

/-! # Rationally weighted coefficient packets

Substitution by series whose coefficients have at least the weights of the
original variables preserves the kernel of every finite coefficient packet.
This is the filtration needed for the logarithm truncation change of variables.
-/

namespace ImaginaryQuadratic

def VanishesBelow {σ : Type*} [Fintype σ] (v : σ → ℚ) (H : ℚ)
    (f : MvPowerSeries σ ℂ) : Prop :=
  ∀ α, weightedDegree v α < H → MvPowerSeries.coeff α f = 0

theorem weightedDegree_add {σ : Type*} [Fintype σ] (v : σ → ℚ)
    (α β : σ →₀ ℕ) :
    weightedDegree v (α + β) = weightedDegree v α + weightedDegree v β := by
  simp [weightedDegree, mul_add, Finset.sum_add_distrib]

theorem weightedDegree_nonneg {σ : Type*} [Fintype σ] (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (α : σ →₀ ℕ) : 0 ≤ weightedDegree v α :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (Nat.cast_nonneg _))

theorem VanishesBelow.mono {σ : Type*} [Fintype σ]
    {v : σ → ℚ} {H J : ℚ} {f : MvPowerSeries σ ℂ}
    (hf : VanishesBelow v H f) (hJ : J ≤ H) : VanishesBelow v J f :=
  fun α hα => hf α (hα.trans_le hJ)

theorem VanishesBelow.zero {σ : Type*} [Fintype σ] (v : σ → ℚ) (H : ℚ) :
    VanishesBelow v H (0 : MvPowerSeries σ ℂ) := by
  intro α hα
  simp

theorem VanishesBelow.add {σ : Type*} [Fintype σ]
    {v : σ → ℚ} {H : ℚ} {f g : MvPowerSeries σ ℂ}
    (hf : VanishesBelow v H f) (hg : VanishesBelow v H g) :
    VanishesBelow v H (f + g) := by
  intro α hα
  simp [hf α hα, hg α hα]

theorem VanishesBelow.sub {σ : Type*} [Fintype σ]
    {v : σ → ℚ} {H : ℚ} {f g : MvPowerSeries σ ℂ}
    (hf : VanishesBelow v H f) (hg : VanishesBelow v H g) :
    VanishesBelow v H (f - g) := by
  intro α hα
  simp [hf α hα, hg α hα]

theorem VanishesBelow.mul {σ : Type*} [Fintype σ]
    {v : σ → ℚ} {H J : ℚ} {f g : MvPowerSeries σ ℂ}
    (hf : VanishesBelow v H f) (hg : VanishesBelow v J g) :
    VanishesBelow v (H + J) (f * g) := by
  classical
  intro α hα
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro β hβ
  have hsum : β.1 + β.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.mp hβ
  have hw : weightedDegree v β.1 + weightedDegree v β.2 < H + J := by
    rw [← weightedDegree_add, hsum]
    exact hα
  by_cases hleft : weightedDegree v β.1 < H
  · rw [hf β.1 hleft, zero_mul]
  · rw [hg β.2 (by linarith [le_of_not_gt hleft]), mul_zero]

theorem VanishesBelow.one {σ : Type*} [Fintype σ] (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) : VanishesBelow v 0 (1 : MvPowerSeries σ ℂ) := by
  intro α hα
  exact False.elim (not_lt_of_ge (weightedDegree_nonneg v hv α) hα)

theorem VanishesBelow.pow {σ : Type*} [Fintype σ]
    {v : σ → ℚ} (hv : ∀ i, 0 ≤ v i) {H : ℚ} {f : MvPowerSeries σ ℂ}
    (hf : VanishesBelow v H f) (n : ℕ) : VanishesBelow v ((n : ℚ) * H) (f ^ n) := by
  induction n with
  | zero => simpa using VanishesBelow.one v hv
  | succ n ih => simpa [pow_succ, Nat.cast_add, add_mul] using ih.mul hf

theorem VanishesBelow.prod {σ ι : Type*} [Fintype σ]
    {v : σ → ℚ} (hv : ∀ i, 0 ≤ v i) (s : Finset ι)
    (H : ι → ℚ) (f : ι → MvPowerSeries σ ℂ)
    (hf : ∀ i ∈ s, VanishesBelow v (H i) (f i)) :
    VanishesBelow v (∑ i ∈ s, H i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using VanishesBelow.one v hv
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A filtered substitution preserves all coefficients that are zero below `H`.
Rational weights are handled directly, without rounding or a uniform order cutoff. -/
theorem VanishesBelow.subst {σ : Type*} [Fintype σ]
    {v : σ → ℚ} (hv : ∀ i, 0 ≤ v i) {H : ℚ}
    {f : MvPowerSeries σ ℂ} (hf : VanishesBelow v H f)
    {a : σ → MvPowerSeries σ ℂ} (ha : MvPowerSeries.HasSubst a)
    (hweight : ∀ i, VanishesBelow v (v i) (a i)) :
    VanishesBelow v H (MvPowerSeries.subst a f) := by
  classical
  intro α hα
  rw [MvPowerSeries.coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro β
  by_cases hβ : weightedDegree v β < H
  · rw [hf β hβ, zero_smul]
  · have hp := VanishesBelow.prod hv β.support
      (fun i => (β i : ℚ) * v i) (fun i => a i ^ β i)
      (fun i _ => (hweight i).pow hv (β i))
    have hsum : (∑ i ∈ β.support, (β i : ℚ) * v i) = weightedDegree v β := by
      rw [weightedDegree]
      rw [← Finset.sum_subset (Finset.subset_univ β.support)]
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · intro i hi hnot
        simp [Finsupp.notMem_support_iff.mp hnot]
    rw [hsum] at hp
    have hc := hp α (hα.trans_le (le_of_not_gt hβ))
    change _ • MvPowerSeries.coeff α (∏ i ∈ β.support, a i ^ β i) = 0
    rw [hc, smul_zero]

/-- Packet equality is preserved by every filtered substitution. -/
theorem packet_equality_subst {σ : Type*} [Fintype σ]
    {v : σ → ℚ} (hv : ∀ i, 0 ≤ v i) {H : ℚ}
    {f g : MvPowerSeries σ ℂ}
    (hfg : ∀ α, weightedDegree v α < H →
      MvPowerSeries.coeff α f = MvPowerSeries.coeff α g)
    {a : σ → MvPowerSeries σ ℂ} (ha : MvPowerSeries.HasSubst a)
    (hweight : ∀ i, VanishesBelow v (v i) (a i)) :
    ∀ α, weightedDegree v α < H →
      MvPowerSeries.coeff α (MvPowerSeries.subst a f) =
        MvPowerSeries.coeff α (MvPowerSeries.subst a g) := by
  have hvan : VanishesBelow v H (f - g) := by
    intro α hα
    simp [hfg α hα]
  have hout := hvan.subst hv ha hweight
  intro α hα
  have h := hout α hα
  rw [MvPowerSeries.subst_sub ha, map_sub, sub_eq_zero] at h
  exact h

/-- A substitution fixes every series supported on variables it fixes. -/
theorem subst_eq_of_fixed_support {σ : Type*} [Fintype σ]
    {a : σ → MvPowerSeries σ ℂ} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries σ ℂ)
    (hfix : ∀ α, MvPowerSeries.coeff α f ≠ 0 →
      ∀ i ∈ α.support, a i = MvPowerSeries.X i) :
    MvPowerSeries.subst a f = f := by
  classical
  have hself : MvPowerSeries.subst MvPowerSeries.X f = f :=
    congrFun (MvPowerSeries.subst_self (R := ℂ)) f
  conv_rhs => rw [← hself]
  ext β
  rw [MvPowerSeries.coeff_subst ha, MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.X]
  apply finsum_congr
  intro α
  by_cases hα : MvPowerSeries.coeff α f = 0
  · simp [hα]
  · congr 2
    change (∏ i ∈ α.support, a i ^ α i) =
      ∏ i ∈ α.support, MvPowerSeries.X i ^ α i
    exact Finset.prod_congr rfl (fun i hi => by rw [hfix α hα i hi])

/-- Substitution of formal variables commutes with polynomial evaluation. -/
theorem subst_eval₂ {σ τ : Type*} [Fintype σ]
    {a : σ → MvPowerSeries σ ℂ} (ha : MvPowerSeries.HasSubst a)
    (z : τ → MvPowerSeries σ ℂ) (P : MvPolynomial τ ℂ) :
    MvPowerSeries.subst a (MvPolynomial.eval₂ MvPowerSeries.C z P) =
      MvPolynomial.eval₂ MvPowerSeries.C (fun i => MvPowerSeries.subst a (z i)) P := by
  rw [← MvPowerSeries.substAlgHom_apply ha]
  change (MvPowerSeries.substAlgHom ha).toRingHom
    (MvPolynomial.eval₂ MvPowerSeries.C z P) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · apply RingHom.ext
    intro c
    change MvPowerSeries.substAlgHom ha (MvPowerSeries.C c) = MvPowerSeries.C c
    rw [MvPowerSeries.substAlgHom_apply]
    exact MvPowerSeries.subst_C c
  · funext i
    exact MvPowerSeries.substAlgHom_apply ha (z i)

/-- Surjectivity on a finite packet survives an invertible filtered change
of formal variables. The permitted polynomial support is unchanged. -/
theorem packet_surjectivity_change {σ τ : Type*} [Fintype σ]
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (S : Finset (τ →₀ ℕ)) (z : τ → MvPowerSeries σ ℂ)
    {a b : σ → MvPowerSeries σ ℂ} (ha : MvPowerSeries.HasSubst a)
    (hweight : ∀ i, VanishesBelow v (v i) (a i))
    (hinv : ∀ f : MvPowerSeries σ ℂ,
      MvPowerSeries.subst a (MvPowerSeries.subst b f) = f)
    (honto : ∀ target : MvPowerSeries σ ℂ, ∃ P : MvPolynomial τ ℂ,
      P.support ⊆ S ∧ ∀ α, weightedDegree v α < H →
        MvPowerSeries.coeff α (MvPolynomial.eval₂ MvPowerSeries.C z P) =
          MvPowerSeries.coeff α target) :
    ∀ target : MvPowerSeries σ ℂ, ∃ P : MvPolynomial τ ℂ,
      P.support ⊆ S ∧ ∀ α, weightedDegree v α < H →
        MvPowerSeries.coeff α
          (MvPolynomial.eval₂ MvPowerSeries.C
            (fun i => MvPowerSeries.subst a (z i)) P) =
          MvPowerSeries.coeff α target := by
  intro target
  obtain ⟨P, hP, hcoeff⟩ := honto (MvPowerSeries.subst b target)
  refine ⟨P, hP, ?_⟩
  have h := packet_equality_subst hv hcoeff ha hweight
  rw [subst_eval₂ ha z P, hinv target] at h
  exact h

/-- The same change of variables works simultaneously at every centre. -/
theorem multicentre_packet_surjectivity_change {σ τ ι : Type*} [Fintype σ]
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (S : Finset (τ →₀ ℕ)) (z : ι → τ → MvPowerSeries σ ℂ)
    {a b : σ → MvPowerSeries σ ℂ} (ha : MvPowerSeries.HasSubst a)
    (hweight : ∀ i, VanishesBelow v (v i) (a i))
    (hinv : ∀ f : MvPowerSeries σ ℂ,
      MvPowerSeries.subst a (MvPowerSeries.subst b f) = f)
    (honto : ∀ target : ι → MvPowerSeries σ ℂ, ∃ P : MvPolynomial τ ℂ,
      P.support ⊆ S ∧ ∀ j α, weightedDegree v α < H →
        MvPowerSeries.coeff α (MvPolynomial.eval₂ MvPowerSeries.C (z j) P) =
          MvPowerSeries.coeff α (target j)) :
    ∀ target : ι → MvPowerSeries σ ℂ, ∃ P : MvPolynomial τ ℂ,
      P.support ⊆ S ∧ ∀ j α, weightedDegree v α < H →
        MvPowerSeries.coeff α
          (MvPolynomial.eval₂ MvPowerSeries.C
            (fun i => MvPowerSeries.subst a (z j i)) P) =
          MvPowerSeries.coeff α (target j) := by
  intro target
  obtain ⟨P, hP, hcoeff⟩ := honto (fun j => MvPowerSeries.subst b (target j))
  refine ⟨P, hP, ?_⟩
  intro j
  have h := packet_equality_subst hv (hcoeff j) ha hweight
  rw [subst_eval₂ ha (z j) P, hinv (target j)] at h
  exact h

end ImaginaryQuadratic
