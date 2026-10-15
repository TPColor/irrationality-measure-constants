import QuadraticFieldCriterion.WeightedIndices
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Choose

/-! # Counting lattice points in a simplex -/

namespace QuadraticField

open Filter Topology Asymptotics

noncomputable def simplexIndices (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact (Finset.range (N + 1)).biUnion (fun n => (Finset.univ : Finset σ).finsuppAntidiag n)

theorem mem_simplexIndices_iff {σ : Type*} [Fintype σ] (N : ℕ) (α : σ →₀ ℕ) :
    α ∈ simplexIndices σ N ↔ (∑ i, α i) ≤ N := by
  classical
  simp only [simplexIndices, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  constructor
  · rintro ⟨n, hn, hα⟩
    exact hα.le.trans (Nat.le_of_lt_succ hn)
  · intro h
    exact ⟨∑ i, α i, by omega, rfl⟩

theorem card_simplexIndices (σ : Type*) [Fintype σ] (N : ℕ) :
    (simplexIndices σ N).card = (N + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  rw [simplexIndices, Finset.card_biUnion]
  · simp only [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ]
    exact Nat.sum_range_multichoose N (Fintype.card σ)
  · intro n hn k hk hnk
    apply Finset.disjoint_left.mpr
    intro α hαn hαk
    have hn' := (Finset.mem_finsuppAntidiag.mp hαn).1
    have hk' := (Finset.mem_finsuppAntidiag.mp hαk).1
    exact hnk (hn'.symm.trans hk')

/-- The binomial leading term along any degree sequence and normalization. -/
theorem choose_scaled_limit (k : ℕ) (n : ℕ → ℕ) (H : ℕ → ℝ) {r : ℝ}
    (hn : Tendsto n atTop atTop) (hr : Tendsto (fun j => (n j : ℝ) / H j) atTop (𝓝 r)) :
    Tendsto (fun j => ((n j).choose k : ℝ) / (H j) ^ k) atTop (𝓝 (r ^ k / k.factorial)) := by
  have heq : (fun j => ((n j).choose k : ℝ) / (H j) ^ k) ~[atTop]
      (fun j => ((n j : ℝ) / H j) ^ k / k.factorial) := by
    calc
      _ ~[atTop] (fun j => ((n j : ℝ) ^ k / k.factorial) / (H j) ^ k) :=
        ((isEquivalent_choose k).comp_tendsto hn).div IsEquivalent.refl
      _ ~[atTop] _ := EventuallyEq.isEquivalent (.of_eq (by
        funext j
        rw [div_pow]
        ring))
  exact (IsEquivalent.tendsto_nhds_iff heq).mpr ((hr.pow k).div_const _)

theorem simplex_count_leading_term (σ : Type*) [Fintype σ] :
    Tendsto (fun N : ℕ => ((simplexIndices σ N).card : ℝ) / (N : ℝ) ^ Fintype.card σ)
      atTop (𝓝 (1 / (Fintype.card σ).factorial : ℝ)) := by
  have hr : Tendsto (fun N : ℕ => ((N + Fintype.card σ : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_natCast_div_add_atTop (Fintype.card σ : ℝ)).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [inv_div, inv_one, Nat.cast_add] using h
  have h := choose_scaled_limit (Fintype.card σ) (fun N => N + Fintype.card σ)
    (fun N => (N : ℝ)) (tendsto_add_atTop_nat _) hr
  simpa only [card_simplexIndices, one_pow] using h

/-- Decomposing each coordinate into its quotient and residue bounds a
rationally weighted simplex by a multiple of an ordinary simplex. -/
theorem weighted_simplex_card_le {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (step : σ → ℕ) (hstep : ∀ i, 0 < step i)
    {L H : ℚ} (hL : 0 < L) (hscale : ∀ i, w i * (step i : ℚ) = L) :
    (ImaginaryQuadratic.monomialIndices w H).card ≤
      (∏ i, step i) * (⌊H / L⌋₊ + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  let quot : (σ →₀ ℕ) → σ →₀ ℕ :=
    fun α => Finsupp.equivFunOnFinite.symm (fun i => α i / step i)
  have hquot : ∀ α ∈ ImaginaryQuadratic.monomialIndices w H,
      quot α ∈ simplexIndices σ ⌊H / L⌋₊ := by
    intro α hα
    apply (mem_simplexIndices_iff _ _).mpr
    apply Nat.le_floor
    apply (le_div_iff₀ hL).mpr
    have hdeg := (ImaginaryQuadratic.mem_monomialIndices_iff w hw H α).mp hα
    calc
      _ = ∑ i, w i * ((step i * (α i / step i) : ℕ) : ℚ) := by
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        change (α i / step i : ℕ) * L = _
        rw [← hscale i]
        ring
      _ ≤ ImaginaryQuadratic.weightedDegree w α := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mul_div_le (α i) (step i)) (hw i).le)
      _ ≤ H := hdeg
  let encode : {α // α ∈ ImaginaryQuadratic.monomialIndices w H} →
      (∀ i, Fin (step i)) × {β // β ∈ simplexIndices σ ⌊H / L⌋₊} :=
    fun α => ((fun i => ⟨α.val i % step i, Nat.mod_lt _ (hstep i)⟩),
      ⟨quot α.val, hquot α.val α.prop⟩)
  have hinj : Function.Injective encode := by
    intro α β h
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have hr : α.val i % step i = β.val i % step i :=
      congrArg (fun x => (x.1 i).val) h
    have hq : α.val i / step i = β.val i / step i := by
      have h' := congrArg (fun x => x.2.val i) h
      exact h'
    have hα := Nat.mod_add_div (α.val i) (step i)
    have hβ := Nat.mod_add_div (β.val i) (step i)
    rw [hr, hq] at hα
    exact hα.symm.trans hβ
  have h := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_pi,
    Fintype.card_fin, card_simplexIndices] using h

/-- All residues fit once the quotient simplex is reduced by a fixed
dimension-sized boundary layer. This matches the upper bound asymptotically. -/
theorem weighted_simplex_card_ge {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (step : σ → ℕ) (hstep : ∀ i, 0 < step i)
    {L H : ℚ} (hL : 0 < L) (hscale : ∀ i, w i * (step i : ℚ) = L)
    (hH : (Fintype.card σ : ℚ) ≤ H / L) :
    (∏ i, step i) * (⌊H / L⌋₊ - Fintype.card σ + Fintype.card σ).choose (Fintype.card σ) ≤
      (ImaginaryQuadratic.monomialIndices w H).card := by
  classical
  let B := ⌊H / L⌋₊ - Fintype.card σ
  let assemble : (∀ i, Fin (step i)) → (σ →₀ ℕ) → σ →₀ ℕ :=
    fun r β => Finsupp.equivFunOnFinite.symm (fun i => step i * β i + (r i).val)
  have hfloor : Fintype.card σ ≤ ⌊H / L⌋₊ := Nat.le_floor hH
  have hmem : ∀ (r : ∀ i, Fin (step i)) (β : σ →₀ ℕ), β ∈ simplexIndices σ B →
      assemble r β ∈ ImaginaryQuadratic.monomialIndices w H := by
    intro r β hβ
    apply (ImaginaryQuadratic.mem_monomialIndices_iff w hw H _).mpr
    have hsum := (mem_simplexIndices_iff B β).mp hβ
    have hbound : ImaginaryQuadratic.weightedDegree w (assemble r β) ≤
        L * ((∑ i, β i : ℕ) + Fintype.card σ) := by
      calc
        _ = ∑ i, (L * (β i : ℚ) + w i * ((r i).val : ℚ)) := by
          unfold ImaginaryQuadratic.weightedDegree
          apply Finset.sum_congr rfl
          intro i hi
          change w i * ((step i * β i + (r i).val : ℕ) : ℚ) = _
          push_cast
          rw [← hscale i]
          ring
        _ ≤ ∑ i, (L * (β i : ℚ) + L) := by
          apply Finset.sum_le_sum
          intro i hi
          apply add_le_add le_rfl
          rw [← hscale i]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast (r i).isLt.le) (hw i).le
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_sum]
          ring
    calc
      _ ≤ L * ((∑ i, β i : ℕ) + Fintype.card σ) := hbound
      _ ≤ L * (⌊H / L⌋₊ : ℚ) := by
        apply mul_le_mul_of_nonneg_left _ hL.le
        have hn : (∑ i, β i) + Fintype.card σ ≤ ⌊H / L⌋₊ :=
          (Nat.add_le_add_right hsum (Fintype.card σ)).trans_eq (Nat.sub_add_cancel hfloor)
        exact_mod_cast hn
      _ ≤ H := by
        simpa only [mul_comm] using (le_div_iff₀ hL).mp
          (Nat.floor_le ((Nat.cast_nonneg (Fintype.card σ)).trans hH))
  let encode : (∀ i, Fin (step i)) × {β // β ∈ simplexIndices σ B} →
      {α // α ∈ ImaginaryQuadratic.monomialIndices w H} :=
    fun x => ⟨assemble x.1 x.2.val, hmem x.1 x.2.val x.2.prop⟩
  have hinj : Function.Injective encode := by
    intro x y heq
    have hv : ∀ i, step i * x.2.val i + (x.1 i).val = step i * y.2.val i + (y.1 i).val :=
      fun i => congrArg (fun α => α.val i) heq
    have hr : x.1 = y.1 := by
      funext i
      apply Fin.ext
      have h := congrArg (fun n => n % step i) (hv i)
      simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
        Nat.mod_eq_of_lt (x.1 i).isLt, Nat.mod_eq_of_lt (y.1 i).isLt] using h
    apply Prod.ext hr
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have h := hv i
    rw [hr] at h
    exact Nat.eq_of_mul_eq_mul_left (hstep i) (Nat.add_right_cancel h)
  have h := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_pi,
    Fintype.card_fin, card_simplexIndices, B] using h

/-- The upper and lower residue bounds have the same leading term. -/
theorem weighted_simplex_leading_term_on_period {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (step : σ → ℕ) (hstep : ∀ i, 0 < step i)
    {L : ℚ} (hL : 0 < L) (hscale : ∀ i, w i * (step i : ℚ) = L) :
    Tendsto (fun n : ℕ => ((ImaginaryQuadratic.monomialIndices w ((n : ℚ) * L)).card : ℝ) /
      (n : ℝ) ^ Fintype.card σ) atTop
      (𝓝 (((∏ i, step i : ℕ) : ℝ) / (Fintype.card σ).factorial)) := by
  classical
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_natCast_div_add_atTop (0 : ℝ)
  have hlo := (choose_scaled_limit (Fintype.card σ) id (fun n => (n : ℝ)) tendsto_id hratio).const_mul
    ((∏ i, step i : ℕ) : ℝ)
  have hhi := (simplex_count_leading_term σ).const_mul ((∏ i, step i : ℕ) : ℝ)
  simp only [one_pow, mul_one_div] at hlo
  simp only [mul_one_div] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (Fintype.card σ)] with n hn
    have hH : (Fintype.card σ : ℚ) ≤ (n : ℚ) * L / L := by
      rw [mul_div_cancel_right₀ _ hL.ne']
      exact_mod_cast hn
    have h := weighted_simplex_card_ge w hw step hstep hL hscale hH
    simp only [mul_div_cancel_right₀ _ hL.ne', Nat.floor_natCast, Nat.sub_add_cancel hn] at h
    have h' : ((∏ i, step i : ℕ) : ℝ) * (n.choose (Fintype.card σ) : ℝ) ≤
        ((ImaginaryQuadratic.monomialIndices w ((n : ℚ) * L)).card : ℝ) := by exact_mod_cast h
    simpa only [id_eq, mul_div_assoc] using div_le_div_of_nonneg_right h' (pow_nonneg (Nat.cast_nonneg _) _)
  · filter_upwards with n
    have h := weighted_simplex_card_le w hw step hstep (H := (n : ℚ) * L) hL hscale
    simp only [mul_div_cancel_right₀ _ hL.ne', Nat.floor_natCast] at h
    have h' : ((ImaginaryQuadratic.monomialIndices w ((n : ℚ) * L)).card : ℝ) ≤
        ((∏ i, step i : ℕ) : ℝ) * ((simplexIndices σ n).card : ℝ) := by
      rw [card_simplexIndices]
      exact_mod_cast h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h' (pow_nonneg (Nat.cast_nonneg _) _)

/-- Every finite family of positive rational weights has an integer period
whose quotient by each weight is a positive integer. -/
theorem exists_integer_weight_period {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) :
    ∃ L : ℕ, 0 < L ∧ ∃ step : σ → ℕ, (∀ i, 0 < step i) ∧
      ∀ i, w i * (step i : ℚ) = (L : ℚ) := by
  classical
  let n : σ → ℕ := fun i => (w i).num.natAbs
  have hn : ∀ i, 0 < n i := by
    intro i
    have hp := Rat.num_pos.mpr (hw i)
    exact Int.natAbs_pos.mpr hp.ne'
  let L := ∏ i, n i
  have hL : 0 < L := Finset.prod_pos (fun i _ => hn i)
  have hdiv : ∀ i, ∃ t : ℕ, L = n i * t := fun i =>
    Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  choose t ht using hdiv
  refine ⟨L, hL, (fun i => t i * (w i).den), ?_, ?_⟩
  · intro i
    have hti : 0 < t i := by
      by_contra hti
      have ht0 : t i = 0 := Nat.eq_zero_of_not_pos hti
      have h := hL
      rw [ht i, ht0, mul_zero] at h
      omega
    exact Nat.mul_pos hti (w i).pos
  · intro i
    have habs : (n i : ℚ) = ((w i).num : ℚ) := by
      have hn' : (n i : ℤ) = (w i).num := Int.natAbs_of_nonneg (Rat.num_pos.mpr (hw i)).le
      exact_mod_cast hn'
    have hwd : w i * ((w i).den : ℚ) = (n i : ℚ) := by
      rw [habs]
      exact (eq_div_iff (by exact_mod_cast (w i).pos.ne')).mp (w i).num_div_den.symm
    rw [Nat.cast_mul]
    calc
      _ = (w i * ((w i).den : ℚ)) * (t i : ℚ) := by ring
      _ = _ := by rw [hwd, ht i, Nat.cast_mul]

/-- Normalizing by the actual degree recovers the simplex volume constant. -/
theorem weighted_simplex_volume_limit {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (step : σ → ℕ) (hstep : ∀ i, 0 < step i)
    {L : ℚ} (hL : 0 < L) (hscale : ∀ i, w i * (step i : ℚ) = L) :
    Tendsto (fun n : ℕ => ((ImaginaryQuadratic.monomialIndices w ((n : ℚ) * L)).card : ℝ) /
      ((n : ℝ) * (L : ℝ)) ^ Fintype.card σ) atTop
      (𝓝 (1 / ((Fintype.card σ).factorial * ∏ i, (w i : ℝ)))) := by
  classical
  have hprod : (∏ i, (w i : ℝ)) * ((∏ i, step i : ℕ) : ℝ) = (L : ℝ) ^ Fintype.card σ := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    calc
      _ = ∏ _i : σ, (L : ℝ) := Finset.prod_congr rfl (fun i _ => by exact_mod_cast hscale i)
      _ = _ := by simp
  have h := (weighted_simplex_leading_term_on_period w hw step hstep hL hscale).div_const
    ((L : ℝ) ^ Fintype.card σ)
  have hwprod : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hf : ((Fintype.card σ).factorial : ℝ) ≠ 0 := by positivity
  convert h using 1
  · funext n
    rw [mul_pow, div_div]
  · congr 1
    field_simp [hf, hwprod, hL']
    nlinarith [hprod]

/-- The counting limit is available along a subsequence of any prescribed
admissible degree progression. No interpolation divisibility is lost. -/
theorem exists_admissible_weighted_simplex_limit {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (R : ℕ) (hR : 0 < R) :
    ∃ L : ℕ, 0 < L ∧ R ∣ L ∧
      Tendsto (fun n : ℕ => ((ImaginaryQuadratic.monomialIndices w ((n * L : ℕ) : ℚ)).card : ℝ) /
        ((n * L : ℕ) : ℝ) ^ Fintype.card σ) atTop
        (𝓝 (1 / ((Fintype.card σ).factorial * ∏ i, (w i : ℝ)))) := by
  obtain ⟨L, hL, step, hstep, hscale⟩ := exists_integer_weight_period w hw
  refine ⟨L * R, Nat.mul_pos hL hR, dvd_mul_left _ _, ?_⟩
  have hscale' : ∀ i, w i * ((step i * R : ℕ) : ℚ) = ((L * R : ℕ) : ℚ) := by
    intro i
    push_cast
    rw [← mul_assoc, hscale i]
  have h := weighted_simplex_volume_limit w hw (fun i => step i * R)
    (fun i => Nat.mul_pos (hstep i) hR) (by exact_mod_cast Nat.mul_pos hL hR) hscale'
  simpa only [Nat.cast_mul, Rat.cast_mul, Rat.cast_natCast] using h

noncomputable def strictSimplexIndices {σ : Type*} [Fintype σ] (w : σ → ℚ) (H : ℚ) :
    Finset (σ →₀ ℕ) := by
  classical
  exact (ImaginaryQuadratic.weightBox w H).filter (fun α => ImaginaryQuadratic.weightedDegree w α < H)

theorem mem_strictSimplexIndices_iff {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (H : ℚ) (α : σ →₀ ℕ) :
    α ∈ strictSimplexIndices w H ↔ ImaginaryQuadratic.weightedDegree w α < H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr
      ⟨ImaginaryQuadratic.mem_weightBox_of_weight_le w hw h.le, h⟩

theorem card_jetIndices {σ : Type*} [Fintype σ] (K : ℕ) (v : σ → ℚ) (H : ℚ) :
    (ImaginaryQuadratic.jetIndices K v H).card = K * (strictSimplexIndices v H).card := by
  classical
  have heq : ImaginaryQuadratic.jetIndices K v H = Finset.univ ×ˢ strictSimplexIndices v H := by
    ext ρ
    simp [ImaginaryQuadratic.jetIndices, strictSimplexIndices]
  rw [heq, Finset.card_product]
  simp

/-- Strict row packets have the same volume constant as the closed source
simplex. The fixed boundary layer disappears in the degree limit. -/
theorem strict_simplex_volume_limit {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (hw : ∀ i, 0 < w i) (step : σ → ℕ) (hstep : ∀ i, 0 < step i)
    {L : ℚ} (hL : 0 < L) (hscale : ∀ i, w i * (step i : ℚ) = L) :
    Tendsto (fun n : ℕ => ((strictSimplexIndices w (((n : ℚ) + 1) * L)).card : ℝ) /
      (((n : ℝ) + 1) * (L : ℝ)) ^ Fintype.card σ) atTop
      (𝓝 (1 / ((Fintype.card σ).factorial * ∏ i, (w i : ℝ)))) := by
  classical
  have hclosed := weighted_simplex_volume_limit w hw step hstep hL hscale
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hlo : Tendsto (fun n : ℕ => ((ImaginaryQuadratic.monomialIndices w ((n : ℚ) * L)).card : ℝ) /
      (((n : ℝ) + 1) * (L : ℝ)) ^ Fintype.card σ) atTop
      (𝓝 (1 / ((Fintype.card σ).factorial * ∏ i, (w i : ℝ)))) := by
    have h := hclosed.mul (hratio.pow (Fintype.card σ))
    simp only [one_pow, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    simp only [mul_pow, div_pow]
    field_simp
  have hhi := hclosed.comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards with n
    apply div_le_div_of_nonneg_right _ (pow_nonneg (by positivity) _)
    exact_mod_cast Finset.card_le_card (show ImaginaryQuadratic.monomialIndices w ((n : ℚ) * L) ⊆
      strictSimplexIndices w (((n : ℚ) + 1) * L) from fun α hα =>
        (mem_strictSimplexIndices_iff w hw _ α).mpr
          (((ImaginaryQuadratic.mem_monomialIndices_iff w hw _ α).mp hα).trans_lt (by nlinarith)))
  · filter_upwards with n
    apply div_le_div_of_nonneg_right _ (pow_nonneg (by positivity) _)
    exact_mod_cast Finset.card_le_card (show strictSimplexIndices w (((n : ℚ) + 1) * L) ⊆
      ImaginaryQuadratic.monomialIndices w (((n : ℚ) + 1) * L) from fun α hα =>
        (ImaginaryQuadratic.mem_monomialIndices_iff w hw _ α).mpr
          (((mem_strictSimplexIndices_iff w hw _ α).mp hα).le))

end QuadraticField
