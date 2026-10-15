import QuadraticFieldCriterion.RowChoices
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Polynomial counting costs vanish after dividing by the degree -/

namespace QuadraticField

open Filter Topology

theorem logarithmic_degree_error_tendsto_zero (a b : ℝ) :
    Tendsto (fun H : ℝ => (a * Real.log H + b) / H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hc := (tendsto_id : Tendsto (fun H : ℝ => H) atTop atTop).const_div_atTop b
  have h := (hlog.const_mul a).add hc
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext H
  change (a * Real.log H + b) / H = a * (Real.log H / H) + b / H
  ring

theorem log_polynomial_degree_error_tendsto_zero (C : ℝ) (d : ℕ) (b : ℝ) :
    Tendsto (fun H : ℝ => (Real.log (C * H ^ d) + b) / H) atTop (𝓝 0) := by
  by_cases hC : C = 0
  · simpa [hC] using (tendsto_id : Tendsto (fun H : ℝ => H) atTop atTop).const_div_atTop b
  apply (logarithmic_degree_error_tendsto_zero d (Real.log C + b)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  rw [Real.log_mul hC (pow_ne_zero _ hH.ne'), Real.log_pow]
  ring

theorem card_RowChoice_le_degree_power {m : ℕ} (N : Fin m → ℕ) (β : Fin m →₀ ℕ) (s : ℕ)
    {H v₀ wstar : ℝ} (hH : 1 ≤ H) (hv₀ : 0 < v₀) (hwstar : 0 < wstar)
    (hs : (s : ℝ) ≤ H / v₀) (hN : ∀ i, (N i : ℝ) ≤ H / wstar) :
    (Fintype.card (RowChoice N β s) : ℝ) ≤ ((1 + v₀⁻¹ + wstar⁻¹) * H) ^ (2 * m + 1) := by
  apply card_RowChoice_real_le
  · have hi : 0 ≤ wstar⁻¹ := inv_nonneg.mpr hwstar.le
    have hh : 0 ≤ H := le_trans zero_le_one hH
    have hp := mul_nonneg hi hh
    simp only [div_eq_mul_inv] at hs
    nlinarith
  · intro i
    have hi : 0 ≤ v₀⁻¹ := inv_nonneg.mpr hv₀.le
    have hh : 0 ≤ H := le_trans zero_le_one hH
    have hp := mul_nonneg hi hh
    have hn := hN i
    simp only [div_eq_mul_inv] at hn
    nlinarith

theorem log_count_div_degree_tendsto_zero (M : ℕ → ℕ) (H : ℕ → ℝ)
    (hH : Tendsto H atTop atTop) {C : ℝ} (_hC : 0 ≤ C) (d : ℕ)
    (hM : ∀ᶠ n in atTop, (M n : ℝ) ≤ C * H n ^ d) :
    Tendsto (fun n => Real.log ((M n : ℝ) + 1) / H n) atTop (𝓝 0) := by
  have hhi := (log_polynomial_degree_error_tendsto_zero (C + 1) d 0).comp hH
  simp only [Function.comp_def, add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi
  · filter_upwards [hH.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    exact div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (M n); linarith)) (by linarith)
  · filter_upwards [hM, hH.eventually (eventually_ge_atTop (1 : ℝ))] with n hm hn
    apply div_le_div_of_nonneg_right _ (by linarith)
    apply Real.log_le_log (by positivity)
    have hp : 1 ≤ H n ^ d := one_le_pow₀ hn
    nlinarith

theorem normalized_log_choice_count_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {m : ℕ} (N : Fin m → ℕ) (β : ι → Fin m →₀ ℕ) (s : ι → ℕ)
    {H C : ℝ} (hH : 0 < H) (_hC : 0 < C)
    (hs : ∀ r, (s r : ℝ) + 1 ≤ C * H) (hN : ∀ i, (N i : ℝ) + 1 ≤ C * H) :
    Real.log (Fintype.card (∀ r, RowChoice N (β r) (s r)) : ℝ) /
      (Fintype.card ι * H) ≤ (2 * m + 1) * Real.log (C * H) / H := by
  classical
  have hbound : (Fintype.card (∀ r, RowChoice N (β r) (s r)) : ℝ) ≤
      ((C * H) ^ (2 * m + 1)) ^ Fintype.card ι := by
    rw [Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _r : ι, (C * H) ^ (2 * m + 1) :=
        Finset.prod_le_prod₀ (fun r _ => Nat.cast_nonneg _) (fun r _ => card_RowChoice_real_le N (β r) (s r) (C * H) (hs r) hN)
      _ = _ := by simp
  have hpos : (0 : ℝ) < Fintype.card (∀ r, RowChoice N (β r) (s r)) := by
    exact_mod_cast Fintype.card_pos
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_pow, Real.log_pow] at hlog
  have hM : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (mul_pos hM hH)).mpr
  calc
    _ ≤ (Fintype.card ι : ℝ) * ((2 * m + 1 : ℕ) : ℝ) * Real.log (C * H) := by
      simpa only [mul_assoc] using hlog
    _ = _ := by
      field_simp
      push_cast
      ring

theorem jet_card_le_polynomial {σ : Type*} [Fintype σ]
    (K : ℕ) (v : σ → ℚ) (hv : ∀ i, 0 < v i) {H : ℚ} (hH : 1 ≤ H) :
    ((ImaginaryQuadratic.jetIndices K v H).card : ℝ) ≤
      ((K : ℝ) * ∏ i, (1 + 1 / (v i : ℝ))) * (H : ℝ) ^ Fintype.card σ := by
  classical
  let cap : σ → ℕ := fun i => ⌊H / v i⌋₊
  have hcap : ∀ ρ : {ρ // ρ ∈ ImaginaryQuadratic.jetIndices K v H}, ∀ i, ρ.val.2 i ≤ cap i := by
    intro ρ i
    apply Nat.le_floor
    apply (le_div_iff₀ (hv i)).mpr
    have hc := ImaginaryQuadratic.coordinate_le_weightedDegree v (fun i => (hv i).le) ρ.val.2 i
    have hr := (ImaginaryQuadratic.mem_jetIndices_iff K v hv H ρ.val).mp ρ.property
    nlinarith
  let f : {ρ // ρ ∈ ImaginaryQuadratic.jetIndices K v H} → Fin K × (∀ i, Fin (cap i + 1)) :=
    fun ρ => (ρ.val.1, fun i => ⟨ρ.val.2 i, Nat.lt_succ_of_le (hcap ρ i)⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x : Fin K × (∀ i, Fin (cap i + 1)) => x.1) hab
    · apply Finsupp.ext
      intro i
      exact congrArg (fun x : Fin K × (∀ i, Fin (cap i + 1)) => (x.2 i : ℕ)) hab
  have hcount : (ImaginaryQuadratic.jetIndices K v H).card ≤ K * ∏ i, (cap i + 1) := by
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin] using h
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hb : ∀ i, (cap i : ℝ) + 1 ≤ (1 + 1 / (v i : ℝ)) * (H : ℝ) := by
    intro i
    have hfloor : ((cap i : ℕ) : ℚ) ≤ H / v i := Nat.floor_le (div_nonneg (by linarith) (hv i).le)
    have hfloor' : (cap i : ℝ) ≤ (H : ℝ) / (v i : ℝ) := by exact_mod_cast hfloor
    simp only [div_eq_mul_inv]
    simp only [div_eq_mul_inv] at hfloor'
    nlinarith
  calc
    _ ≤ (K : ℝ) * ∏ i, ((cap i : ℝ) + 1) := by exact_mod_cast hcount
    _ ≤ (K : ℝ) * ∏ i, ((1 + 1 / (v i : ℝ)) * (H : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hb i)) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [mul_assoc]

end QuadraticField
