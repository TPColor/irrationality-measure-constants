import QuadraticFieldCriterion.LogChangeOfVariables
import QuadraticFieldCriterion.InterpolationMinor

/-! # Interpolation with finite logarithm polynomials

The filtered triangular change of variables carries every prescribed packet
to the packet with truncated logarithms. It preserves the polynomial support,
and hence also yields a nonzero monomial minor containing all retained rows.
-/

namespace ImaginaryQuadratic

noncomputable def truncatedLocalVariables {m K : ℕ} (T : Fin m → ℕ)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (j : Fin K) :
    Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
  Fin.cases (MvPowerSeries.C (y j) * (1 + MvPowerSeries.X 0))
    (fun i => MvPowerSeries.C (c j i) + MvPowerSeries.X i.succ + truncatedLog m (T i))

theorem logShift_localVariables {m K : ℕ} (T : Fin m → ℕ)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (j : Fin K) (i : Fin (m + 1)) :
    MvPowerSeries.subst (logShift m T) (localVariables y c j i) =
      truncatedLocalVariables T y c j i := by
  have ha := logShift_hasSubst m T
  refine Fin.cases ?_ (fun i => ?_) i
  · have hone : MvPowerSeries.subst (logShift m T)
        (1 : MvPowerSeries (Fin (m + 1)) ℂ) = 1 := by
      rw [← MvPowerSeries.substAlgHom_apply ha]
      exact map_one _
    simp [localVariables, truncatedLocalVariables, MvPowerSeries.subst_mul ha,
      MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, hone, logShift]
  · simp only [localVariables, truncatedLocalVariables, Fin.cases_succ]
    rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
      MvPowerSeries.subst_C, MvPowerSeries.subst_X ha,
      subst_logOneAdd_of_fixed_t ha (by simp [logShift])]
    simp only [logShift, Fin.cases_succ]
    ring

/-- Surjectivity is retained after replacing each logarithm by its fixed
truncation. The truncation order does not depend on the eventual degree `H`. -/
theorem truncated_coefficient_surjectivity {m K : ℕ}
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (H : ℚ) (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ v 0 * (T i : ℚ))
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (honto : ∀ target : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
        (∀ α ∈ P.support, weightedDegree w α ≤ H) ∧
        ∀ j α, weightedDegree v α < H → MvPowerSeries.coeff α
          (MvPolynomial.eval₂ MvPowerSeries.C (localVariables y c j) P) = target j α) :
    ∀ target : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
        (∀ α ∈ P.support, weightedDegree w α ≤ H) ∧
        ∀ j α, weightedDegree v α < H → MvPowerSeries.coeff α
          (MvPolynomial.eval₂ MvPowerSeries.C (truncatedLocalVariables T y c j) P) =
            target j α := by
  classical
  have hsurj := multicentre_packet_surjectivity_change v (fun i => (hv i).le) H
    (monomialIndices w H) (localVariables y c)
    (logShift_hasSubst m T) (logShift_filtered v (fun i => (hv i).le) T hT)
    (logShift_inverse m T)
  have hsource : ∀ target : Fin K → MvPowerSeries (Fin (m + 1)) ℂ,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ, P.support ⊆ monomialIndices w H ∧
        ∀ j α, weightedDegree v α < H → MvPowerSeries.coeff α
          (MvPolynomial.eval₂ MvPowerSeries.C (localVariables y c j) P) =
            MvPowerSeries.coeff α (target j) := by
    intro target
    obtain ⟨P, hP, hc⟩ := honto (fun j α => MvPowerSeries.coeff α (target j))
    exact ⟨P, fun α hα => (mem_monomialIndices_iff w hw H α).mpr (hP α hα), hc⟩
  intro target
  obtain ⟨P, hP, hc⟩ := hsurj hsource (fun j => target j)
  refine ⟨P, ?_, ?_⟩
  · intro α hα
    exact (mem_monomialIndices_iff w hw H α).mp (hP hα)
  · intro j α hα
    have h := hc j α hα
    change MvPowerSeries.coeff α
      (MvPolynomial.eval₂ MvPowerSeries.C
        (fun i => MvPowerSeries.subst (logShift m T) (localVariables y c j i)) P) =
      target j α at h
    simpa only [logShift_localVariables] using h

noncomputable def truncatedCoefficientMap {m K : ℕ} (T : Fin m → ℕ)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (v : Fin (m + 1) → ℚ) (H : ℚ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ]
      ({ρ // ρ ∈ jetIndices K v H} → ℂ) :=
  LinearMap.pi (fun ρ => (MvPowerSeries.coeff ρ.val.2).comp
    (MvPolynomial.aeval (truncatedLocalVariables T y c ρ.val.1)).toLinearMap)

theorem truncatedCoefficientMap_apply {m K : ℕ} (T : Fin m → ℕ)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (v : Fin (m + 1) → ℚ) (H : ℚ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) (ρ : {ρ // ρ ∈ jetIndices K v H}) :
    truncatedCoefficientMap T y c v H P ρ = MvPowerSeries.coeff ρ.val.2
      (MvPolynomial.eval₂ MvPowerSeries.C (truncatedLocalVariables T y c ρ.val.1) P) := by
  simp only [truncatedCoefficientMap, LinearMap.pi_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_def, MvPowerSeries.c_eq_algebraMap]

/-- A nonzero minor with every row exists for the truncated-log matrix. -/
theorem nonzero_truncated_minor_of_coefficient_surjectivity {m K : ℕ}
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (H : ℚ) (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ v 0 * (T i : ℚ))
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (honto : ∀ target : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
        (∀ α ∈ P.support, weightedDegree w α ≤ H) ∧
        ∀ j α, weightedDegree v α < H → MvPowerSeries.coeff α
          (MvPolynomial.eval₂ MvPowerSeries.C (localVariables y c j) P) = target j α) :
    ∃ f : {ρ // ρ ∈ jetIndices K v H} → {α // α ∈ monomialIndices w H},
      (Matrix.of (fun ρ τ => truncatedCoefficientMap T y c v H
        (MvPolynomial.monomial (f τ).val 1) ρ)).det ≠ 0 := by
  classical
  have htr := truncated_coefficient_surjectivity w v hw hv H T hT y c honto
  apply exists_nonzero_monomial_minor (monomialIndices w H)
    (truncatedCoefficientMap T y c v H)
  intro target
  let packet : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ := fun j α =>
    if h : (j, α) ∈ jetIndices K v H then target ⟨(j, α), h⟩ else 0
  obtain ⟨P, hP, hc⟩ := htr packet
  refine ⟨P, fun α hα => (mem_monomialIndices_iff w hw H α).mpr (hP α hα), ?_⟩
  ext ρ
  rw [truncatedCoefficientMap_apply, hc ρ.val.1 ρ.val.2
    ((mem_jetIndices_iff K v hv H ρ.val).mp ρ.property)]
  simp only [packet, dite_eq_left ρ.property]

/-- The existing interpolation axiom supplies nonzero truncated-log minors,
with the weights and degree divisibility chosen before the centres. -/
theorem exists_nonzero_truncated_interpolation_minors
    (m K κ : ℕ) (hm : 1 ≤ m) (hK : 1 ≤ K) (hκ : 1 ≤ κ) (hκK : κ ≤ K)
    (w0 v0 θ : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hvolume : (K : ℚ) * (w0 / v0) * θ ^ m < 1)
    (hfibreVolume : (κ : ℚ) * θ ^ m < 1) :
    ∃ thresholds : Fin m → List ℚ → ℚ,
      ∀ w : Fin m → ℚ, (∀ i, 0 < w i) →
        (∀ i, thresholds i ((List.ofFn w).take i.val) < w i) →
        let W : Fin (m + 1) → ℚ := Fin.cases w0 w
        let V : Fin (m + 1) → ℚ := Fin.cases v0 (fun i => w i / θ)
        ∃ R : ℕ, 0 < R ∧
          ∀ (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ),
            (∀ j, y j ≠ 0) →
            (∀ z : ℂ, (Finset.univ.filter (fun j => y j = z)).card ≤ κ) →
            (∀ j k, j ≠ k → y j = y k → ∀ i, c j i ≠ c k i) →
            ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
              ∀ T : Fin m → ℕ, (∀ i, w i / θ ≤ v0 * (T i : ℚ)) →
              ∃ f : {ρ // ρ ∈ jetIndices K V (n * R : ℕ)} →
                  {α // α ∈ monomialIndices W (n * R : ℕ)},
                (Matrix.of (fun ρ τ => truncatedCoefficientMap T y c V (n * R : ℕ)
                  (MvPolynomial.monomial (f τ).val 1) ρ)).det ≠ 0 := by
  classical
  obtain ⟨thresholds, hthresholds⟩ := LiuJiangZhang.theorem9
    m K κ hm hK hκ hκK w0 v0 θ hw0 hv0 hθ hθ1 hvolume hfibreVolume
  refine ⟨thresholds, ?_⟩
  intro w hw hweights
  dsimp only
  obtain ⟨R, hR, hcentres⟩ := hthresholds w hw hweights
  refine ⟨R, hR, ?_⟩
  intro y c hy hfibre hsep
  obtain ⟨n0, hn0⟩ := hcentres y c hy hfibre hsep
  refine ⟨n0, ?_⟩
  intro n hn T hT
  apply nonzero_truncated_minor_of_coefficient_surjectivity
    (Fin.cases w0 w) (Fin.cases v0 (fun i => w i / θ))
  · intro i
    exact Fin.cases hw0 (fun j => hw j) i
  · intro i
    exact Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  · exact hT
  · intro target
    obtain ⟨P, hP, hcoeff⟩ := hn0 n hn target
    refine ⟨P, ?_, ?_⟩
    · intro α hα
      simpa only [weightedDegree, Fin.sum_univ_succ, Fin.cases_zero,
        Fin.cases_succ] using hP α hα
    · intro j α hα
      apply hcoeff j α
      simpa only [weightedDegree, Fin.sum_univ_succ, Fin.cases_zero,
        Fin.cases_succ] using hα

end ImaginaryQuadratic
