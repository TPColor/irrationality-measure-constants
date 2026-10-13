import ArctanProof.NonzeroMinor
import ArctanProof.WeightedIndices

/-! # The interpolation matrix

The finite source is indexed by permitted monomials. The finite target is
indexed by centres and retained local coefficients. Surjectivity of the
coefficient substitution produces a nonzero minor of exactly that matrix.
-/

namespace ImaginaryQuadratic

noncomputable def localVariables {m K : ℕ} (y : Fin K → ℂ)
    (c : Fin K → Fin m → ℂ) (j : Fin K) :
    Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
  Fin.cases (MvPowerSeries.C (y j) * (1 + MvPowerSeries.X 0))
    (fun i => MvPowerSeries.C (c j i) + MvPowerSeries.X i.succ +
      LiuJiangZhang.logOneAdd m)

noncomputable def coefficientMap {m K : ℕ} (y : Fin K → ℂ)
    (c : Fin K → Fin m → ℂ) (v : Fin (m + 1) → ℚ) (H : ℚ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ]
      ({ρ // ρ ∈ jetIndices K v H} → ℂ) :=
  LinearMap.pi (fun ρ => (MvPowerSeries.coeff ρ.val.2).comp
    (MvPolynomial.aeval (localVariables y c ρ.val.1)).toLinearMap)

theorem coefficientMap_apply {m K : ℕ} (y : Fin K → ℂ)
    (c : Fin K → Fin m → ℂ) (v : Fin (m + 1) → ℚ) (H : ℚ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) (ρ : {ρ // ρ ∈ jetIndices K v H}) :
    coefficientMap y c v H P ρ = MvPowerSeries.coeff ρ.val.2
      (MvPolynomial.eval₂ MvPowerSeries.C (localVariables y c ρ.val.1) P) := by
  simp only [coefficientMap, LinearMap.pi_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_def, MvPowerSeries.c_eq_algebraMap]

/-- The coefficient-surjectivity conclusion of Theorem 9 is enough to select
a nonzero square monomial minor, keeping every prescribed row. -/
theorem nonzero_minor_of_coefficient_surjectivity {m K : ℕ}
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (H : ℚ) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (honto : ∀ target : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
        (∀ α ∈ P.support, weightedDegree w α ≤ H) ∧
        ∀ (j : Fin K) (α : Fin (m + 1) →₀ ℕ), weightedDegree v α < H →
          MvPowerSeries.coeff α (MvPolynomial.eval₂ MvPowerSeries.C
            (localVariables y c j) P) = target j α) :
    ∃ f : {ρ // ρ ∈ jetIndices K v H} → {α // α ∈ monomialIndices w H},
      (Matrix.of (fun ρ τ => coefficientMap y c v H
        (MvPolynomial.monomial (f τ).val 1) ρ)).det ≠ 0 := by
  classical
  apply exists_nonzero_monomial_minor (monomialIndices w H) (coefficientMap y c v H)
  intro target
  let packet : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ := fun j α =>
    if h : (j, α) ∈ jetIndices K v H then target ⟨(j, α), h⟩ else 0
  obtain ⟨P, hsupport, hP⟩ := honto packet
  refine ⟨P, ?_, ?_⟩
  · intro α hα
    exact (mem_monomialIndices_iff w hw H α).mpr (hsupport α hα)
  · ext ρ
    rw [coefficientMap_apply, hP ρ.val.1 ρ.val.2
      ((mem_jetIndices_iff K v hv H ρ.val).mp ρ.property)]
    simp only [packet, dite_eq_left ρ.property]

/-- Theorem 9 gives nonzero interpolation minors with weight thresholds and
degree divisibility fixed before the centres. -/
theorem exists_nonzero_interpolation_minors
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
              ∃ f : {ρ // ρ ∈ jetIndices K V (n * R : ℕ)} →
                  {α // α ∈ monomialIndices W (n * R : ℕ)},
                (Matrix.of (fun ρ τ => coefficientMap y c V (n * R : ℕ)
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
  intro n hn
  apply nonzero_minor_of_coefficient_surjectivity
    (Fin.cases w0 w) (Fin.cases v0 (fun i => w i / θ))
  · intro i
    refine Fin.cases hw0 (fun j => hw j) i
  · intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
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
