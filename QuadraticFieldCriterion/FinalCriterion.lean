import QuadraticFieldCriterion.CriterionCentres
import QuadraticFieldCriterion.DimensionLimits
import QuadraticFieldCriterion.EstimateNormalization
import QuadraticFieldCriterion.ParameterSelection

/-! # The quadratic field criterion -/

namespace QuadraticField

set_option maxHeartbeats 1000000

open Filter Topology

/-- The eventual strict bound for unreduced rational approximations. -/
theorem approximationBound :
    ∀ (D : ℤ), ¬ IsSquare D → ∀ (x : ℝ), x ≠ 0 →
      HasNormOneCoordinates D (Complex.exp (2 * root D * (x : ℂ))) →
      ImaginaryQuadratic.EventualStrictBound x := by
  classical
  intro D hD x hx hα
  let : Fact (¬ IsSquare (D : ℚ)) := ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  by_contra hbound
  obtain ⟨ν, hν, hbad⟩ := (not_eventualStrictBound_iff x).mp hbound
  obtain ⟨α, hα, hnorm⟩ := hα
  obtain ⟨den, hden, hdenα⟩ := exists_integerOrder_denominator hD α
  obtain ⟨θ, A, B, C, η, hθ, hθA, hAB, hB1, hC, hCB, hBCT, hCθ,
    hη, hη1, hgap⟩ := ImaginaryQuadratic.exists_gap_parameters ν hν
  have hA : 0 < A := hθ.trans hθA
  have hB : 0 < B := hA.trans hAB
  have hθ1 : θ < 1 := hθA.trans (hAB.trans hB1)
  let ω := 2 * root D * (x : ℂ)
  let γ := 2 * root D
  let gap := ν * ((A : ℝ) * (1 - η) - θ) - (1 - (θ : ℝ))
  let ε : ℝ := min (gap / 8) (1 / 8)
  have hε : 0 < ε := lt_min (div_pos hgap (by norm_num)) (by norm_num)
  let growth : ℕ → ℝ := fun m =>
    (Real.log 4 + 4) * m + θ +
      Real.log (4 * max 1 ((centreCount C m : ℝ) * ‖γ‖ * Real.exp ν)) +
      Real.log (8 * centreCount C m * (1 + ‖ω‖))
  obtain ⟨F, m, wstar, hF, hFθ, hνF, hm, hwstar, hcore, hcollision, hweight⟩ :=
    exists_criterion_scales ν θ A B C η ε (Real.log (den : ℝ)) ω
      (by linarith) hθ hA hAB hC hCB hBCT hη hε growth (2 * (ν * θ + 3))
  let K : ℕ := ⌊C ^ m⌋₊
  let w₀ : ℚ := (B ^ m)⁻¹
  let v₀ : ℚ := 2 * (K : ℚ) * θ ^ m * w₀
  obtain ⟨hK, hw₀, hv₀, hfibre, hvolume⟩ :=
    ImaginaryQuadratic.dimension_data_admissible m hm θ B C hθ hB hC hCθ
  have hKcast : centreCount C m = K := by
    have h : (⌊(C : ℝ) ^ m⌋₊ : ℤ) = (⌊C ^ m⌋₊ : ℤ) := by
      rw [Int.natCast_floor_eq_floor (by positivity), Int.natCast_floor_eq_floor (by positivity),
        ← Rat.cast_pow, Rat.floor_cast]
    change ⌊(C : ℝ) ^ m⌋₊ = ⌊C ^ m⌋₊
    rw [← Rat.cast_pow]
    exact_mod_cast h
  have hwcast : (w₀ : ℝ) = degreeWeight B m := by simp [w₀, degreeWeight]
  have hvcast : (v₀ : ℝ) = jetWeight θ B C m := by
    simp [v₀, jetWeight, hwcast, hKcast]
  let E : ℝ := max 1 ((K : ℝ) * ‖γ‖ * Real.exp ν)
  let Rdisk : ℝ := 4 * K * (1 + ‖ω‖)
  have hE : 1 ≤ E := le_max_left _ _
  have hRdisk : 1 ≤ Rdisk := by
    have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
    dsimp [Rdisk]
    nlinarith [norm_nonneg ω]
  have hcore' : ((Real.log 4 + 4) * (F : ℝ) * m + 2 * Real.log 2) / (v₀ : ℝ) +
      ((K : ℝ) * Real.log (den : ℝ) + Rdisk) / (w₀ : ℝ) < ε := by
    rw [← hvcast, ← hwcast, hKcast] at hcore
    convert hcore using 1
    dsimp [Rdisk]
    ring
  have hweight' : ((Real.log 4 + 4) * m + θ + Real.log (4 * E) + Real.log (2 * Rdisk)) /
      (wstar : ℝ) < ε := by
    have hr : 2 * Rdisk = 8 * K * (1 + ‖ω‖) := by dsimp [Rdisk]; ring
    simpa only [growth, hKcast, E, hr] using hweight
  obtain ⟨thresholds, hthresholds⟩ := LiuJiangZhang.theorem9 m K K hm hK hK le_rfl
    w₀ v₀ θ hw₀ hv₀ hθ hθ1 (by linarith) hfibre
  obtain ⟨pq, hpq, hpqthreshold⟩ := exists_successive_bad_approximations hx hν hbad m thresholds wstar
  let p : Fin m → ℤ := fun i => (pq i).1
  let q : Fin m → ℕ := fun i => (pq i).2
  let w : Fin m → ℚ := fun i => ((⌈Real.log (q i : ℝ)⌉ : ℤ) : ℚ)
  have hw : ∀ i, 0 < w i := fun i => hwstar.trans (hpq i).2.2.1
  have hp : ∀ i, p i ≠ 0 := fun i => (hpq i).1
  have hq : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by norm_num : 0 < 2) (hpq i).2.1
  have hmin : ∀ i, wstar ≤ w i := fun i => (hpq i).2.2.1.le
  have hsmall : criterionArithmeticError (fun i => (w i : ℝ)) F v₀ θ w₀ wstar
        (Real.log (den : ℝ)) K + translationCost ν E F v₀ wstar +
        holomorphicCost Rdisk w₀ wstar v₀ < 3 * ε := by
    have h := combined_criterion_error_le (fun i => (w i : ℝ)) F v₀ θ w₀ wstar
      (Real.log (den : ℝ)) K ν E Rdisk (by exact_mod_cast hwstar)
      (fun i => by exact_mod_cast hmin i)
    linarith
  obtain ⟨R, hR, hcentres⟩ := hthresholds w hw hpqthreshold
  let y := powerCentres α K
  let c := rationalCentres D p q K
  have hy : ∀ j, embedding D (y j) ≠ 0 := by
    intro j
    rw [embedding_powerCentres α K ω hα]
    exact pow_ne_zero _ (Complex.exp_ne_zero ω)
  have hfibres : ∀ z : ℂ, (Finset.univ.filter (fun j => embedding D (y j) = z)).card ≤ K := by
    intro z
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin K)
  have hsep : ∀ j k : Fin K, j ≠ k → embedding D (y j) = embedding D (y k) →
      ∀ i, embedding D (c j i) ≠ embedding D (c k i) := by
    intro j k hjk hyjk i hcjk
    exact hjk (embedding_rationalCentres_injective hD p q hp hq K i hcjk)
  obtain ⟨n₀, honto⟩ := hcentres (fun j => embedding D (y j)) (fun j i => embedding D (c j i)) hy hfibres hsep
  let T : Fin m → ℕ := fun i => ⌈F * w i / v₀⌉₊
  have htrunc : ∀ i, F * w i ≤ v₀ * (T i : ℚ) := by
    intro i
    have h := (div_le_iff₀ hv₀).mp (Nat.le_ceil (F * w i / v₀))
    calc
      _ ≤ (T i : ℚ) * v₀ := h
      _ = _ := mul_comm _ _
  have hfiltered : ∀ i, w i / θ ≤ v₀ * (T i : ℚ) := by
    intro i
    calc
      _ = (1 / θ) * w i := by ring
      _ ≤ F * w i := mul_le_mul_of_nonneg_right hFθ (hw i).le
      _ ≤ _ := htrunc i
  let W : Fin (m + 1) → ℚ := Fin.cases w₀ w
  let V : Fin (m + 1) → ℚ := Fin.cases v₀ (fun i => w i / θ)
  have hW : ∀ i, 0 < W i := fun i => Fin.cases hw₀ hw i
  have hV : ∀ i, 0 < V i := fun i => Fin.cases hv₀ (fun i => div_pos (hw i) hθ) i
  have hminors : ∀ n : ℕ, n₀ ≤ n →
      ∃ f : {ρ // ρ ∈ ImaginaryQuadratic.jetIndices K V (n * R : ℕ)} →
          {a // a ∈ ImaginaryQuadratic.monomialIndices W (n * R : ℕ)},
        (quadraticInterpolationMatrix D T y c (fun ρ => ρ.val.1)
          (fun ρ => ρ.val.2) (fun ρ => (f ρ).val)).det ≠ 0 := by
    intro n hn
    apply exists_nonzero_quadratic_interpolation_minor D W V hW hV (n * R : ℕ) T hfiltered y c
    intro target
    obtain ⟨P, hP, hcoeff⟩ := honto n hn target
    refine ⟨P, ?_, ?_⟩
    · intro a ha
      simpa only [ImaginaryQuadratic.weightedDegree, W, Fin.sum_univ_succ,
        Fin.cases_zero, Fin.cases_succ] using hP a ha
    · intro j a ha
      apply hcoeff j a
      simpa only [ImaginaryQuadratic.weightedDegree, V, Fin.sum_univ_succ,
        Fin.cases_zero, Fin.cases_succ] using ha
  obtain ⟨L, hL, hRL, hratio⟩ := exists_collision_count_ratio m K w hw hv₀ hθ hA R hR
  let H : ℕ → ℚ := fun n => ((n : ℚ) + 1) * (L : ℚ)
  let M : ℕ → ℕ := fun n => (ImaginaryQuadratic.jetIndices K V (H n)).card
  have hHpos : ∀ n, 0 < H n := by intro n; dsimp [H]; positivity
  have hHtop : Tendsto (fun n => (H n : ℝ)) atTop atTop := by
    have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    convert hn.atTop_mul_const (show (0 : ℝ) < L by exact_mod_cast hL) using 1
    simp only [H, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
      Nat.cast_add, Nat.cast_one]
  let countConstant : ℝ := (K : ℝ) * ∏ i, (1 + 1 / (V i : ℝ))
  have hcountConstant : 0 ≤ countConstant := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.prod_nonneg
    intro i hi
    have hv : (0 : ℝ) < V i := by exact_mod_cast hV i
    positivity
  have hMpoly : ∀ᶠ n in atTop, (M n : ℝ) ≤ countConstant * (H n : ℝ) ^ (m + 1) := by
    filter_upwards [hHtop.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    simpa only [M, countConstant, Fintype.card_fin] using
      jet_card_le_polynomial K V hV (show 1 ≤ H n by exact_mod_cast hn)
  have hlogM := log_count_div_degree_tendsto_zero M (fun n => (H n : ℝ)) hHtop hcountConstant (m + 1) hMpoly
  have hrem : Tendsto (fun n => determinantRemainder (M n) / (H n : ℝ)) atTop (𝓝 0) := by
    have h := hlogM.add (hHtop.const_div_atTop
      (Real.log 2 / 4 - Real.log (1 - Real.exp (-(Real.log 2 / 2)))))
    simp only [zero_add] at h
    convert h using 1
    funext n
    unfold determinantRemainder
    ring
  let choiceConstant : ℝ := 1 + (v₀ : ℝ)⁻¹ + (wstar : ℝ)⁻¹
  have hchoice : Tendsto (fun n => ((2 * m + 1 : ℕ) : ℝ) *
      Real.log (choiceConstant * (H n : ℝ)) / (H n : ℝ)) atTop (𝓝 0) := by
    have h := ((log_polynomial_degree_error_tendsto_zero choiceConstant 1 0).comp hHtop).const_mul
      (((2 * m + 1 : ℕ) : ℝ))
    simpa only [Function.comp_def, pow_one, add_zero, mul_zero, mul_div_assoc] using h
  have hdegreeError := hrem.add hchoice
  simp only [zero_add] at hdegreeError
  let saving : ℝ := (Real.log 2 / 4) * (η ^ 2 * ((B : ℝ) / A) ^ m / (2 * (m + 1)))
  have hsaving : Tendsto (fun n => (Real.log 2 / 4) *
      (η ^ 2 * (M n : ℝ) /
        ((ImaginaryQuadratic.monomialIndices w (A * H n)).card * (H n : ℝ))))
      atTop (𝓝 saving) := by
    have h := hratio.const_mul ((Real.log 2 / 4) * η ^ 2)
    convert h using 1
    · funext n
      dsimp [M, H, V]
      push_cast
      ring
    · congr 1
      dsimp [saving, v₀, w₀, K]
      push_cast
      rw [div_pow]
      have hkn : ((⌊C ^ m⌋₊ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      have htn : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
      have hbn : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
      have han : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
      field_simp
  have hsavingLarge : ν * (θ : ℝ) + 3 < saving := by
    have ht : 0 < ν * (θ : ℝ) + 3 := by
      have hθ' : (0 : ℝ) < θ := by exact_mod_cast hθ
      positivity
    change 2 * (ν * (θ : ℝ) + 3) < saving at hcollision
    linarith
  obtain ⟨n, hn, hdegree, hlarge, hdegreeOne⟩ := ((eventually_ge_atTop n₀).and
    ((hdegreeError.eventually (gt_mem_nhds hε)).and
      ((hsaving.eventually (lt_mem_nhds hsavingLarge)).and
        (hHtop.eventually (eventually_ge_atTop (1 : ℝ)))))).exists
  obtain ⟨d, hd⟩ := hRL
  have hdpos : 0 < d := by
    rw [hd] at hL
    exact Nat.pos_of_mul_pos_left hL
  have hn' : n₀ ≤ (n + 1) * d := by nlinarith
  have hdegreeEq : ((((n + 1) * d) * R : ℕ) : ℚ) = H n := by
    simp only [H, hd, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hminor := hminors ((n + 1) * d) hn'
  rw [hdegreeEq] at hminor
  obtain ⟨f, hf⟩ := hminor
  let ι := {ρ // ρ ∈ ImaginaryQuadratic.jetIndices K V (H n)}
  let centre : ι → Fin K := fun ρ => ρ.val.1
  let row : ι → Fin (m + 1) →₀ ℕ := fun ρ => ρ.val.2
  let column : ι → Fin (m + 1) →₀ ℕ := fun ρ => (f ρ).val
  let β : ι → Fin m →₀ ℕ := fun ρ => (row ρ).tail
  let s : ι → ℕ := fun ρ => row ρ 0
  let h : ι → ℕ := fun ρ => column ρ 0
  let l : ι → Fin m → ℕ := fun ρ i => column ρ i.succ
  let N : Fin m → ℕ := fun i => ⌊H n / w i⌋₊
  let mat := quadraticInterpolationMatrix D T y c centre row column
  let : Nonempty ι := ⟨⟨(⟨0, hK⟩, 0),
    (ImaginaryQuadratic.mem_jetIndices_iff K V hV (H n) _).mpr (by simpa [ImaginaryQuadratic.weightedDegree] using hHpos n)⟩⟩
  have hcard : Fintype.card ι = M n := by simp [ι, M]
  have hmass : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hHn : (0 : ℝ) < H n := by exact_mod_cast hHpos n
  have hrow : ∀ ρ, ImaginaryQuadratic.weightedDegree V (row ρ) < H n := fun ρ =>
    (ImaginaryQuadratic.mem_jetIndices_iff K V hV (H n) ρ.val).mp ρ.property
  have hcol : ∀ ρ, ImaginaryQuadratic.weightedDegree W (column ρ) ≤ H n := fun ρ =>
    (ImaginaryQuadratic.mem_monomialIndices_iff W hW (H n) (column ρ)).mp (f ρ).property
  have hsource := fun ρ => ImaginaryQuadratic.source_degree_budgets w hw hw₀ (column ρ) (hcol ρ)
  have hpacket := fun ρ => ImaginaryQuadratic.row_degree_budgets w hw hv₀ hθ (row ρ) (hrow ρ)
  have hcap : ∀ ρ i, column ρ i.succ ≤ N i := fun ρ i => (hsource ρ).2.2 i
  have hnormBound := interpolation_matrix_norm_lower_bound hD T q N (den ^ K)
    (pow_pos hden _) y c (powerCentres_cleared α den K hdenα) hq
    (rationalCentres_cleared hD p q hq K) centre row column hcap hf
  have hplus : (mat.map (embedding D)).det ≠ 0 := by
    intro heq
    simp only [show mat = quadraticInterpolationMatrix D T y c centre row column from rfl] at heq
    simp [heq] at hnormBound
    norm_num at hnormBound
  have hminus : (mat.map (conjugateEmbedding D)).det ≠ 0 := by
    intro heq
    simp only [show mat = quadraticInterpolationMatrix D T y c centre row column from rfl] at heq
    simp [heq] at hnormBound
    norm_num at hnormBound
  have hweightReal : ∀ i, (w i : ℝ) = (⌈Real.log (q i : ℝ)⌉ : ℤ) := by intro i; simp [w]
  have hhh : ∀ ρ, (h ρ : ℚ) ≤ H n / w₀ := fun ρ => (hsource ρ).1
  have hll : ∀ ρ, (∑ i, w i * (l ρ i : ℚ)) ≤ H n := fun ρ => (hsource ρ).2.1
  have hjet : ∀ ρ, v₀ * (s ρ : ℚ) < H n := by
    intro ρ
    rw [mul_comm]
    exact (lt_div_iff₀ hv₀).mp (hpacket ρ).1
  have hrowWeight : ∀ ρ, (∑ i, w i * (β ρ i : ℚ)) ≤ θ * H n := fun ρ => (hpacket ρ).2.le
  have hminReal : ∀ i, (wstar : ℝ) ≤ (⌈Real.log (q i : ℝ)⌉ : ℤ) := by
    intro i
    rw [← hweightReal]
    exact_mod_cast hmin i
  have hcolAr : ∀ ρ, (∑ i, (column ρ i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) ≤ (H n : ℝ) := by
    intro ρ
    have h : (∑ i, (w i : ℝ) * (column ρ i.succ : ℝ)) ≤ (H n : ℝ) := by exact_mod_cast (hsource ρ).2.1
    simpa only [hweightReal, mul_comm] using h
  have hrowAr : ∀ ρ, (∑ i, (row ρ i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) ≤ (θ : ℝ) * (H n : ℝ) := by
    intro ρ
    have h : (∑ i, (w i : ℝ) * (row ρ i.succ : ℝ)) ≤ (θ : ℝ) * (H n : ℝ) := by exact_mod_cast (hpacket ρ).2.le
    simpa only [hweightReal, mul_comm] using h
  have hAr := full_interpolation_arithmetic_estimate (H := (H n : ℝ)) (θ := (θ : ℝ))
    (w₀ := (w₀ : ℝ)) (wstar := (wstar : ℝ)) hD T q N (den ^ K) (pow_pos hden _)
    y c (powerCentres_cleared α den K hdenα) hq (rationalCentres_cleared hD p q hq K)
    centre row column hcap hf (show (0 : ℝ) < wstar by exact_mod_cast hwstar) hminReal
    (fun ρ => by exact_mod_cast hhh ρ) hcolAr hrowAr
  let rowWeight : ℝ := ∑ ρ, ∑ i, (w i : ℝ) * (β ρ i : ℝ)
  let b := rowWeight / (Fintype.card ι * (H n : ℝ))
  let Ear := criterionArithmeticError (fun i => (w i : ℝ)) F v₀ θ w₀ wstar (Real.log (den : ℝ)) K
  let Dmean := ((Real.log ‖(mat.map (embedding D)).det‖ + Real.log ‖(mat.map (conjugateEmbedding D)).det‖) / 2) /
    (Fintype.card ι * (H n : ℝ))
  have hrowSum : (∑ ρ, ∑ i, (row ρ i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉ : ℤ)) = rowWeight := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hweightReal]
    change (row ρ i.succ : ℝ) * (w i : ℝ) = (w i : ℝ) * (row ρ i.succ : ℝ)
    ring
  have hdenCost := rational_truncation_denominator_cost w hw (hHpos n).le hF.le hv₀
  have hdenCost' : Real.log ((∏ i, Nat.lcmUpto (T i) ^ N i : ℕ) : ℝ) / (H n : ℝ) ≤
      (Real.log 4 + 4) * ((F : ℝ) * m / (v₀ : ℝ) + ∑ i, 1 / (w i : ℝ)) := by
    apply (div_le_iff₀ hHn).mpr
    apply hdenCost.trans_eq
    ring
  have hcost : interpolationArithmeticCost T q N (den ^ K) row (H n) θ w₀ wstar /
      (Fintype.card ι * (H n : ℝ)) ≤ 1 - b + Ear := by
    unfold interpolationArithmeticCost
    rw [Nat.cast_pow, Real.log_pow, hrowSum,
      normalize_arithmetic_cost hmass hHn (show (0 : ℝ) < w₀ by exact_mod_cast hw₀)
        (show (0 : ℝ) < wstar by exact_mod_cast hwstar)]
    dsimp [b, Ear, criterionArithmeticError]
    linarith only [hdenCost']
  have hlower : -(1 - b) - Ear ≤ Dmean := by
    have h := div_le_div_of_nonneg_right hAr (mul_pos hmass hHn).le
    change -interpolationArithmeticCost T q N (den ^ K) row (H n) θ w₀ wstar /
      (Fintype.card ι * (H n : ℝ)) ≤ Dmean at h
    rw [neg_div] at h
    linarith only [h, hcost]
  let err : ι → Fin m → ℂ := fun ρ i => approximationCentreError γ x (p i) (q i) (centre ρ)
  have herr : ∀ ρ i, ‖err ρ i‖ ≤ E * Real.exp (-ν * (w i : ℝ)) := by
    intro ρ i
    have he := approximationCentreError_bound γ (hq i) (centre ρ).isLt.le
      (show 0 ≤ ν by linarith) (hpq i).2.2.2
    have he' := he.trans (mul_le_mul_of_nonneg_right (show (K : ℝ) * ‖γ‖ * Real.exp ν ≤ E from le_max_right _ _)
      (Real.exp_pos _).le)
    simpa only [err, hweightReal] using he'
  have hmapplus := map_quadraticInterpolationMatrix_eq_translated D T y c centre row column
    (embedding D).toRingHom (fun r => (embedding D).commutes r) ω err
    (fun ρ => embedding_powerCentres α K ω hα (centre ρ))
    (fun ρ i => embedding_rationalCentres_eq_translated hD p q K x (centre ρ) i)
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hmapplus
  let σ : Algebra D →+* ℂ := (embedding D).toRingHom.comp (starRingEnd (Algebra D))
  have hσ : ∀ r : ℚ, σ (algebraMap ℚ (Algebra D) r) = (r : ℂ) := by
    intro r
    exact map_ratCast σ r
  have hmapminus := map_quadraticInterpolationMatrix_eq_translated D T y c centre row column σ hσ
    (-ω) (fun ρ i => -err ρ i)
    (fun ρ => conjugateEmbedding_powerCentres α K ω hα hnorm (centre ρ))
    (fun ρ i => by
      change conjugateEmbedding D (rationalCentres D p q K (centre ρ) i) = _
      simpa only [err, γ, ω, approximationCentreError_neg] using
        conjugateEmbedding_rationalCentres_eq_translated hD p q K x (centre ρ) i)
  change mat.map (conjugateEmbedding D) = _ at hmapminus
  have hsC : ∀ ρ, (s ρ : ℝ) + 1 ≤ choiceConstant * (H n : ℝ) := by
    intro ρ
    have hsQ : (s ρ : ℚ) ≤ H n / v₀ := (hpacket ρ).1.le
    have hs : (s ρ : ℝ) ≤ (H n : ℝ) / (v₀ : ℝ) := by
      have hs' := (Rat.cast_le (K := ℝ)).mpr hsQ
      simpa only [Rat.cast_natCast, Rat.cast_div] using hs'
    have hv : (0 : ℝ) < v₀ := Rat.cast_pos.mpr hv₀
    have hws : (0 : ℝ) < wstar := by exact_mod_cast hwstar
    dsimp [choiceConstant]
    simp only [div_eq_mul_inv] at hs
    have hp := mul_nonneg (inv_nonneg.mpr hws.le) hHn.le
    linear_combination hs + hp + hdegreeOne
  have hNC : ∀ i, (N i : ℝ) + 1 ≤ choiceConstant * (H n : ℝ) := by
    intro i
    have hn : (N i : ℝ) ≤ (H n : ℝ) / (w i : ℝ) := by
      exact_mod_cast Nat.floor_le (div_nonneg (hHpos n).le (hw i).le)
    have hwi : (wstar : ℝ) ≤ (w i : ℝ) := by exact_mod_cast hmin i
    have hws : (0 : ℝ) < wstar := by exact_mod_cast hwstar
    have hv : (0 : ℝ) < v₀ := Rat.cast_pos.mpr hv₀
    have hi := one_div_le_one_div_of_le hws hwi
    have hp := mul_le_mul_of_nonneg_left hi hHn.le
    dsimp [choiceConstant]
    simp only [div_eq_mul_inv] at hn hp
    have hp' := mul_nonneg (inv_nonneg.mpr hv.le) hHn.le
    linear_combination hn + hp + hp' + hdegreeOne
  have hchoiceConstant : 0 < choiceConstant := by
    dsimp [choiceConstant]
    have hv : (0 : ℝ) < v₀ := Rat.cast_pos.mpr hv₀
    have hws : (0 : ℝ) < wstar := by exact_mod_cast hwstar
    positivity
  have hAnalytic := fun (z : ℂ) (error : ι → Fin m → ℂ)
      (hz : ∀ ρ, ‖(centre ρ : ℂ) * z‖ + 1 ≤ Rdisk / 2)
      (he : ∀ ρ i, ‖error ρ i‖ ≤ E * Real.exp (-ν * (w i : ℝ)))
      (hne : (Matrix.of (fun ρ τ => translatedInterpolationEntry m (h τ) (centre ρ) (s ρ) z T (l τ) (β ρ) (error ρ))).det ≠ 0) =>
    normalized_translated_det_bound T N β s h (fun ρ => (centre ρ : ℕ)) z l error
      hcap w hw hA.le (hHpos n) hη.le hF hv₀ hw₀ hwstar hmin hE (by linarith) hRdisk hz
      hhh hll htrunc hjet he hchoiceConstant hsC hNC hne
  have hupperplus := hAnalytic ω err
    (fun ρ => centre_radius_bound ω hK (centre ρ).isLt) herr
    (by rw [← hmapplus]; exact hplus)
  have hupperminus := hAnalytic (-ω) (fun ρ i => -err ρ i)
    (fun ρ => by simpa only [mul_neg, norm_neg] using centre_radius_bound ω hK (centre ρ).isLt)
    (fun ρ i => by simpa only [norm_neg] using herr ρ i)
    (by rw [← hmapminus]; exact hminus)
  rw [← hmapplus] at hupperplus
  rw [← hmapminus] at hupperminus
  let δ := determinantRemainder (Fintype.card ι) / (H n : ℝ) +
    (((2 * m + 1 : ℕ) : ℝ)) * Real.log (choiceConstant * (H n : ℝ)) / (H n : ℝ)
  let Lsave := η ^ 2 * (Fintype.card ι : ℝ) /
    ((ImaginaryQuadratic.monomialIndices w (A * H n)).card * (H n : ℝ))
  have hb0 : 0 ≤ b := by
    apply div_nonneg _ (mul_pos hmass hHn).le
    exact Finset.sum_nonneg (fun ρ _ => Finset.sum_nonneg (fun i _ =>
      mul_nonneg (show (0 : ℝ) ≤ w i by exact_mod_cast (hw i).le) (Nat.cast_nonneg _)))
  have hbθ : b ≤ (θ : ℝ) := by
    apply (div_le_iff₀ (mul_pos hmass hHn)).mpr
    calc
      rowWeight ≤ ∑ _ρ : ι, (θ : ℝ) * (H n : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact_mod_cast hrowWeight ρ
      _ = _ := by simp; ring
  have hupper : Dmean ≤ translationCost ν E F v₀ wstar + holomorphicCost Rdisk w₀ wstar v₀ + δ + ν * b +
      max (-(Real.log 2 / 4) * Lsave) (-ν * ((A : ℝ) * (1 - η))) := by
    dsimp [Dmean]
    have heq : ((Real.log ‖(mat.map (embedding D)).det‖ + Real.log ‖(mat.map (conjugateEmbedding D)).det‖) / 2) /
        (Fintype.card ι * (H n : ℝ)) =
      (Real.log ‖(mat.map (embedding D)).det‖ / (Fintype.card ι * (H n : ℝ)) +
        Real.log ‖(mat.map (conjugateEmbedding D)).det‖ / (Fintype.card ι * (H n : ℝ))) / 2 := by ring
    rw [heq]
    dsimp [δ, b, rowWeight, Lsave, v₀, w₀, K, mat] at hupperplus hupperminus ⊢
    push_cast at hupperplus hupperminus ⊢
    linarith only [hupperplus, hupperminus]
  have hδ : δ < ε := by simpa only [δ, hcard] using hdegree
  change Ear + translationCost ν E F v₀ wstar + holomorphicCost Rdisk w₀ wstar v₀ < 3 * ε at hsmall
  have hlarge' : ν * (θ : ℝ) + 3 < (Real.log 2 / 4) * Lsave := by
    simpa only [Lsave, hcard] using hlarge
  apply determinant_estimates_incompatible_with_row_weight (ν := ν) (A := (A : ℝ))
    (η := η) (θ := (θ : ℝ)) (b := b) (c := Real.log 2 / 4) (L := Lsave)
    (Ear := Ear) (Etr := translationCost ν E F v₀ wstar)
    (Ehol := holomorphicCost Rdisk w₀ wstar v₀) (δ := δ) (D := Dmean)
    (by linarith) hb0 hbθ ?_ ?_ hlower hupper
  · have he := min_le_left (gap / 8) (1 / 8 : ℝ)
    change ε ≤ gap / 8 at he
    dsimp [gap] at he
    linarith only [hsmall, hδ, he, hε]
  · have he := min_le_right (gap / 8) (1 / 8 : ℝ)
    change ε ≤ 1 / 8 at he
    linarith only [hsmall, hδ, he, hlarge']

end QuadraticField
