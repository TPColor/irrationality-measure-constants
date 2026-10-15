import QuadraticFieldCriterion.QuadraticOrder
import QuadraticFieldCriterion.LogDenominators
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! # Clearing monomial coefficients by rescaling the transverse variables -/

namespace QuadraticField

def coefficientSubring {σ R : Type*} [CommRing R] (S : Subring R) :
    Subring (MvPowerSeries σ R) where
  carrier := {f | ∀ α, MvPowerSeries.coeff α f ∈ S}
  zero_mem' := by intro α; simp
  one_mem' := by
    intro α
    classical
    simp only [MvPowerSeries.coeff_one]
    split <;> simp
  add_mem' := by intro f g hf hg α; simpa using S.add_mem (hf α) (hg α)
  neg_mem' := by intro f hf α; simpa using S.neg_mem (hf α)
  mul_mem' := by
    intro f g hf hg α
    classical
    rw [MvPowerSeries.coeff_mul]
    exact S.sum_mem (fun β _ => S.mul_mem (hf β.1) (hg β.2))

theorem C_mem_coefficientSubring {σ R : Type*} [CommRing R]
    (S : Subring R) {r : R} (hr : r ∈ S) :
    MvPowerSeries.C r ∈ coefficientSubring (σ := σ) S := by
  intro α
  classical
  simp only [MvPowerSeries.coeff_C]
  split <;> simp_all

theorem X_mem_coefficientSubring {σ R : Type*} [CommRing R]
    (S : Subring R) (i : σ) :
    MvPowerSeries.X i ∈ coefficientSubring S := by
  intro α
  classical
  simp only [MvPowerSeries.coeff_X]
  split <;> simp

theorem rescale_C {σ R : Type*} [CommRing R] (a : σ → R) (r : R) :
    MvPowerSeries.rescale a (MvPowerSeries.C r) = MvPowerSeries.C r := by
  ext α
  classical
  simp only [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst α; simp
  · simp

theorem rescale_X {σ R : Type*} [CommRing R] (a : σ → R) (i : σ) :
    MvPowerSeries.rescale a (MvPowerSeries.X i) =
      MvPowerSeries.C (a i) * MvPowerSeries.X i := by
  ext α
  classical
  simp only [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_X]
  split_ifs with h
  · subst α; simp
  · simp

/-- Clearing each rescaled variable clears every monomial coefficient, with
the precise row factor from the rescaling and column factor from the degree. -/
theorem cleared_monomial_coefficient_mem {σ R : Type*} [Fintype σ] [CommRing R]
    (S : Subring R) (a d : σ → R) (F : σ → MvPowerSeries σ R)
    (hF : ∀ i, MvPowerSeries.C (d i) * MvPowerSeries.rescale a (F i) ∈ coefficientSubring S)
    (ℓ : σ → ℕ) (β : σ →₀ ℕ) :
    (∏ i, d i ^ ℓ i) * (β.prod fun i n => a i ^ n) *
      MvPowerSeries.coeff β (∏ i, F i ^ ℓ i) ∈ S := by
  classical
  have hmem : (∏ i, (MvPowerSeries.C (d i) * MvPowerSeries.rescale a (F i)) ^ ℓ i) ∈
      coefficientSubring S :=
    (coefficientSubring S).prod_mem (fun i _ => (coefficientSubring S).pow_mem (hF i) _)
  have heq : (∏ i, (MvPowerSeries.C (d i) * MvPowerSeries.rescale a (F i)) ^ ℓ i) =
      MvPowerSeries.C (∏ i, d i ^ ℓ i) * MvPowerSeries.rescale a (∏ i, F i ^ ℓ i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  have h := hmem β
  rw [heq, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_rescale] at h
  simpa only [mul_assoc] using h

theorem rescale_of_single_support {σ R : Type*} [CommRing R]
    (a : σ → R) (i : σ) (ha : a i = 1) (f : MvPowerSeries σ R)
    (hsupport : ∀ α, MvPowerSeries.coeff α f ≠ 0 → α = Finsupp.single i (α i)) :
    MvPowerSeries.rescale a f = f := by
  classical
  ext α
  rw [MvPowerSeries.coeff_rescale]
  by_cases hα : MvPowerSeries.coeff α f = 0
  · simp [hα]
  · rw [hsupport α hα]
    simp [ha]

noncomputable def rationalTruncatedLog (m T : ℕ) : MvPowerSeries (Fin (m + 1)) ℚ :=
  fun α => if α 0 < T ∧ α = Finsupp.single 0 (α 0) then
    (-1 : ℚ) ^ (α 0 + 1) / (α 0 : ℚ) else 0

noncomputable def quadraticTruncatedLog (D : ℤ) (m T : ℕ) :
    MvPowerSeries (Fin (m + 1)) (Algebra D) :=
  MvPowerSeries.map (algebraMap ℚ (Algebra D)) (rationalTruncatedLog m T)

theorem exists_integer_scaled_rationalTruncatedLog_coefficient (m T : ℕ)
    (α : Fin (m + 1) →₀ ℕ) :
    ∃ z : ℤ, (Nat.lcmUpto T : ℚ) *
      MvPowerSeries.coeff α (rationalTruncatedLog m T) = (z : ℚ) := by
  classical
  change ∃ z : ℤ, (Nat.lcmUpto T : ℚ) *
    (if α 0 < T ∧ α = Finsupp.single 0 (α 0) then
      (-1 : ℚ) ^ (α 0 + 1) / (α 0 : ℚ) else 0) = (z : ℚ)
  split_ifs with h
  · by_cases hk : α 0 = 0
    · exact ⟨0, by simp [hk]⟩
    have hd : α 0 ∣ Nat.lcmUpto T :=
      Finset.dvd_lcm (by simp [Finset.mem_Icc, Nat.one_le_iff_ne_zero, hk, h.1.le])
    obtain ⟨a, ha⟩ := hd
    refine ⟨(-1 : ℤ) ^ (α 0 + 1) * (a : ℤ), ?_⟩
    rw [ha]
    push_cast
    have hk' : (α 0 : ℚ) ≠ 0 := by exact_mod_cast hk
    field_simp
  · exact ⟨0, by simp⟩

theorem scaled_quadraticTruncatedLog_mem (D : ℤ) (m T : ℕ) :
    MvPowerSeries.C (Nat.lcmUpto T : Algebra D) * quadraticTruncatedLog D m T ∈
      coefficientSubring (integerOrder D) := by
  intro α
  obtain ⟨z, hz⟩ := exists_integer_scaled_rationalTruncatedLog_coefficient m T α
  rw [MvPowerSeries.coeff_C_mul, quadraticTruncatedLog, MvPowerSeries.coeff_map]
  have heq : (Nat.lcmUpto T : Algebra D) *
      (algebraMap ℚ (Algebra D)) (MvPowerSeries.coeff α (rationalTruncatedLog m T)) =
      (z : Algebra D) := by
    have h := congrArg (algebraMap ℚ (Algebra D)) hz
    simpa using h
  rw [heq]
  exact intCast_mem (integerOrder D) z

theorem rescale_quadraticTruncatedLog (D : ℤ) (m T : ℕ)
    (a : Fin (m + 1) → Algebra D) (ha : a 0 = 1) :
    MvPowerSeries.rescale a (quadraticTruncatedLog D m T) = quadraticTruncatedLog D m T := by
  apply rescale_of_single_support a 0 ha
  intro α hα
  by_contra h
  apply hα
  rw [quadraticTruncatedLog, MvPowerSeries.coeff_map]
  change (algebraMap ℚ (Algebra D))
    (if α 0 < T ∧ α = Finsupp.single 0 (α 0) then _ else 0) = 0
  simp [h]

theorem cleared_additiveVariable_mem {σ R : Type*} [Field R]
    (S : Subring R) (a : σ → R) (i : σ) (q d c : R) (G : MvPowerSeries σ R)
    (hq : q ≠ 0) (hqS : q ∈ S) (hdS : d ∈ S) (hc : q * c ∈ S)
    (ha : a i = q⁻¹) (hG : MvPowerSeries.rescale a G = G)
    (hdG : MvPowerSeries.C d * G ∈ coefficientSubring S) :
    MvPowerSeries.C (q * d) * MvPowerSeries.rescale a
      (MvPowerSeries.C c + G + MvPowerSeries.X i) ∈ coefficientSubring S := by
  let C := MvPowerSeries.C (σ := σ) (R := R)
  have hqc : C q * C c = C (q * c) := (map_mul C q c).symm
  have hqi : C q * C (q⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  rw [map_add, map_add, rescale_C, hG, rescale_X, ha, map_mul]
  have heq : C q * C d * (C c + G + C (q⁻¹) * MvPowerSeries.X i) =
      C d * C (q * c) + C q * (C d * G) + C d * MvPowerSeries.X i := by
    calc
      _ = C d * (C q * C c) + C q * (C d * G) +
          C d * (C q * C (q⁻¹)) * MvPowerSeries.X i := by ring
      _ = _ := by rw [hqc, hqi, mul_one]
  rw [heq]
  exact (coefficientSubring S).add_mem
    ((coefficientSubring S).add_mem
      ((coefficientSubring S).mul_mem (C_mem_coefficientSubring S hdS) (C_mem_coefficientSubring S hc))
      ((coefficientSubring S).mul_mem (C_mem_coefficientSubring S hqS) hdG))
      ((coefficientSubring S).mul_mem (C_mem_coefficientSubring S hdS)
        (X_mem_coefficientSubring S i))

noncomputable def quadraticLocalVariables (D : ℤ) {m : ℕ}
    (y : Algebra D) (c : Fin m → Algebra D) (T : Fin m → ℕ) :
    Fin (m + 1) → MvPowerSeries (Fin (m + 1)) (Algebra D) :=
  Fin.cases (MvPowerSeries.C y * (1 + MvPowerSeries.X 0))
    (fun i => MvPowerSeries.C (c i) + quadraticTruncatedLog D m (T i) + MvPowerSeries.X i.succ)

/-- Every full interpolation entry is in the quadratic order after the
explicit column scaling and the inverse-denominator row scaling. -/
theorem cleared_quadratic_monomial_coefficient_mem {D : ℤ} (hD : ¬ IsSquare D)
    {m : ℕ} (y : Algebra D) (c : Fin m → Algebra D) (T q : Fin m → ℕ)
    (s : ℕ) (hy : (s : Algebra D) * y ∈ integerOrder D)
    (hq : ∀ i, 0 < q i) (hc : ∀ i, (q i : Algebra D) * c i ∈ integerOrder D)
    (ℓ : Fin (m + 1) → ℕ) (β : Fin (m + 1) →₀ ℕ) :
    (s : Algebra D) ^ ℓ 0 *
      (∏ i, ((q i : Algebra D) * (Nat.lcmUpto (T i) : Algebra D)) ^ ℓ i.succ) *
      (∏ i, ((q i : Algebra D)⁻¹) ^ β i.succ) *
      MvPowerSeries.coeff β (∏ i, quadraticLocalVariables D y c T i ^ ℓ i) ∈ integerOrder D := by
  classical
  let : Fact (¬ IsSquare (D : ℚ)) := ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  let a : Fin (m + 1) → Algebra D := Fin.cases 1 (fun i => (q i : Algebra D)⁻¹)
  let d : Fin (m + 1) → Algebra D :=
    Fin.cases (s : Algebra D) (fun i => (q i : Algebra D) * Nat.lcmUpto (T i))
  have hvars : ∀ i, MvPowerSeries.C (d i) *
      MvPowerSeries.rescale a (quadraticLocalVariables D y c T i) ∈
      coefficientSubring (integerOrder D) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [quadraticLocalVariables, Fin.cases_zero, d, map_mul, map_add, map_one,
        rescale_C, rescale_X, a, Fin.cases_zero, one_mul]
      rw [← mul_assoc, ← map_mul]
      exact (coefficientSubring (integerOrder D)).mul_mem
        (C_mem_coefficientSubring _ hy)
        ((coefficientSubring (integerOrder D)).add_mem (Subring.one_mem _)
          (X_mem_coefficientSubring _ 0))
    · exact cleared_additiveVariable_mem (integerOrder D) a j.succ (q j)
        (Nat.lcmUpto (T j)) (c j) (quadraticTruncatedLog D m (T j))
        (by exact_mod_cast (hq j).ne') (natCast_mem _ _) (natCast_mem _ _) (hc j)
        rfl (rescale_quadraticTruncatedLog D m (T j) a rfl)
        (scaled_quadraticTruncatedLog_mem D m (T j))
  have h := cleared_monomial_coefficient_mem (integerOrder D) a d
    (quadraticLocalVariables D y c T) hvars ℓ β
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_succ,
    Fin.prod_univ_succ] at h
  simpa only [a, d, Fin.cases_zero, Fin.cases_succ, one_pow, one_mul] using h

/-- One denominator works for every selected column bounded by `N`. -/
theorem uniformly_cleared_quadratic_coefficient_mem {D : ℤ} (hD : ¬ IsSquare D)
    {m : ℕ} (y : Algebra D) (c : Fin m → Algebra D) (T q N : Fin m → ℕ)
    (s : ℕ) (hy : (s : Algebra D) * y ∈ integerOrder D)
    (hq : ∀ i, 0 < q i) (hc : ∀ i, (q i : Algebra D) * c i ∈ integerOrder D)
    (ℓ : Fin (m + 1) → ℕ) (hℓ : ∀ i, ℓ i.succ ≤ N i) (β : Fin (m + 1) →₀ ℕ) :
    (∏ i, (Nat.lcmUpto (T i) : Algebra D) ^ N i) * (s : Algebra D) ^ ℓ 0 *
      (∏ i, (q i : Algebra D) ^ ℓ i.succ) *
      (∏ i, ((q i : Algebra D)⁻¹) ^ β i.succ) *
      MvPowerSeries.coeff β (∏ i, quadraticLocalVariables D y c T i ^ ℓ i) ∈ integerOrder D := by
  classical
  have h := cleared_quadratic_monomial_coefficient_mem hD y c T q s hy hq hc ℓ β
  simp only [mul_pow, Finset.prod_mul_distrib] at h
  have hmult : (∏ i, (Nat.lcmUpto (T i) : Algebra D) ^ (N i - ℓ i.succ)) ∈ integerOrder D :=
    (integerOrder D).prod_mem (fun i _ => (integerOrder D).pow_mem (natCast_mem _ _) _)
  have hprod : (∏ i, (Nat.lcmUpto (T i) : Algebra D) ^ (N i - ℓ i.succ)) *
      (∏ i, (Nat.lcmUpto (T i) : Algebra D) ^ ℓ i.succ) =
      ∏ i, (Nat.lcmUpto (T i) : Algebra D) ^ N i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← pow_add, Nat.sub_add_cancel (hℓ i)]
  have hmem := (integerOrder D).mul_mem hmult h
  convert hmem using 1
  rw [← hprod]
  ring

theorem cleared_powers_mem_integerOrder (D : ℤ) (α : Algebra D) (s N j : ℕ)
    (hα : (s : Algebra D) * α ∈ integerOrder D) (hj : j ≤ N) :
    (s : Algebra D) ^ N * α ^ j ∈ integerOrder D := by
  have h := (integerOrder D).mul_mem ((integerOrder D).pow_mem hα j)
    ((integerOrder D).pow_mem (natCast_mem _ s) (N - j))
  have heq : (s : Algebra D) ^ N * α ^ j =
      ((s : Algebra D) * α) ^ j * (s : Algebra D) ^ (N - j) := by
    rw [mul_pow]
    calc
      _ = (s : Algebra D) ^ (j + (N - j)) * α ^ j := by rw [Nat.add_sub_of_le hj]
      _ = _ := by rw [pow_add]; ring
  rwa [heq]

theorem map_quadraticTruncatedLog (D : ℤ) (m T : ℕ)
    (φ : Algebra D →+* ℂ) (hφ : ∀ r : ℚ, φ (algebraMap ℚ (Algebra D) r) = (r : ℂ)) :
    MvPowerSeries.map φ (quadraticTruncatedLog D m T) = ImaginaryQuadratic.truncatedLog m T := by
  classical
  ext α
  rw [MvPowerSeries.coeff_map, quadraticTruncatedLog, MvPowerSeries.coeff_map, hφ]
  change (((if α 0 < T ∧ α = Finsupp.single 0 (α 0) then
    (-1 : ℚ) ^ (α 0 + 1) / (α 0 : ℚ) else 0) : ℚ) : ℂ) =
      if α 0 < T then (if α = Finsupp.single 0 (α 0) then
        (-1 : ℂ) ^ (α 0 + 1) / (α 0 : ℂ) else 0) else 0
  by_cases hT : α 0 < T
  · rw [ite_eq_left hT]
    by_cases hα : α = Finsupp.single 0 (α 0)
    · rw [ite_eq_left ⟨hT, hα⟩, ite_eq_left hα]
      push_cast
      rfl
    · rw [ite_eq_right (fun h => hα h.2), ite_eq_right hα]
      simp
  · rw [ite_eq_right (fun h => hT h.1), ite_eq_right hT]
    simp

theorem map_quadraticLocalVariables (D : ℤ) {m K : ℕ}
    (T : Fin m → ℕ) (y : Fin K → Algebra D) (c : Fin K → Fin m → Algebra D)
    (φ : Algebra D →+* ℂ) (hφ : ∀ r : ℚ, φ (algebraMap ℚ (Algebra D) r) = (r : ℂ))
    (j : Fin K) (i : Fin (m + 1)) :
    MvPowerSeries.map φ (quadraticLocalVariables D (y j) (c j) T i) =
      ImaginaryQuadratic.truncatedLocalVariables T (fun j => φ (y j))
        (fun j i => φ (c j i)) j i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [quadraticLocalVariables, ImaginaryQuadratic.truncatedLocalVariables]
  · simp only [quadraticLocalVariables, ImaginaryQuadratic.truncatedLocalVariables,
      Fin.cases_succ, map_add, MvPowerSeries.map_C, MvPowerSeries.map_X,
      map_quadraticTruncatedLog D m _ φ hφ]
    ring

noncomputable def quadraticInterpolationMatrix (D : ℤ) {m K : ℕ} {ι : Type*}
    (T : Fin m → ℕ) (y : Fin K → Algebra D) (c : Fin K → Fin m → Algebra D)
    (centre : ι → Fin K) (row : ι → (Fin (m + 1) →₀ ℕ))
    (column : ι → (Fin (m + 1) →₀ ℕ)) : Matrix ι ι (Algebra D) :=
  fun i j => MvPowerSeries.coeff (row i)
    (∏ k, quadraticLocalVariables D (y (centre i)) (c (centre i)) T k ^ column j k)

theorem map_quadraticInterpolationMatrix (D : ℤ) {m K : ℕ} {ι : Type*}
    (T : Fin m → ℕ) (y : Fin K → Algebra D) (c : Fin K → Fin m → Algebra D)
    (centre : ι → Fin K) (row column : ι → (Fin (m + 1) →₀ ℕ))
    (φ : Algebra D →+* ℂ) (hφ : ∀ r : ℚ, φ (algebraMap ℚ (Algebra D) r) = (r : ℂ)) :
    (quadraticInterpolationMatrix D T y c centre row column).map φ =
      Matrix.of (fun i j => MvPowerSeries.coeff (row i)
        (MvPolynomial.eval₂ MvPowerSeries.C
          (ImaginaryQuadratic.truncatedLocalVariables T (fun j => φ (y j))
            (fun j k => φ (c j k)) (centre i)) (MvPolynomial.monomial (column j) 1))) := by
  classical
  ext i j
  change φ (MvPowerSeries.coeff (row i) _) = _
  rw [← MvPowerSeries.coeff_map]
  simp only [map_prod, map_pow, map_quadraticLocalVariables D T y c φ hφ,
    MvPolynomial.eval₂_monomial, map_one, one_mul, Matrix.of_apply,
    Finsupp.prod_fintype _ _ (fun k => pow_zero _)]

noncomputable def interpolationRowScale {m : ℕ} (q : Fin m → ℕ)
    (β : Fin (m + 1) →₀ ℕ) : ℚ := ∏ i, ((q i : ℚ)⁻¹) ^ β i.succ

noncomputable def interpolationColumnScale {m : ℕ} (T q N : Fin m → ℕ) (s : ℕ)
    (ℓ : Fin (m + 1) →₀ ℕ) : ℚ :=
  (∏ i, (Nat.lcmUpto (T i) : ℚ) ^ N i) * (s : ℚ) ^ ℓ 0 * ∏ i, (q i : ℚ) ^ ℓ i.succ

/-- The arithmetic norm lower bound for the full interpolation matrix,
including the common logarithm denominator and inverse row factors. -/
theorem interpolation_matrix_norm_lower_bound {D : ℤ} (hD : ¬ IsSquare D)
    {m K : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T q N : Fin m → ℕ) (s : ℕ) (hs : 0 < s)
    (y : Fin K → Algebra D) (c : Fin K → Fin m → Algebra D)
    (hy : ∀ j, (s : Algebra D) * y j ∈ integerOrder D)
    (hq : ∀ i, 0 < q i) (hc : ∀ j i, (q i : Algebra D) * c j i ∈ integerOrder D)
    (centre : ι → Fin K) (row column : ι → (Fin (m + 1) →₀ ℕ))
    (hcolumn : ∀ j i, column j i.succ ≤ N i)
    (hne : (quadraticInterpolationMatrix D T y c centre row column).det ≠ 0) :
    1 ≤ |(((∏ i, interpolationRowScale q (row i)) *
        ∏ j, interpolationColumnScale T q N s (column j) : ℚ) : ℝ)| ^ 2 *
      (‖((quadraticInterpolationMatrix D T y c centre row column).map (embedding D)).det‖ *
       ‖((quadraticInterpolationMatrix D T y c centre row column).map (conjugateEmbedding D)).det‖) := by
  classical
  let : Fact (¬ IsSquare (D : ℚ)) := ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  apply scaled_norm_det_lower_bound hD _ (fun i => interpolationRowScale q (row i))
    (fun j => interpolationColumnScale T q N s (column j)) _ _ _ hne
  · intro i
    apply ne_of_gt
    exact Finset.prod_pos (fun k _ => pow_pos (inv_pos.mpr (by exact_mod_cast hq k)) _)
  · intro j
    apply ne_of_gt
    have hs' : (0 : ℚ) < s := by exact_mod_cast hs
    have hd : 0 < ∏ i, (Nat.lcmUpto (T i) : ℚ) ^ N i :=
      Finset.prod_pos (fun k _ => pow_pos (by exact_mod_cast Nat.lcmUpto_pos (T k)) _)
    have hq' : 0 < ∏ i, (q i : ℚ) ^ column j i.succ :=
      Finset.prod_pos (fun k _ => pow_pos (by exact_mod_cast hq k) _)
    exact mul_pos (mul_pos hd (pow_pos hs' _)) hq'
  · intro i j
    have h := uniformly_cleared_quadratic_coefficient_mem hD
      (y (centre i)) (c (centre i)) T q N s (hy (centre i)) hq (hc (centre i))
      (fun k => column j k) (hcolumn j) (row i)
    convert h using 1
    simp only [interpolationRowScale, interpolationColumnScale, map_mul, map_prod,
      map_pow, map_inv₀, map_natCast, quadraticInterpolationMatrix]
    ring

/-- A nonzero complex interpolation minor is already a nonzero determinant
over the rational quadratic algebra. -/
theorem exists_nonzero_quadratic_interpolation_minor (D : ℤ) {m K : ℕ}
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (H : ℚ) (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ v 0 * (T i : ℚ))
    (y : Fin K → Algebra D) (c : Fin K → Fin m → Algebra D)
    (honto : ∀ target : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
        (∀ α ∈ P.support, ImaginaryQuadratic.weightedDegree w α ≤ H) ∧
        ∀ j α, ImaginaryQuadratic.weightedDegree v α < H → MvPowerSeries.coeff α
          (MvPolynomial.eval₂ MvPowerSeries.C
            (ImaginaryQuadratic.localVariables (fun j => embedding D (y j))
              (fun j i => embedding D (c j i)) j) P) = target j α) :
    ∃ f : {ρ // ρ ∈ ImaginaryQuadratic.jetIndices K v H} →
        {α // α ∈ ImaginaryQuadratic.monomialIndices w H},
      (quadraticInterpolationMatrix D T y c (fun ρ => ρ.val.1)
        (fun ρ => ρ.val.2) (fun ρ => (f ρ).val)).det ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := ImaginaryQuadratic.nonzero_truncated_minor_of_coefficient_surjectivity
    w v hw hv H T hT (fun j => embedding D (y j)) (fun j i => embedding D (c j i)) honto
  refine ⟨f, ?_⟩
  have hmap := map_quadraticInterpolationMatrix D T y c (fun ρ => ρ.val.1)
    (fun ρ => ρ.val.2) (fun ρ => (f ρ).val) (embedding D).toRingHom
    (fun r => (embedding D).commutes r)
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hmap
  have heq : ((quadraticInterpolationMatrix D T y c (fun ρ => ρ.val.1)
      (fun ρ => ρ.val.2) (fun ρ => (f ρ).val)).map (embedding D)).det ≠ 0 := by
    rw [hmap]
    simpa only [ImaginaryQuadratic.truncatedCoefficientMap_apply] using hf
  intro h
  have hdet := (embedding D).map_det
    (quadraticInterpolationMatrix D T y c (fun ρ => ρ.val.1)
      (fun ρ => ρ.val.2) (fun ρ => (f ρ).val))
  rw [h, map_zero] at hdet
  exact heq hdet.symm

noncomputable def quadraticGenerator (D : ℤ) : Algebra D := ⟨0, 2⟩

theorem quadraticGenerator_mem (D : ℤ) : quadraticGenerator D ∈ integerOrder D :=
  ⟨⟨0, 2⟩, rfl⟩

theorem embedding_quadraticGenerator (D : ℤ) :
    embedding D (quadraticGenerator D) = 2 * root D := by
  simp [embedding_apply, quadraticGenerator]

theorem conjugateEmbedding_quadraticGenerator (D : ℤ) :
    conjugateEmbedding D (quadraticGenerator D) = -(2 * root D) := by
  simp [conjugateEmbedding_apply, quadraticGenerator]

theorem additive_centre_cleared {D : ℤ} (hD : ¬ IsSquare D) (j : ℕ) (p : ℤ)
    (q : ℕ) (hq : 0 < q) :
    (q : Algebra D) * ((j : Algebra D) * quadraticGenerator D * (p : Algebra D) /
      (q : Algebra D)) ∈ integerOrder D := by
  let : Fact (¬ IsSquare (D : ℚ)) := ⟨fun h => hD (Rat.isSquare_intCast_iff.mp h)⟩
  have hq' : (q : Algebra D) ≠ 0 := by exact_mod_cast hq.ne'
  rw [mul_div_cancel₀ _ hq']
  exact (integerOrder D).mul_mem
    ((integerOrder D).mul_mem (natCast_mem _ _) (quadraticGenerator_mem D)) (intCast_mem _ _)

end QuadraticField
