import QuadraticFieldCriterion.CollisionEstimate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Counting the low-weight rows in the collision alternative -/

namespace QuadraticField

/-- Cauchy--Schwarz converts a large number of rows in a small set of
transverse indices into a lower bound for the collision mass. -/
theorem small_index_collision_bound {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (a : ι → κ) (S : Finset κ) :
    (((Finset.univ.filter (fun i => a i ∈ S)).card : ℝ) ^ 2) ≤
      collisionMass a * (S.card : ℝ) := by
  classical
  let image := Finset.univ.image a
  let s := S ∩ image
  let rows := Finset.univ.filter (fun i => a i ∈ S)
  let n : κ → ℝ := fun k => (Finset.univ.filter (fun i => a i = k)).card
  have hcount : ∑ k ∈ s, n k = (rows.card : ℝ) := by
    have h := Finset.card_eq_sum_card_image a rows
    have himage : rows.image a = s := by
      ext k
      simp only [rows, s, image, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hi, i, rfl⟩
      · rintro ⟨hk, i, rfl⟩
        exact ⟨i, hk, rfl⟩
    rw [himage] at h
    have hfib : ∀ k ∈ s, rows.filter (fun i => a i = k) =
        Finset.univ.filter (fun i => a i = k) := by
      intro k hk
      have hkS : k ∈ S := (Finset.mem_inter.mp hk).1
      ext i
      simp only [rows, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hi
        exact ⟨hi ▸ hkS, hi⟩
    have hc : (∑ k ∈ s, (rows.filter (fun i => a i = k)).card) =
        ∑ k ∈ s, (Finset.univ.filter (fun i => a i = k)).card :=
      Finset.sum_congr rfl (fun k hk => congrArg Finset.card (hfib k hk))
    rw [hc] at h
    dsimp only [n]
    exact_mod_cast h.symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s n (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hcount] at hcs
  have hsum : (∑ k ∈ s, n k ^ 2) ≤ collisionMass a := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.inter_subset_right : s ⊆ image)
      (fun k _ _ => sq_nonneg (n k))
    convert h using 1
    simp [collisionMass, n, image]
    apply Finset.sum_congr
    · ext k
      simp
    · intro k hk
      norm_cast
      congr 2
      ext i
      simp
  calc
    _ ≤ (∑ k ∈ s, n k ^ 2) * (s.card : ℝ) := hcs
    _ ≤ collisionMass a * (S.card : ℝ) := mul_le_mul hsum
      (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : s ⊆ S))
      (by positivity) (Finset.sum_nonneg (fun k _ => sq_nonneg _))

theorem collision_mass_nonneg {ι κ : Type*} [Fintype ι] (a : ι → κ) :
    0 ≤ collisionMass a := by
  classical
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

/-- This is the first alternative before inserting the simplex asymptotic. -/
theorem collision_bound_of_many_small_indices {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (a : ι → κ) (S : Finset κ) {η : ℝ} (hη : 0 ≤ η)
    (hmany : η * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => a i ∈ S)).card : ℝ)) :
    η ^ 2 * (Fintype.card ι : ℝ) ^ 2 ≤ collisionMass a * (S.card : ℝ) := by
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ η * (Fintype.card ι : ℝ)) hmany 2
  rw [mul_pow] at hsq
  exact hsq.trans (small_index_collision_bound a S)

/-- If too few rows have weight at most `r`, the total selected weight
already gives the second alternative in the determinant comparison. -/
theorem low_weight_or_large_total {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) {r η : ℝ} (hr : 0 ≤ r) :
    η * Fintype.card ι ≤ ((Finset.univ.filter (fun i => weight i ≤ r)).card : ℝ) ∨
      (1 - η) * Fintype.card ι * r ≤ ∑ i, weight i := by
  classical
  by_cases h : η * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => weight i ≤ r)).card : ℝ)
  · exact Or.inl h
  right
  let low := Finset.univ.filter (fun i => weight i ≤ r)
  let high := Finset.univ.filter (fun i => ¬ weight i ≤ r)
  have hcard : (low.card : ℝ) + high.card = Fintype.card ι := by
    exact_mod_cast Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun i => weight i ≤ r)
  have hsum : (high.card : ℝ) * r ≤ ∑ i, weight i := by
    calc
      _ = ∑ _i ∈ high, r := by simp
      _ ≤ ∑ i ∈ high, weight i := Finset.sum_le_sum (fun i hi =>
        (lt_of_not_ge (Finset.mem_filter.mp hi).2).le)
      _ ≤ ∑ i, weight i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun i _ _ => hweight i)
  have hsmall : (low.card : ℝ) < η * Fintype.card ι := lt_of_not_ge h
  have := mul_nonneg hr (le_of_lt hsmall |> sub_nonneg.mpr)
  nlinarith

/-- The two alternatives give a single uniform exponent for every term of
the finite determinant expansion. -/
theorem weight_collision_exponent_le_max {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (a : ι → κ) (weight : κ → ℝ) (S : Finset κ)
    (hweight : ∀ k, 0 ≤ weight k) {r η ν c : ℝ}
    (hr : 0 ≤ r) (hη : 0 ≤ η) (hν : 0 ≤ ν) (hc : 0 ≤ c)
    (hS : ∀ k, k ∈ S ↔ weight k ≤ r) (hcard : 0 < S.card) :
    -ν * (∑ i, weight (a i)) - c * collisionMass a ≤
      max (-c * (η ^ 2 * (Fintype.card ι : ℝ) ^ 2 / S.card))
        (-ν * ((1 - η) * Fintype.card ι * r)) := by
  have hsum : 0 ≤ ∑ i, weight (a i) := Finset.sum_nonneg (fun i _ => hweight _)
  have hmass := collision_mass_nonneg a
  rcases low_weight_or_large_total (fun i => weight (a i)) (fun i => hweight _) hr with hlow | hhigh
  · have hfilter : Finset.univ.filter (fun i => weight (a i) ≤ r) =
        Finset.univ.filter (fun i => a i ∈ S) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS]
    rw [hfilter] at hlow
    have hcoll := collision_bound_of_many_small_indices a S hη hlow
    have hcard' : (0 : ℝ) < S.card := by exact_mod_cast hcard
    have hmass' : η ^ 2 * (Fintype.card ι : ℝ) ^ 2 / S.card ≤ collisionMass a := by
      apply (div_le_iff₀ hcard').mpr
      exact hcoll
    apply le_trans _ (le_max_left _ _)
    have h₁ := mul_nonneg hν hsum
    have h₂ := mul_le_mul_of_nonneg_left hmass' hc
    linarith
  · apply le_trans _ (le_max_right _ _)
    have h₁ := mul_le_mul_of_nonneg_left hhigh hν
    have h₂ := mul_nonneg hc hmass
    linarith

end QuadraticField
