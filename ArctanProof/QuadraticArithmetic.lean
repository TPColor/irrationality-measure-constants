import ArctanProof.ImaginaryQuadratic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # The discrete imaginary-quadratic ring

These lemmas supply the arithmetic property of `ℤ[i√d]` used to bound a
nonzero denominator-cleared determinant. No algebraic-integer assumption
or squarefreeness assumption on `d` is used.
-/

namespace ImaginaryQuadratic

def IsQuadraticInteger (d : ℕ) (z : ℂ) : Prop :=
  ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * Complex.I * (Real.sqrt (d : ℝ) : ℂ)

theorem quadraticInteger_zero (d : ℕ) : IsQuadraticInteger d 0 :=
  ⟨0, 0, by simp⟩

theorem quadraticInteger_one (d : ℕ) : IsQuadraticInteger d 1 :=
  ⟨1, 0, by simp⟩

theorem quadraticInteger_intCast (d : ℕ) (a : ℤ) : IsQuadraticInteger d a :=
  ⟨a, 0, by simp⟩

theorem quadraticInteger_add {d : ℕ} {z w : ℂ}
    (hz : IsQuadraticInteger d z) (hw : IsQuadraticInteger d w) :
    IsQuadraticInteger d (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, e, rfl⟩ := hw
  exact ⟨a + c, b + e, by push_cast; ring⟩

theorem quadraticInteger_neg {d : ℕ} {z : ℂ} (hz : IsQuadraticInteger d z) :
    IsQuadraticInteger d (-z) := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨-a, -b, by push_cast; ring⟩

theorem quadraticInteger_mul {d : ℕ} {z w : ℂ}
    (hz : IsQuadraticInteger d z) (hw : IsQuadraticInteger d w) :
    IsQuadraticInteger d (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, e, rfl⟩ := hw
  refine ⟨a * c - (d : ℤ) * b * e, a * e + b * c, ?_⟩
  have hs : (Real.sqrt (d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  push_cast
  linear_combination (b : ℂ) * e * Complex.I ^ 2 * hs +
    (b : ℂ) * e * (d : ℂ) * Complex.I_sq

theorem quadraticInteger_pow {d : ℕ} {z : ℂ} (hz : IsQuadraticInteger d z) (n : ℕ) :
    IsQuadraticInteger d (z ^ n) := by
  induction n with
  | zero => simpa using quadraticInteger_one d
  | succ n ih => simpa only [pow_succ] using quadraticInteger_mul ih hz

/-- The squared modulus of `a + bi√d` is `a² + db²`. -/
theorem norm_sq_quadratic (d : ℕ) (a b : ℤ) :
    ‖(a : ℂ) + (b : ℂ) * Complex.I * (Real.sqrt (d : ℝ) : ℂ)‖ ^ 2 =
      (a : ℝ) ^ 2 + (d : ℝ) * (b : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  nlinarith [sq_nonneg (b : ℝ)]

/-- Every nonzero element of the ring has modulus at least one. -/
theorem one_le_norm_quadraticInteger {d : ℕ} (hd : 0 < d)
    {z : ℂ} (hz : IsQuadraticInteger d z) (hne : z ≠ 0) : 1 ≤ ‖z‖ := by
  obtain ⟨a, b, rfl⟩ := hz
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hne
  have hN : (1 : ℤ) ≤ a ^ 2 + (d : ℤ) * b ^ 2 := by
    have hdZ : (1 : ℤ) ≤ d := by exact_mod_cast hd
    rcases hab with ha | hb
    · have ha2 : (1 : ℤ) ≤ a ^ 2 := by
        have h := Int.one_le_abs ha
        nlinarith [sq_abs a, sq_nonneg a]
      nlinarith [sq_nonneg b]
    · have hb2 : (1 : ℤ) ≤ b ^ 2 := by
        have h := Int.one_le_abs hb
        nlinarith [sq_abs b, sq_nonneg b]
      nlinarith [sq_nonneg a]
  have hR : (1 : ℝ) ≤ (a : ℝ) ^ 2 + (d : ℝ) * (b : ℝ) ^ 2 := by
    exact_mod_cast hN
  rw [← norm_sq_quadratic] at hR
  nlinarith [norm_nonneg
    ((a : ℂ) + (b : ℂ) * Complex.I * (Real.sqrt (d : ℝ) : ℂ))]

/-- A single positive integer clears both rational coordinates. -/
theorem exists_denominator_clear {d : ℕ} {z : ℂ}
    (hz : HasRationalCoordinates d z) :
    ∃ s : ℕ, 0 < s ∧ IsQuadraticInteger d ((s : ℂ) * z) := by
  obtain ⟨a, b, rfl⟩ := hz
  refine ⟨a.den * b.den, Nat.mul_pos a.pos b.pos,
    a.num * (b.den : ℤ), b.num * (a.den : ℤ), ?_⟩
  have ha : (a.den : ℂ) * (a : ℂ) = (a.num : ℂ) := by
    rw [Rat.cast_def]
    have h : (a.den : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
    field_simp
  have hb : (b.den : ℂ) * (b : ℂ) = (b.num : ℂ) := by
    rw [Rat.cast_def]
    have h : (b.den : ℂ) ≠ 0 := by exact_mod_cast b.pos.ne'
    field_simp
  push_cast
  linear_combination (b.den : ℂ) * ha +
    (a.den : ℂ) * Complex.I * (Real.sqrt (d : ℝ) : ℂ) * hb

/-- The ring used for denominator clearing, including nonsquarefree `d`. -/
def quadraticIntegerRing (d : ℕ) : Subring ℂ where
  carrier := {z | IsQuadraticInteger d z}
  zero_mem' := quadraticInteger_zero d
  one_mem' := quadraticInteger_one d
  add_mem' := quadraticInteger_add
  neg_mem' := quadraticInteger_neg
  mul_mem' := quadraticInteger_mul

theorem quadraticInteger_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (M : Matrix ι ι ℂ) (hM : ∀ i j, IsQuadraticInteger d (M i j)) :
    IsQuadraticInteger d M.det := by
  classical
  change M.det ∈ quadraticIntegerRing d
  rw [Matrix.det_apply']
  apply (quadraticIntegerRing d).sum_mem
  intro σ hσ
  apply (quadraticIntegerRing d).mul_mem
  · exact quadraticInteger_intCast d (Equiv.Perm.sign σ : ℤ)
  · apply (quadraticIntegerRing d).prod_mem
    intro i hi
    exact hM (σ i) i

/-- The arithmetic modulus bound applies to the entire cleared determinant. -/
theorem one_le_norm_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (hd : 0 < d) (M : Matrix ι ι ℂ)
    (hM : ∀ i j, IsQuadraticInteger d (M i j)) (hne : M.det ≠ 0) :
    1 ≤ ‖M.det‖ :=
  one_le_norm_quadraticInteger hd (quadraticInteger_det d M hM) hne

end ImaginaryQuadratic
