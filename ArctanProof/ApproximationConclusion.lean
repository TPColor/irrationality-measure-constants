import ArctanProof.MeasureBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Consequences of eventual approximation bounds

An eventual strict approximation bound implies irrationality and measure two.
-/

namespace ImaginaryQuadratic

def EventualStrictBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, ∀ p : ℤ, ∀ q : ℕ,
    Q ≤ q → 0 < q → (q : ℝ) ^ (-ν) < |x - (p : ℝ) / (q : ℝ)|

theorem irrational_of_eventualStrictBound {x : ℝ} (h : EventualStrictBound x) :
    Irrational x := by
  rintro ⟨r, hr⟩
  obtain ⟨Q, hQ⟩ := h 3 (by norm_num)
  have hk : (Q + 1 : ℝ) ≠ 0 := by positivity
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.pos.ne'
  have hden : Q ≤ (Q + 1) * r.den := by nlinarith [r.pos]
  have hpos : 0 < (Q + 1) * r.den := Nat.mul_pos (by omega) r.pos
  have heq : x = (((Q + 1 : ℕ) : ℤ) * r.num : ℤ) /
      (((Q + 1) * r.den : ℕ) : ℝ) := by
    rw [← hr, Rat.cast_def]
    push_cast
    field_simp
  have hbad := hQ (((Q + 1 : ℕ) : ℤ) * r.num) ((Q + 1) * r.den) hden hpos
  rw [← heq, sub_self, abs_zero] at hbad
  exact (not_lt_of_ge (Real.rpow_nonneg (by positivity) _)) hbad

/-- Fractions in a bounded real interval with bounded reduced denominators form
a finite set. This also handles the finitely many small denominators omitted
by an eventual approximation bound. -/
theorem finite_bounded_denominator (x : ℝ) (N : ℕ) :
    Set.Finite {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| ≤ 1} := by
  obtain ⟨B, hB⟩ := exists_nat_gt ((|x| + 1) * (N : ℝ))
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hf : Function.Injective f := by
    intro a b hab
    have hp := Prod.mk.inj hab
    rw [← a.num_div_den, ← b.num_div_den, hp.1, hp.2]
  have hsub : f '' {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| ≤ 1} ⊆
      Set.Icc (-(B : ℤ)) B ×ˢ Set.Icc 0 N := by
    rintro _ ⟨r, ⟨hden, herr⟩, rfl⟩
    have hr : |(r : ℝ)| ≤ |x| + 1 := by
      calc
        |(r : ℝ)| = |((r : ℝ) - x) + x| := by congr 1; ring
        _ ≤ |(r : ℝ) - x| + |x| := abs_add_le _ _
        _ ≤ |x| + 1 := by rw [abs_sub_comm]; linarith
    have hnum : (r.num : ℝ) = (r : ℝ) * (r.den : ℝ) := by
      rw [Rat.cast_def]
      have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.pos.ne'
      field_simp
    have hnumB : |(r.num : ℝ)| ≤ (B : ℝ) := by
      calc
        |(r.num : ℝ)| = |(r : ℝ)| * (r.den : ℝ) := by
          rw [hnum, abs_mul, abs_of_nonneg
            (show (0 : ℝ) ≤ r.den by exact_mod_cast Nat.zero_le r.den)]
        _ ≤ (|x| + 1) * (N : ℝ) :=
          mul_le_mul hr (by exact_mod_cast hden) (by positivity) (by positivity)
        _ ≤ B := hB.le
    have hnumZ : -(B : ℤ) ≤ r.num ∧ r.num ≤ B := by
      exact_mod_cast abs_le.mp hnumB
    exact ⟨hnumZ, Nat.zero_le _, hden⟩
  exact ((Set.finite_Icc (-(B : ℤ)) B).prod (Set.finite_Icc 0 N)).subset
    hsub |>.of_finite_image hf.injOn

theorem finite_approximations_of_eventualStrictBound {x : ℝ}
    (h : EventualStrictBound x) (ν : ℝ) (hν : 2 < ν) :
    Set.Finite {r : ℚ | |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ ν} := by
  obtain ⟨Q, hQ⟩ := h ν hν
  refine (finite_bounded_denominator x Q).subset ?_
  intro r hr
  change |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ ν at hr
  have hrpow : (r.den : ℝ) ^ (-ν) = 1 / (r.den : ℝ) ^ ν := by
    rw [Real.rpow_neg (by positivity), one_div]
  have hden : r.den < Q := by
    by_contra hn
    have hs := hQ r.num r.den (le_of_not_gt hn) r.pos
    rw [Rat.cast_def] at hr
    rw [hrpow] at hs
    exact (not_lt_of_ge hr.le) hs
  refine ⟨hden.le, hr.le.trans ?_⟩
  have hpower : (1 : ℝ) ≤ (r.den : ℝ) ^ ν :=
    Real.one_le_rpow (by exact_mod_cast r.pos) (by linarith)
  exact (div_le_one (by positivity)).mpr hpower

theorem irrationalityMeasure_eq_two_of_eventualStrictBound {x : ℝ}
    (h : EventualStrictBound x) : irrationalityMeasure x = 2 :=
  irrationalityMeasure_eq_two_of_finite (irrational_of_eventualStrictBound h)
    (finite_approximations_of_eventualStrictBound h)

end ImaginaryQuadratic
