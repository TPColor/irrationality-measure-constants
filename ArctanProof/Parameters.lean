import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Rat.Floor

/-! # Rational parameters with a positive gap -/

namespace ImaginaryQuadratic

/-- Every real exponent above two admits rational parameters and a positive
`η` for which the determinant comparison has a positive gap. -/
theorem exists_gap_parameters (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ, ∃ η : ℝ,
      0 < θ ∧ θ < A ∧ A < B ∧ B < 1 ∧
      1 < C ∧ C * B < 1 ∧ B < C * θ ∧ C * θ < 1 ∧
      0 < η ∧ η < 1 ∧
      0 < ν * ((A : ℝ) * (1 - η) - θ) - (1 - (θ : ℝ)) := by
  have hνpos : 0 < ν := by linarith
  have hinv : 1 / ν < (1 / 2 : ℝ) := by
    apply (div_lt_div_iff₀ hνpos (by norm_num)).mpr
    linarith
  obtain ⟨b, hb0, hb1⟩ := exists_rat_btwn
    (show (1 / 2 : ℝ) < 1 - 1 / ν by linarith)
  have hbposR : (0 : ℝ) < b := by linarith
  have hbpos : (0 : ℚ) < b := by exact_mod_cast hbposR
  have hbdouble : (1 : ℚ) < 2 * b := by
    have : (1 : ℝ) < 2 * (b : ℝ) := by linarith
    exact_mod_cast this
  have hblt : b < 1 := by
    have : (b : ℝ) < 1 := by have := one_div_pos.mpr hνpos; linarith
    exact_mod_cast this
  have hbν : 0 < ν * (1 - (b : ℝ)) - 1 := by
    have h := (div_lt_iff₀ hνpos).mp (show 1 / ν < 1 - (b : ℝ) by linarith)
    nlinarith
  have hb2 : (0 : ℚ) < b ^ 2 := sq_pos_of_pos hbpos
  have hratio : (0 : ℚ) < (2 * b - 1) / b ^ 2 := div_pos (by linarith) hb2
  obtain ⟨δ, hδpos, hδ⟩ := exists_between
    (show (0 : ℚ) < min 1 ((2 * b - 1) / b ^ 2) from lt_min (by norm_num) hratio)
  have hδ1 : δ < 1 := hδ.trans_le (min_le_left _ _)
  have hδratio : δ * b ^ 2 < 2 * b - 1 :=
    (lt_div_iff₀ hb2).mp (hδ.trans_le (min_le_right _ _))
  let θ : ℚ := 1 - δ
  let A : ℚ := 1 - b * δ
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθA : θ < A := by dsimp [θ, A]; nlinarith
  have hA : 0 < A := hθ.trans hθA
  have hA1 : A < 1 := by dsimp [A]; nlinarith
  have hAsq : A ^ 2 < θ := by
    have h := mul_lt_mul_of_pos_right hδratio hδpos
    dsimp [A, θ]
    nlinarith
  have hgap : 0 < ν * ((A : ℝ) - θ) - (1 - (θ : ℝ)) := by
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδpos
    have h := mul_pos hbν hδR
    dsimp [A, θ]
    push_cast
    nlinarith
  have hCwindow : A / θ < 1 / A := by
    apply (div_lt_div_iff₀ hθ hA).mpr
    nlinarith
  obtain ⟨C, hClo, hChi⟩ := exists_between hCwindow
  have hC1 : 1 < C := by
    have : 1 < A / θ := (lt_div_iff₀ hθ).mpr (by simpa using hθA)
    exact this.trans hClo
  have hCpos : 0 < C := by linarith
  have hAC : A < 1 / C := by
    have h := (lt_div_iff₀ hA).mp hChi
    apply (lt_div_iff₀ hCpos).mpr
    nlinarith
  have hACT : A < C * θ := by
    have h := (div_lt_iff₀ hθ).mp hClo
    simpa [mul_comm] using h
  obtain ⟨B, hAB, hB⟩ := exists_between (lt_min hAC hACT)
  have hBC : B < 1 / C := hB.trans_le (min_le_left _ _)
  have hBCT : B < C * θ := hB.trans_le (min_le_right _ _)
  have hCB : C * B < 1 := by
    have h := (lt_div_iff₀ hCpos).mp hBC
    simpa [mul_comm] using h
  have hB1 : B < 1 := by
    have : 1 / C < (1 : ℚ) := (div_lt_one hCpos).mpr hC1
    exact hBC.trans this
  have hCT1 : C * θ < 1 := by
    have h := mul_lt_mul_of_pos_left hθA hCpos
    have h' := (lt_div_iff₀ hA).mp hChi
    nlinarith
  have hνA : 0 < ν * (A : ℝ) := mul_pos hνpos (by exact_mod_cast hA)
  obtain ⟨η, hη, hηhi⟩ := exists_between
    (lt_min (show (0 : ℝ) < 1 by norm_num) (div_pos hgap hνA))
  have hη1 : η < 1 := hηhi.trans_le (min_le_left _ _)
  have hηgap := (lt_div_iff₀ hνA).mp (hηhi.trans_le (min_le_right _ _))
  refine ⟨θ, A, B, C, η, hθ, hθA, hAB, hB1, hC1, hCB, hBCT, hCT1, hη, hη1, ?_⟩
  nlinarith

/-- The dimension-dependent choices satisfy both volume hypotheses
of Theorem 9, with the first volume exactly one half. -/
theorem dimension_data_admissible (m : ℕ) (hm : 0 < m)
    (θ B C : ℚ) (hθ : 0 < θ) (hB : 0 < B) (hC : 1 < C)
    (hCθ : C * θ < 1) :
    let K := ⌊C ^ m⌋₊
    let w0 := (B ^ m)⁻¹
    let v0 := 2 * (K : ℚ) * θ ^ m * w0
    0 < K ∧ 0 < w0 ∧ 0 < v0 ∧
      (K : ℚ) * θ ^ m < 1 ∧ (K : ℚ) * (w0 / v0) * θ ^ m = 1 / 2 := by
  dsimp only
  have hCpos : 0 < C := by linarith
  have hK : 0 < ⌊C ^ m⌋₊ := by
    have hpow : (1 : ℚ) ≤ C ^ m := one_le_pow₀ hC.le
    exact Nat.le_floor hpow
  have hKR : (0 : ℚ) < ⌊C ^ m⌋₊ := by exact_mod_cast hK
  have hw0 : (0 : ℚ) < (B ^ m)⁻¹ := by positivity
  have hv0 : (0 : ℚ) < 2 * (⌊C ^ m⌋₊ : ℚ) * θ ^ m * (B ^ m)⁻¹ := by
    positivity
  have hfloor : (⌊C ^ m⌋₊ : ℚ) ≤ C ^ m := Nat.floor_le (by positivity)
  have hvolume : (⌊C ^ m⌋₊ : ℚ) * θ ^ m < 1 := by
    calc
      _ ≤ C ^ m * θ ^ m := mul_le_mul_of_nonneg_right hfloor (by positivity)
      _ = (C * θ) ^ m := (mul_pow C θ m).symm
      _ < 1 := pow_lt_one₀ (by positivity) hCθ hm.ne'
  refine ⟨hK, hw0, hv0, hvolume, ?_⟩
  have hKn : (⌊C ^ m⌋₊ : ℚ) ≠ 0 := hKR.ne'
  have hθn : θ ≠ 0 := hθ.ne'
  have hBn : B ≠ 0 := hB.ne'
  field_simp

end ImaginaryQuadratic
