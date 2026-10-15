import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.List.OfFn
import ExternalResults.LiuJiangZhangLogSeries
import ExternalResults.RepeatedFibres.Interpolation
import ExternalResults.RepeatedFibres.LogBridge

/-!
# Liu–Jiang–Zhang, Theorem 9

Source: [https://arxiv.org/abs/2610.10192v2](https://arxiv.org/abs/2610.10192v2)

Variable `0` represents `t` in the local series and `Y` in the polynomial;
variable `i.succ` represents `u_i` and `X_i`, respectively. Prescribing every
coefficient of weight less than `H` expresses surjectivity onto
the direct sum of coefficient packets. Coefficients outside those packets are
irrelevant, so targets can be given as unrestricted coefficient functions.

The theorem extends the external interpolation proof to bounded fibre multiplicity.
-/

namespace LiuJiangZhang

/-- Theorem 9: surjectivity of the substitution on
weighted polynomial and coefficient spaces. Weight thresholds and the degree
divisibility are chosen before the centres; the eventual degree threshold can
depend on the centres. -/
theorem theorem9
    (m K κ : ℕ) (hm : 1 ≤ m) (hK : 1 ≤ K) (hκ : 1 ≤ κ) (hκK : κ ≤ K)
    (w0 v0 θ : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hvolume : (K : ℚ) * (w0 / v0) * θ ^ m < 1)
    (hfibreVolume : (κ : ℚ) * θ ^ m < 1) :
    ∃ thresholds : Fin m → List ℚ → ℚ,
      ∀ w : Fin m → ℚ,
        (∀ i, 0 < w i) →
        (∀ i, thresholds i ((List.ofFn w).take i.val) < w i) →
        ∃ R : ℕ, 0 < R ∧
          ∀ (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ),
            (∀ j, y j ≠ 0) →
            (∀ z : ℂ, (Finset.univ.filter (fun j => y j = z)).card ≤ κ) →
            (∀ j k, j ≠ k → y j = y k → ∀ i, c j i ≠ c k i) →
            ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
              ∀ target : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ,
                ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
                  (∀ α ∈ P.support,
                    w0 * (α 0 : ℚ) +
                      ∑ i : Fin m, w i * (α i.succ : ℚ) ≤ (n * R : ℕ)) ∧
                  ∀ (j : Fin K) (α : Fin (m + 1) →₀ ℕ),
                    v0 * (α 0 : ℚ) +
                      ∑ i : Fin m, (w i / θ) * (α i.succ : ℚ) < (n * R : ℕ) →
                    MvPowerSeries.coeff α
                      (MvPolynomial.eval₂ MvPowerSeries.C
                        (Fin.cases
                          (MvPowerSeries.C (y j) * (1 + MvPowerSeries.X 0))
                          (fun i => MvPowerSeries.C (c j i) +
                            MvPowerSeries.X i.succ + logOneAdd m)) P) = target j α := by
  classical
  clear hK hκ hκK
  obtain ⟨thresholds, hthresholds⟩ := RepeatedFibres.interpolation m K κ hm
    w0 v0 θ hw0 hv0 hθ hθ1 hvolume hfibreVolume
  refine ⟨thresholds, ?_⟩
  intro w hw hlarge
  obtain ⟨R, hR, hcentres⟩ := hthresholds w hw hlarge
  refine ⟨R, hR, ?_⟩
  intro y c hy hcard hsep
  obtain ⟨n0, hn0⟩ := hcentres y c hy hcard hsep
  refine ⟨n0, ?_⟩
  intro n hn target
  obtain ⟨P, hP, hjet⟩ := hn0 n hn target
  refine ⟨P, ?_, ?_⟩
  · simpa only [RepeatedFibres.weight_eq_explicit] using hP
  · intro j α hα
    have h := hjet j α (by simpa only [RepeatedFibres.weight_eq_explicit] using hα)
    simpa only [RepeatedFibres.formalJet_eq_eval] using h

end LiuJiangZhang
