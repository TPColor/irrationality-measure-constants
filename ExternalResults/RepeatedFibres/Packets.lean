import ExternalResults.RepeatedFibres.AdmissibleJetSurjectivity
import ExternalResults.RepeatedFibres.AdmissibleJetPackets
import ExternalResults.RepeatedFibres.AdmissibleMatrixFrame
import LogIrrationalityMeasure.Approximation.WeightedGlobalSectionBound

namespace LiuJiangZhang.RepeatedFibres

open LogIrrationalityMeasure LogExponent
open AlgebraicGeometry CategoryTheory Filter
open LiuJiangZhang.RepeatedFibres.AdmissibleBlowupGeometry LiuJiangZhang.RepeatedFibres.AdmissibleJetPackets
open scoped BigOperators

noncomputable section

/-- The geometric extension gives all sufficiently large admissible degrees,
with exactly the same weighted polynomial and jet packets as Theorem 9. -/
theorem eventual_packets (d : InterpolationData) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ target : Fin d.K → (Fin (d.m + 1) →₀ ℕ) → ℂ,
        ∃ P : MvPolynomial (Fin (d.m + 1)) ℂ,
          (∀ α ∈ P.support, Finsupp.weight d.curveDegreeWeights α ≤ n * (scale d).radius) ∧
          ∀ (j : Fin d.K) (α : Fin (d.m + 1) →₀ ℕ),
            Finsupp.weight d.curveJetWeights α < n * (scale d).radius →
              MvPowerSeries.coeff α (FormalLogJet.formalJet (d.curveCenters j) P) =
                target j α := by
  classical
  obtain ⟨e⟩ := AdmissibleMatrixInterpolation.actualFrame_exists d
  have hbudget : ∀ j : Index d,
      Finsupp.weight (fun i => (d.curveDegreeWeights i : ℝ)) (exponents d j) ≤
        ((scale d).radius : ℝ) := by
    intro j
    have h := (scale d).budget d.curveDegreeWeights_pos j
    simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_natCast, mul_comm] using (show ((∑ i, d.curveDegreeWeights i *
        ((exponents d j) i : ℚ) : ℚ) : ℝ) ≤ ((scale d).radius : ℝ) by exact_mod_cast h)
  have hbound := WeightedGlobalSectionBound.eventual_supportBound
    (K := ℂ) (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos) (coordinateIndex d)
    ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ)) ((scale d).radius : ℝ) hbudget
  obtain ⟨N, hN⟩ := hbound
  have hjet := AdmissibleJetSurjectivity.eventually_jetRestriction_surjective d
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp (hjet.and (eventually_ge_atTop N))
  refine ⟨n0, ?_⟩
  intro n hn target
  obtain ⟨hjn, hnN⟩ := hn0 n hn
  have hsurj := formalPackets_surjective_of_jetRestriction d n e hjn
  obtain ⟨s, hs⟩ := hsurj (fun j α => target j α.val)
  refine ⟨sectionPolynomial d n e s, ?_, ?_⟩
  · intro α hα
    have hd := hN n hnN e s α hα
    have hcast : ((Finsupp.weight d.curveDegreeWeights α : ℚ) : ℝ) ≤
        ((n * (scale d).radius : ℕ) : ℝ) := by
      simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum, Rat.cast_mul,
        Rat.cast_natCast, Nat.cast_mul] using hd
    exact_mod_cast hcast
  · intro j α hα
    exact congrFun (congrFun hs j) ⟨α, hα⟩

end
end LiuJiangZhang.RepeatedFibres
