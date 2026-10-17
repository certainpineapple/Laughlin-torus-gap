import torus.shared.ThermalCoherentRegularity

/-! Finite exact expansions for two raw spectators after the actual pair
annihilator, with no operator-norm bound on bosonic annihilation. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentDoubleRegularity
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.ThermalCoherentRegularity

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- Literal two ordered spectator annihilations after the normalized pair.
No symmetric-tensor 1/2 is included in this squared norm. -/
def twoSpectatorNormSq (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (R S T : ℂ) : ℝ :=
  occupationMetricNormSq (fun _ => 1)
    (spectatorPair (evaluationCoordinates G theta S) (evaluationCoordinates G theta T)
      (modePair (evaluationCoordinates G theta R) p))

theorem twoSpectatorNormSq_nonneg (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (R S T : ℂ) :
    0 ≤ twoSpectatorNormSq G theta p R S T := occupationMetricNormSq_nonneg _ _

theorem twoSpectatorNormSq_continuous (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun x : ℂ × (ℂ × ℂ) => twoSpectatorNormSq G theta p x.1 x.2.1 x.2.2) := by
  let c : (TwoBodyLift.PairIndex (OrbitalIndex G theta) × (OrbitalIndex G theta × OrbitalIndex G theta)) → (ℂ × (ℂ × ℂ)) → ℂ := fun j x =>
    pairProduct G theta j.1.1 j.1.2 x.1 *
      (orbitalBasis G theta j.2.1).val x.2.1 * (orbitalBasis G theta j.2.2).val x.2.2
  let v : (TwoBodyLift.PairIndex (OrbitalIndex G theta) × (OrbitalIndex G theta × OrbitalIndex G theta)) → Core (OrbitalIndex G theta) ℂ := fun j =>
    annihilate j.2.2 (annihilate j.2.1 (TwoBodyLift.pairRemove j.1 p))
  have hc (j : (TwoBodyLift.PairIndex (OrbitalIndex G theta) × (OrbitalIndex G theta × OrbitalIndex G theta))) : Continuous (c j) :=
    (((pairProduct_continuous G theta j.1.1 j.1.2).comp continuous_fst).mul
      ((rawLLL_continuous G theta 1 (orbitalBasis G theta j.2.1)).comp
        (continuous_fst.comp continuous_snd))).mul
      ((rawLLL_continuous G theta 1 (orbitalBasis G theta j.2.2)).comp
        (continuous_snd.comp continuous_snd))
  have he (x : ℂ × (ℂ × ℂ)) :
      spectatorPair (evaluationCoordinates G theta x.2.1) (evaluationCoordinates G theta x.2.2)
        (modePair (evaluationCoordinates G theta x.1) p) = ∑ j, c j x • v j := by
    rw [spectatorPair, LinearMap.comp_apply, modePair_evaluation_expansion]
    simp only [map_sum, map_smul, modeAnnihilate_evaluation_expansion,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type, c, v, mul_assoc]
  simpa only [twoSpectatorNormSq, he] using finite_combination_normSq_continuous c hc v

/-- Both raw modes retain their untruncated whole-plane offsets. -/
theorem twoSpectatorOffset_continuous (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun x : ℂ × (ℂ × ℂ) =>
      twoSpectatorNormSq G theta p x.1 (x.1 + x.2.1) (x.1 + x.2.2)) := by
  have hm : Continuous (fun x : ℂ × (ℂ × ℂ) =>
      (x.1, (x.1 + x.2.1, x.1 + x.2.2))) :=
    continuous_fst.prodMk ((continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.add (continuous_snd.comp continuous_snd)))
  exact Continuous.comp
    (g := fun x : ℂ × (ℂ × ℂ) => twoSpectatorNormSq G theta p x.1 x.2.1 x.2.2)
    (f := fun x : ℂ × (ℂ × ℂ) => (x.1, (x.1 + x.2.1, x.1 + x.2.2)))
    (twoSpectatorNormSq_continuous G theta p) hm

#print axioms twoSpectatorNormSq_continuous
#print axioms twoSpectatorOffset_continuous
end TorusLean.Shared.ThermalCoherentDoubleRegularity
