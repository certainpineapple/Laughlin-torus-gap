import torus.shared.PhysicalBosonS4

/-! Finite exact scalar expansions establish measurability of the physical
one-spectator form before any Bochner integral is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentRegularity
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open scoped ComplexConjugate

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- Continuity of the true factorial norm squared of a finite combination;
no topology or boundedness on the whole polynomial Fock core is postulated. -/
theorem finite_combination_normSq_continuous
    {X ι J : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype J]
    (c : J → X → ℂ) (hc : ∀ j, Continuous (c j)) (p : J → Core ι ℂ) :
    Continuous (fun x => occupationMetricNormSq (fun _ => 1) (∑ j, c j x • p j)) := by
  have he (x : X) : occupationMetricNormSq (fun _ => 1) (∑ j, c j x • p j) =
      (∑ j, ∑ k, conj (c j x) * c k x * occupationInner (fun _ => 1) (p j) (p k)).re := by
    rw [← Complex.ofReal_re (occupationMetricNormSq (fun _ => 1) (∑ j, c j x • p j)),
      ← occupationInner_self]
    change (SpectatorControl.ip _ _).re = _
    simp only [TwoBodyLift.inner_sum_left, TwoBodyLift.inner_sum_right,
      TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
      Complex.star_def, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    simp only [SpectatorControl.ip]
    ring
  simp_rw [he]
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro k hk
  exact ((Complex.continuous_conj.comp (hc j)).mul (hc k)).mul continuous_const

theorem modeAnnihilate_evaluation_expansion (G : Geometry) (theta : Twist) (R : ℂ)
    (p : Core (OrbitalIndex G theta) ℂ) :
    modeAnnihilate (evaluationCoordinates G theta R) p =
      ∑ i, (orbitalBasis G theta i).val R • annihilate i p := by
  simp only [modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    Complex.star_def, evaluationCoordinates_conj]

/-- The literal spectator-after-pair-removal quadratic form. -/
def oneSpectatorNormSq (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (R S : ℂ) : ℝ :=
  occupationMetricNormSq (fun _ => 1)
    (modeAnnihilate (evaluationCoordinates G theta S)
      (modePair (evaluationCoordinates G theta R) p))

theorem oneSpectatorNormSq_nonneg (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (R S : ℂ) :
    0 ≤ oneSpectatorNormSq G theta p R S := occupationMetricNormSq_nonneg _ _

theorem oneSpectatorNormSq_continuous (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun x : ℂ × ℂ => oneSpectatorNormSq G theta p x.1 x.2) := by
  let c : (TwoBodyLift.PairIndex (OrbitalIndex G theta) × OrbitalIndex G theta) →
      (ℂ × ℂ) → ℂ := fun j x =>
    pairProduct G theta j.1.1 j.1.2 x.1 * (orbitalBasis G theta j.2).val x.2
  let v : (TwoBodyLift.PairIndex (OrbitalIndex G theta) × OrbitalIndex G theta) →
      Core (OrbitalIndex G theta) ℂ := fun j => annihilate j.2 (TwoBodyLift.pairRemove j.1 p)
  have hc (j) : Continuous (c j) :=
    ((pairProduct_continuous G theta j.1.1 j.1.2).comp continuous_fst).mul
      ((rawLLL_continuous G theta 1 (orbitalBasis G theta j.2)).comp continuous_snd)
  have he (x : ℂ × ℂ) :
      modeAnnihilate (evaluationCoordinates G theta x.2)
        (modePair (evaluationCoordinates G theta x.1) p) = ∑ j, c j x • v j := by
    rw [modePair_evaluation_expansion]
    simp only [map_sum, map_smul, modeAnnihilate_evaluation_expansion,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type, c, v]
  simpa only [oneSpectatorNormSq, he] using finite_combination_normSq_continuous c hc v

/-- In particular the translated offset is the genuine sum R+β on the
whole plane; no fundamental-cell representative enters this definition. -/
theorem oneSpectatorOffset_continuous (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun x : ℂ × ℂ => oneSpectatorNormSq G theta p x.1 (x.1 + x.2)) := by
  have hm : Continuous (fun x : ℂ × ℂ => (x.1, x.1 + x.2)) :=
    continuous_fst.prodMk (continuous_fst.add continuous_snd)
  exact Continuous.comp
    (g := fun x : ℂ × ℂ => oneSpectatorNormSq G theta p x.1 x.2)
    (f := fun x : ℂ × ℂ => (x.1, x.1 + x.2))
    (oneSpectatorNormSq_continuous G theta p) hm

#print axioms finite_combination_normSq_continuous
#print axioms oneSpectatorNormSq_continuous
#print axioms oneSpectatorOffset_continuous
end TorusLean.Shared.ThermalCoherentRegularity
