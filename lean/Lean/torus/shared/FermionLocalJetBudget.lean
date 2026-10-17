import torus.shared.FermionLocalJetOccupation

/-! The manuscript local errors e8, e23 and e24, with one geometric threshold
for all original geometries, twists, centers and Fock particle sectors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PlaneJetFiniteGram TorusLean.Fermion.LatticePacking
open Filter Topology
open scoped BigOperators ComplexConjugate

/-- The local 0,...,8 raw-jet Gram error used by the seven-row metric remainder. -/
def e8 (G : Geometry) (theta : Twist) : ℝ := localJetError G theta 8
/-- The local 0,...,23 raw-jet Gram error used by the pair left factor p≤22. -/
def e23 (G : Geometry) (theta : Twist) : ℝ := localJetError G theta 23
/-- The local 0,...,24 raw-jet Gram error used by the two CAR contractions. -/
def e24 (G : Geometry) (theta : Twist) : ℝ := localJetError G theta 24

theorem localJetBudget_tendsto (J : ℕ) : Tendsto (localJetBudget J) atTop (𝓝 0) :=
  PlaneJetFiniteGram.finiteGramOperatorError_tendsto J

/-- Actual e_J tends to zero for arbitrary varying original lattices and twists. -/
theorem localJetError_tendsto {ι : Type*} {l : Filter ι}
    (G : ι → Geometry) (theta : ι → Twist) (J : ℕ)
    (hG : Tendsto (fun a => systole (G a)) l atTop) :
    Tendsto (fun a => localJetError (G a) (theta a) J) l (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ ((localJetBudget_tendsto J).comp hG)
  · filter_upwards [hG.eventually_ge_atTop 1] with a ha
    exact localJetError_nonneg (G a) (theta a) J ha
  · filter_upwards [hG.eventually_ge_atTop 1] with a ha
    exact localJetError_le_budget (G a) (theta a) J (systole (G a)) ha le_rfl

/-- A fixed degree has a threshold independent of shape, flux and twist. -/
theorem localJetError_exists_threshold (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      localJetError G theta J ≤ ε := by
  have he := (localJetBudget_tendsto J).eventually (gt_mem_nhds hε)
  obtain ⟨L,hL⟩ := eventually_atTop.mp he
  refine ⟨max 1 L,le_max_left _ _,fun G theta hG => ?_⟩
  exact (localJetError_le_budget G theta J (systole G)
    ((le_max_left _ _).trans hG) le_rfl).trans
      (hL (systole G) ((le_max_right _ _).trans hG)).le

/-- One threshold simultaneously controls precisely the three manuscript errors. -/
theorem e8_e23_e24_exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      e8 G theta ≤ ε ∧ e23 G theta ≤ ε ∧ e24 G theta ≤ ε := by
  obtain ⟨L8,h81,h8⟩ := localJetError_exists_threshold 8 ε hε
  obtain ⟨L23,h231,h23⟩ := localJetError_exists_threshold 23 ε hε
  obtain ⟨L24,h241,h24⟩ := localJetError_exists_threshold 24 ε hε
  refine ⟨max L8 (max L23 L24),h81.trans (le_max_left _ _),fun G theta hG => ?_⟩
  exact ⟨h8 G theta ((le_max_left _ _).trans hG),
    h23 G theta ((le_max_left _ _).trans ((le_max_right _ _).trans hG)),
    h24 G theta ((le_max_right _ _).trans ((le_max_right _ _).trans hG))⟩

/-- The precise e8 metric error on arbitrary actual occupation output states. -/
theorem e8_occupation_metric_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (R : ℂ) (x : Fin 9 → Space (physicalQ G theta)) :
    |(∑ i : Fin 9, ∑ j : Fin 9,
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * occupationInner (physicalQ G theta) (x i) (x j)).re| ≤
      e8 G theta * ∑ i, occupationNormSq (physicalQ G theta) (x i) :=
  localJetError_occupation_real_form G theta 8 hG R x

/-- The actual p≤22 input coefficient span uses e23, with no orthogonalization. -/
theorem e23_synthesis_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (R : ℂ) (c : Fin 24 → ℂ) :
    ‖jetSynthesis G theta 23 R c‖^2 ≤ (1+e23 G theta) * ∑ j, ‖c j‖^2 :=
  localJetSynthesis_norm_le G theta 23 hG R c

/-- The true double annihilation allowance is (1+e24)^2 on every Fock state. -/
theorem e24_two_annihilator_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (R : ℂ) (i j : ℕ) (hi : i ≤ 24) (hj : j ≤ 24)
    (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta)
      (localJetAnnihilate G theta j R (localJetAnnihilate G theta i R x)) ≤
      (1+e24 G theta)^2 * occupationNormSq (physicalQ G theta) x :=
  localJetAnnihilate_two_bound G theta 24 hG R i j hi hj x

/-- Simultaneous actual Gram and occupation budgets.  The geometric threshold
is chosen before the state and has no particle or occupation dimension input. -/
theorem actual_local_jet_uniform_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      (e8 G theta ≤ ε ∧ e23 G theta ≤ ε ∧ e24 G theta ≤ ε) ∧
      (∀ (R : ℂ) (c : Fin 24 → ℂ),
        ‖jetSynthesis G theta 23 R c‖^2 ≤ (1+ε) * ∑ j, ‖c j‖^2) ∧
      (∀ (R : ℂ) (j : ℕ), j ≤ 8 → ∀ x : Space (physicalQ G theta),
        occupationNormSq (physicalQ G theta) (localJetAnnihilate G theta j R x) ≤
          (1+ε) * occupationNormSq (physicalQ G theta) x) ∧
      (∀ (R : ℂ) (i j : ℕ), i ≤ 24 → j ≤ 24 → ∀ x : Space (physicalQ G theta),
        occupationNormSq (physicalQ G theta)
          (localJetAnnihilate G theta j R (localJetAnnihilate G theta i R x)) ≤
            (1+ε)^2 * occupationNormSq (physicalQ G theta) x) := by
  obtain ⟨L,hL1,hL⟩ := e8_e23_e24_exists_threshold ε hε
  refine ⟨L,hL1,fun G theta hG => ?_⟩
  have hg := hL1.trans hG
  have he := hL G theta hG
  refine ⟨he,?_,?_,?_⟩
  · intro R c
    exact (e23_synthesis_bound G theta hg R c).trans
      (mul_le_mul_of_nonneg_right (by linarith [he.2.1])
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  · intro R j hj x
    exact (localJetAnnihilate_finite_bound G theta 8 hg R j hj x).trans
      (mul_le_mul_of_nonneg_right (by change 1+e8 G theta ≤ 1+ε; linarith [he.1])
        (occupationNormSq_nonneg _ _))
  · intro R i j hi hj x
    have hc : 0 ≤ 1+e24 G theta := by
      have hp := localJetError_nonneg G theta 24 hg
      change 0 ≤ localJetError G theta 24 at hp
      change 0 ≤ 1+localJetError G theta 24
      linarith
    exact (e24_two_annihilator_bound G theta hg R i j hi hj x).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc (by linarith [he.2.2]) 2)
        (occupationNormSq_nonneg _ _))

#print axioms localJetBudget_tendsto
#print axioms localJetError_tendsto
#print axioms localJetError_exists_threshold
#print axioms e8_e23_e24_exists_threshold
#print axioms e8_occupation_metric_bound
#print axioms e23_synthesis_bound
#print axioms e24_two_annihilator_bound
#print axioms actual_local_jet_uniform_threshold
end TorusLean.Shared.FermionLocalJet
