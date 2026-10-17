import torus.shared.PlaneJetGramBounds
import UniformTail

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetTailBudget

open Filter Topology TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetGramBounds
open TorusLean.Fermion.UniformTail

/-- All actual centers on the universal cover and all seed degrees at most z.
This is a uniform dominating budget, without selecting a center or a degree. -/
def jetNormValues (G : Geometry) (theta : Twist) (z : ℕ) : Set ℝ :=
  {v | ∃ j : ℕ, j ≤ z ∧ ∃ R : ℂ, ‖rawPlaneJet G theta j R‖^2 = v}

def jetNormBudget (G : Geometry) (theta : Twist) (z : ℕ) : ℝ :=
  sSup (jetNormValues G theta z)

theorem jetNormValues_nonempty (G : Geometry) (theta : Twist) (z : ℕ) :
    (jetNormValues G theta z).Nonempty :=
  ⟨_, 0, Nat.zero_le _, 0, rfl⟩

theorem jetNormValues_bddAbove (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (z : ℕ) : BddAbove (jetNormValues G theta z) := by
  refine ⟨(4096 + gaussianConstant) * (1 + (z : ℝ)), ?_⟩
  rintro v ⟨j, hj, R, rfl⟩
  exact (rawPlaneJet_norm_sq_le G theta hG j R).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_left hj 1)
      (by linarith [gaussianConstant_nonneg]))

theorem rawPlaneJet_norm_sq_le_budget (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (z j : ℕ) (hj : j ≤ z) (R : ℂ) :
    ‖rawPlaneJet G theta j R‖^2 ≤ jetNormBudget G theta z :=
  le_csSup (jetNormValues_bddAbove G theta hG z) ⟨j, hj, R, rfl⟩

theorem jetNormBudget_nonneg (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (z : ℕ) : 0 ≤ jetNormBudget G theta z :=
  (sq_nonneg _).trans (rawPlaneJet_norm_sq_le_budget G theta hG z 0 (Nat.zero_le _) 0)

theorem jetNormBudget_le (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (z : ℕ) :
    jetNormBudget G theta z ≤ (4096 + gaussianConstant) * (1 + (z : ℝ)) := by
  apply csSup_le (jetNormValues_nonempty G theta z)
  rintro v ⟨j, hj, R, rfl⟩
  exact (rawPlaneJet_norm_sq_le G theta hG j R).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_left hj 1)
      (by linarith [gaussianConstant_nonneg]))

theorem jetNormBudget_sub_one_le (G : Geometry) (theta : Twist)
    (z : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (hfar : 64 * (z : ℝ) ≤ L^2) :
    |jetNormBudget G theta z - 1| ≤ Real.exp (-L^2 / 8) * gaussianConstant := by
  have hG := hL1.trans hL
  have hupper : jetNormBudget G theta z ≤ 1 + Real.exp (-L^2 / 8) * gaussianConstant := by
    apply csSup_le (jetNormValues_nonempty G theta z)
    rintro v ⟨j, hj, R, rfl⟩
    have hjr : (j : ℝ) ≤ z := by exact_mod_cast hj
    have h := rawPlaneJet_norm_sq_sub_one_le G theta j R L hL1 hL
      ((mul_le_mul_of_nonneg_left hjr (by norm_num)).trans hfar)
    linarith [(abs_le.mp h).2]
  have hzero := rawPlaneJet_norm_sq_sub_one_le G theta 0 0 L hL1 hL (by simpa using sq_nonneg L)
  have hlow := rawPlaneJet_norm_sq_le_budget G theta hG z 0 (Nat.zero_le _) 0
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hzero).1], by linarith⟩

/-- Arbitrary twists and centers remain uniform as the actual shortest cycle
diverges. Area growth by itself is not the hypothesis. -/
theorem jetNormBudget_tendsto {ι : Type*} {l : Filter ι}
    (G : ι → Geometry) (theta : ι → Twist)
    (hG : Tendsto (fun a => systole (G a)) l atTop) (z : ℕ) :
    Tendsto (fun a => jetNormBudget (G a) (theta a) z) l (𝓝 1) := by
  have hs : Tendsto (fun a => (systole (G a))^2) l atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hG
  have hd : Tendsto (fun a => (systole (G a))^2 / 8) l atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 8)).mpr hs
  have he : Tendsto (fun a => Real.exp (-(systole (G a))^2 / 8) * gaussianConstant) l (𝓝 0) := by
    simpa only [Function.comp_def, neg_div, zero_mul] using
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hd)).mul_const gaussianConstant
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ he
  filter_upwards [hG.eventually_ge_atTop 1, hs.eventually_ge_atTop (64 * (z : ℝ))] with a ha hb
  exact jetNormBudget_sub_one_le (G a) (theta a) z (systole (G a)) ha le_rfl hb

theorem actual_jet_tail_summable (G : Geometry) (theta : Twist) (hG : 1 ≤ systole G) :
    Summable (fun m => weight m * jetNormBudget G theta (degree m)) := by
  apply delta_summable (jetNormBudget_nonneg G theta hG)
  intro z
  simpa only [add_comm (z : ℝ) 1] using jetNormBudget_le G theta hG z

/-- The scalar odd-tail constant is now instantiated by the actual uniform
finite-degree jet-norm supremum. The many-body energy domination is separate. -/
theorem actual_jet_tail_tendsto {ι : Type*} {l : Filter ι}
    (G : ι → Geometry) (theta : ι → Twist)
    (hG : Tendsto (fun a => systole (G a)) l atTop) :
    Tendsto (fun a => delta (jetNormBudget (G a) (theta a))) l (𝓝 (61/4096 : ℝ)) := by
  apply delta_tendsto (C := 4096 + gaussianConstant)
  · filter_upwards [hG.eventually_ge_atTop 1] with a ha
    intro z
    exact ⟨jetNormBudget_nonneg (G a) (theta a) ha z,
      by simpa only [add_comm (z : ℝ) 1] using jetNormBudget_le (G a) (theta a) ha z⟩
  · exact jetNormBudget_tendsto G theta hG

#print axioms jetNormValues_nonempty
#print axioms jetNormValues_bddAbove
#print axioms rawPlaneJet_norm_sq_le_budget
#print axioms jetNormBudget_nonneg
#print axioms jetNormBudget_le
#print axioms jetNormBudget_sub_one_le
#print axioms jetNormBudget_tendsto
#print axioms actual_jet_tail_summable
#print axioms actual_jet_tail_tendsto

end TorusLean.Shared.PlaneJetTailBudget
