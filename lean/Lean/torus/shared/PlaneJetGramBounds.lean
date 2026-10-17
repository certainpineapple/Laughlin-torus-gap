import torus.shared.PlaneJetLaguerreGram
import LatticeLaguerreSum

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetGramBounds

open TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Fermion.LatticeLaguerreSum
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetLaguerreGram

theorem magneticCocycle_norm_one (k : ℝ) (x y : ℂ) :
    ‖magneticCocycle k x y‖ = 1 := by
  rw [magneticCocycle_eq_im, Complex.norm_exp_ofReal_mul_I]

theorem imagePhase_norm_one (G : Geometry) (theta : Twist) (R S : ℂ) (p : ℤ × ℤ) :
    ‖imagePhase G theta R S p‖ = 1 := by
  simp only [imagePhase, norm_mul, norm_inv, latticeChi_norm,
    magneticCocycle_norm_one, inv_one, mul_one]

def gramImageTerm (G : Geometry) (theta : Twist) (j : ℕ) (R S : ℂ) (p : ℤ × ℤ) : ℂ :=
  imagePhase G theta R S p *
    ((Real.exp (-‖imageDisplacement G R S p‖ ^ 2 / 2) *
      TorusLean.Fermion.JetEnvelope.paperLaguerre j (‖imageDisplacement G R S p‖ ^ 2) : ℝ) : ℂ)

theorem gramImageTerm_norm (G : Geometry) (theta : Twist) (j : ℕ)
    (R S : ℂ) (p : ℤ × ℤ) :
    ‖gramImageTerm G theta j R S p‖ = laguerreTerm G (R - S) j p := by
  have hd : imageDisplacement G R S p = period G p - (R - S) := by
    unfold imageDisplacement period
    ring
  simp only [gramImageTerm, norm_mul, imagePhase_norm_one, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    hd, laguerreTerm]
  rfl

/-- The exact physical cell Gram inherits the already proved uniform
linear-in-j absolute Laguerre budget, for every center and twist. -/
theorem rawPlaneJet_cell_gram_norm_le (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (j : ℕ) (R S : ℂ) :
    ‖cellInner G 1
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R)
      (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j S)‖ ≤
      (4096 + gaussianConstant) * (1 + (j : ℝ)) := by
  have h := (rawPlaneJet_cell_gram_laguerre_hasSum G theta j R S).norm_le_of_bounded
    (laguerre_summable G hG (R - S) j).hasSum
    (fun p => (gramImageTerm_norm G theta j R S p).le)
  exact h.trans (laguerre_sum_bound G hG (R - S) j)

/-- Actual cell-Hilbert norm bound, with no supplied Gram or norm premise. -/
theorem rawPlaneJet_norm_sq_le (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (j : ℕ) (R : ℂ) :
    ‖rawPlaneJet G theta j R‖ ^ 2 ≤ (4096 + gaussianConstant) * (1 + (j : ℝ)) := by
  calc
    _ = (inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta j R)).re :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ ≤ ‖inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta j R)‖ :=
      Complex.re_le_norm _
    _ ≤ _ := rawPlaneJet_cell_gram_norm_le G theta hG j R R

theorem gramImageTerm_zero_self (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    gramImageTerm G theta j R R 0 = 1 := by
  simp [gramImageTerm, imagePhase, imageDisplacement, latticePeriod, latticeChi,
    twistExponent, magneticCocycle, map_neg, mul_comm,
    TorusLean.Fermion.PlaneJetDisplacement.paperLaguerre_at_zero]

/-- A finite-order error budget on the actual physical Hilbert norm.
The hypotheses concern the actual shortest lattice cycle, not area alone. -/
theorem rawPlaneJet_norm_sq_sub_one_le (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (hfar : 64 * (j : ℝ) ≤ L^2) :
    |‖rawPlaneJet G theta j R‖^2 - 1| ≤ Real.exp (-L^2 / 8) * gaussianConstant := by
  classical
  have hG : 1 ≤ systole G := hL1.trans hL
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hs : HasSum (gramImageTerm G theta j R R)
      ((‖rawPlaneJet G theta j R‖^2 : ℝ) : ℂ) := by
    have hg := rawPlaneJet_cell_gram_laguerre_hasSum G theta j R R
    change HasSum (gramImageTerm G theta j R R)
      (inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta j R)) at hg
    rw [inner_self_eq_norm_sq_to_K] at hg
    convert hg using 1
    push_cast
    rfl
  have ht := hasSum_ite_sub_hasSum hs (0 : ℤ × ℤ)
  rw [gramImageTerm_zero_self] at ht
  have hb : ∀ p : ℤ × ℤ,
      ‖if p = 0 then (0 : ℂ) else gramImageTerm G theta j R R p‖ ≤ gaussianTail G 0 L p := by
    intro p
    by_cases hp : p = 0
    · simp only [hp, ite_eq_left, norm_zero]
      unfold gaussianTail
      split_ifs <;> positivity
    · have hl := (systole_ge_iff G L).mp hL p hp
      have hsq : L^2 ≤ ‖period G p‖^2 := (sq_le_sq₀ hL0 (norm_nonneg _)).mpr hl
      simp only [hp, ite_false, gramImageTerm_norm, sub_self, laguerreTerm,
        sub_zero, gaussianTail, ite_eq_left hl]
      exact TorusLean.Fermion.JetEnvelope.laguerre_gaussian_far_bound j _ (hfar.trans hsq)
  have hn := ht.norm_le_of_bounded (gaussianTail_summable G hG 0 L hL0).hasSum hb
  have he := hn.trans (gaussianTail_bound G hG 0 L hL0)
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using he

#print axioms gramImageTerm_zero_self
#print axioms rawPlaneJet_norm_sq_sub_one_le
#print axioms magneticCocycle_norm_one
#print axioms imagePhase_norm_one
#print axioms gramImageTerm_norm
#print axioms rawPlaneJet_cell_gram_norm_le
#print axioms rawPlaneJet_norm_sq_le

end TorusLean.Shared.PlaneJetGramBounds
