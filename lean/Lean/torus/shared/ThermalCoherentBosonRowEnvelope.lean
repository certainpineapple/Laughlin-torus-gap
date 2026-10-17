import torus.shared.ThermalCoherentBosonRowFiniteTrace
import torus.shared.ThermalCoherentBosonRowAuxiliary
import torus.shared.BosonThermalJacobiRows

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowEnvelope
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.ThermalCoherentBosonRowRotation
open TorusLean.Shared.ThermalCoherentBosonRowAuxiliary
open TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonNatThreeRemovalTrace TorusLean.Shared.BosonThermalJacobiRows
open MeasureTheory
open scoped BigOperators ComplexConjugate
local instance rowEnvelope_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem natThreeAnnihilator_cross_expansion (G : Geometry) (theta : Twist)
    (p r : Core ℕ ℂ) (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (natThreeAnnihilator G theta R p f) (natThreeAnnihilator G theta R r g) =
      ∑ a, ∑ b, ip (tripleRemove a f) (tripleRemove b g) *
        (conj (seedDualMapNat G theta (tripleVacuum b).val r R) *
          seedDualMapNat G theta (tripleVacuum a).val p R) := by
  simp only [natThreeAnnihilator,LinearMap.coe_mk,AddHom.coe_mk,
    LinearMap.sum_apply,LinearMap.smul_apply]
  rw [inner_sum_left]
  simp only [inner_sum_right,TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,
    starRingEnd_apply,star_star]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- A genuine finite scalar cross-Parseval identity transports through the
actual antlinear annihilation map. This is a finite algebraic lemma, not an
isometry premise on the physical insertion. -/
theorem finite_annihilator_cross_congr {ι κ : Type*} (G : Geometry) (theta : Twist)
    (s : Finset ι) (t : Finset κ) (p : ι → Core ℕ ℂ) (r : κ → Core ℕ ℂ)
    (h : ∀ F H : Core ℕ ℂ →ₗ[ℂ] ℂ,
      (∑ i ∈ s, conj (F (p i)) * H (p i)) = ∑ j ∈ t, conj (F (r j)) * H (r j))
    (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i ∈ s, ip (natThreeAnnihilator G theta R (p i) f)
      (natThreeAnnihilator G theta R (p i) g)) =
    ∑ j ∈ t, ip (natThreeAnnihilator G theta R (r j) f)
      (natThreeAnnihilator G theta R (r j) g) := by
  simp_rw [natThreeAnnihilator_cross_expansion]
  rw [Finset.sum_comm (s := s),Finset.sum_comm (s := t)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm (s := s),Finset.sum_comm (s := t)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.mul_sum,← Finset.mul_sum]
  congr 1
  exact h ((LinearMap.proj R).comp (seedDualMapNat G theta (tripleVacuum b).val))
    ((LinearMap.proj R).comp (seedDualMapNat G theta (tripleVacuum a).val))

/-- Complete degree-t Parseval for the original raw a_j B_p outputs. -/
theorem auxiliary_degree_norm_eq (G : Geometry) (theta : Twist) (t : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∑ p : Fin (t+1), q (singleJetAnnihilator G theta (t-p.val) R
      (pairDescendant G theta p.val R f))) =
    ∑ n : Fin (t+1), q (natThreeRemoval G theta (w3RelativeSeed (t-n.val))
      (w3RelativeSeed_bihomogeneous (t-n.val)).1 n.val R f) := by
  have h := finite_annihilator_cross_congr G theta (Finset.univ : Finset (Fin (t+1)))
    (Finset.univ : Finset (Fin (t+1)))
    (fun p => pairCOMSeed p.val*MvPolynomial.X (t-p.val))
    (fun n => normalizedCOMDescendant n.val (w3RelativeSeed (t-n.val)))
    (w3_complete_auxiliary_cross t) R f f
  have hn (d n : ℕ) := natThreeAnnihilator_normalized G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 n R
  simp only [natThreeAnnihilator_pair_spectator,normalizedCOMDescendant_eq_nat,hn] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum,ip,occupationInner_self_re] using hr

/-- Each relative descendant has a genuine L1 square on the original cell. -/
theorem relative_descendant_norm_integrable (G : Geometry) (theta : Twist)
    (d n charge : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => q (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 n R f)) (cellMeasure G charge) := by
  have h := (natThreeRemoval_cross_integrable G theta charge _ _
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1 n n f f).re
  change Integrable (fun R => (ip (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 n R f) (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 n R f)).re) (cellMeasure G charge) at h
  simpa only [ip,occupationInner_self_re] using h

/-- The original charge-two to charge-three cell factor is exactly 2/3. -/
theorem relative_descendant_norm_integral (G : Geometry) (theta : Twist)
    (d n : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, q (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 n R f) ∂cellMeasure G 2) =
      (2/3:ℝ)*w3RelativeForm G theta d f := by
  have h := natThreeRemoval_com_integral G theta _ _
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1
    (w3RelativeSeed_lower d) (w3RelativeSeed_lower d) n n f f
  simp only [ite_true] at h
  have h2 := integral_re (natThreeRemoval_cross_integrable G theta 2 _ _
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1 n n f f)
  have h3 := integral_re (natThreeRemoval_cross_integrable G theta 3 _ _
    (w3RelativeSeed_bihomogeneous d).1 (w3RelativeSeed_bihomogeneous d).1 0 0 f f)
  change (∫ R, (ip (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 n R f) (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 n R f)).re ∂cellMeasure G 2) =
    (∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 n R f) (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 n R f) ∂cellMeasure G 2).re at h2
  change (∫ R, (ip (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 0 R f) (natThreeRemoval G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 0 R f)).re ∂cellMeasure G 3) =
    (∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 0 R f) (natThreeRemoval G theta (w3RelativeSeed d)
      (w3RelativeSeed_bihomogeneous d).1 0 R f) ∂cellMeasure G 3).re at h3
  have hr := congrArg Complex.re h
  rw [show (2/3:ℂ)=((2/3:ℝ):ℂ) by norm_num] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  rw [←h2,←h3] at hr
  simpa only [ip,occupationInner_self_re,w3RelativeForm] using hr

/-- The complete unrotated auxiliary envelope is integrable before integration. -/
theorem auxiliary_degree_integrable (G : Geometry) (theta : Twist) (t : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ∑ p : Fin (t+1), q (singleJetAnnihilator G theta (t-p.val) R
      (pairDescendant G theta p.val R f))) (cellMeasure G 2) := by
  simp_rw [auxiliary_degree_norm_eq]
  exact integrable_finsetSum _ (fun n _ => relative_descendant_norm_integrable G theta _ _ 2 f)

/-- Full degree-t trace of all pair/spectator channels. -/
theorem auxiliary_degree_integral (G : Geometry) (theta : Twist) (t : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ p : Fin (t+1), q (singleJetAnnihilator G theta (t-p.val) R
      (pairDescendant G theta p.val R f)) ∂cellMeasure G 2) =
      (2/3:ℝ)*∑ n : Fin (t+1), w3RelativeForm G theta (t-n.val) f := by
  simp_rw [auxiliary_degree_norm_eq]
  rw [integral_finsetSum _ (fun n _ => relative_descendant_norm_integrable G theta _ _ 2 f)]
  simp only [relative_descendant_norm_integral,Finset.mul_sum]

end TorusLean.Shared.ThermalCoherentBosonRowEnvelope
