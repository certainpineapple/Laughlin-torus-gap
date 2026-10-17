import torus.shared.BosonNatThreeFiniteCrossTrace
import torus.shared.BosonThermalJacobiRows
import torus.shared.ThermalCoherentJacobiAnchoredAlgebra
import torus.shared.NatAnchoredThreeAction

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredKRows
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeRemovalTrace TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeFiniteTrace TorusLean.Shared.BosonNatThreeFiniteCrossTrace
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonNormalizedNatSeeds
open TorusLean.Shared.ThermalCoherentJacobiInsertion TorusLean.Shared.ThermalCoherentJacobiWeights
open TorusLean.Shared.ThermalCoherentJacobiAnchored
open MeasureTheory
open scoped BigOperators ComplexConjugate

local instance anchoredRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Identification with the independently defined original anchored operator,
on its actual total-degree block. The rank coefficient is two at degree zero;
the unnormalized ket has squared norm three. -/
theorem original_K_block_rank (l : ℕ) (p : Core ℕ ℂ)
    (hN : p.IsHomogeneous 3) (hd : p.IsWeightedHomogeneous id l) :
    natAnchoredThreeK p = ((anchoredKernelCoefficient l : ℂ) *
      natOccupationInner (pairAnchoredSeed l) p) • w3Seed l := by
  rw [natAnchoredThreeK_rank l p hN hd]
  simp only [natAnchoredThreeKet,natAnchoredThreeBra,pairAnchoredSeed,
    natAnchoredThreeDecay,anchoredKernelCoefficient,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat,div_eq_mul_inv,mul_assoc]

theorem pairAnchored_row_jacobi (G : Geometry) (theta : Twist) (l : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natThreeAnnihilator G theta R (pairAnchoredSeed l) f =
      finiteCOMRow G theta (Finset.range (l+1)) w3RelativeSeed
        (fun d => (w3RelativeSeed_bihomogeneous d).1) (fun d => l-d)
        (fun d => (pairAnchoredJacobiAmplitude (l-d) d : ℂ)) R f := by
  have hn (d : ℕ) := natThreeAnnihilator_normalized G theta (w3RelativeSeed d)
    (w3RelativeSeed_bihomogeneous d).1 (l-d) R
  rw [pairAnchoredSeed_jacobi_decomposition]
  simp only [map_sum,LinearMap.map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply,
    normalizedCOMDescendant_eq_nat,hn,starRingEnd_apply,finiteCOMRow]

/-- Actual physical block rank form of the original anchored K, before any
infinite COM summation or claim about the original torus single contraction. -/
def anchoredBlockForm (G : Geometry) (theta : Twist) (l : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) : ℂ :=
  ∫ R, (anchoredKernelCoefficient l : ℂ) *
    ip (natThreeAnnihilator G theta R (w3Seed l) f)
      (natThreeAnnihilator G theta R (pairAnchoredSeed l) g) ∂cellMeasure G 2

theorem anchoredBlockForm_finite_COM (G : Geometry) (theta : Twist) (l : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    anchoredBlockForm G theta l f g =
      ∑ d ∈ Finset.range (l+1), (anchoredJacobiCrossWeight d (l-d) : ℂ) *
        (∫ R, ip (natThreeRemoval G theta (w3RelativeSeed d)
          (w3RelativeSeed_bihomogeneous d).1 0 R f)
          (natThreeRemoval G theta (w3RelativeSeed d)
          (w3RelativeSeed_bihomogeneous d).1 0 R g) ∂cellMeasure G 3) := by
  have hn : Set.InjOn (fun d : ℕ => l-d) (↑(Finset.range (l+1)) : Set ℕ) := by
    intro d hd e he h
    have hd' := Finset.mem_range.mp hd
    have he' := Finset.mem_range.mp he
    change l-d=l-e at h
    omega
  unfold anchoredBlockForm
  simp_rw [w3Annihilator_eq_original,LinearMap.comp_apply,w3_row_jacobi,
    pairAnchored_row_jacobi]
  rw [integral_const_mul,finiteCOMRow_integral_cross_diagonal ℕ G theta
    (Finset.range (l+1)) w3RelativeSeed (fun d => (w3RelativeSeed_bihomogeneous d).1)
    w3RelativeSeed_lower (fun d => l-d) hn]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have he : l-d+d=l := by have := Finset.mem_range.mp hd; omega
  simp only [anchoredJacobiCrossWeight,he,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat,Complex.conj_ofReal]
  ring

end TorusLean.Shared.BosonAnchoredKRows
