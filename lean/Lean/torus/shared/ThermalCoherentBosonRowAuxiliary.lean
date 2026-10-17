import torus.shared.BosonAnchoredTripleRows
import torus.shared.BosonPairCOMCoefficientBound
import torus.shared.BosonRelativeFrameJets

/-! The full auxiliary pair/spectator basis has the actual all-core row
 a_j B_p. This identifies the 45-column metric envelope with genuine W3
source images, before its finite Jacobi trace or any estimate. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowAuxiliary
open TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.BosonPairCOMCoefficientBound TorusLean.Shared.BosonAnchoredTripleRows
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.ThermalCoherentSpectralOccupation
open scoped BigOperators ComplexConjugate
local instance rowAux_nonempty (G : Geometry) (theta : Twist) : Nonempty (OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- The two already proved binomial conventions have exactly the same scalar. -/
theorem pairCOMCoefficient_eq_descendant (p i : ℕ) (hi : i≤p) :
    (pairCOMCoefficientReal p i:ℂ)=((Real.sqrt (2:ℝ))⁻¹:ℂ)*pairDescendantCoeff p i := by
  have h2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have he : pairCOMCoefficientReal p i =
      (Real.sqrt (2:ℝ))⁻¹*Real.sqrt (p.choose i:ℝ)*(Real.sqrt (2:ℝ)/2)^p := by
    apply (sq_eq_sq₀ (by unfold pairCOMCoefficientReal; positivity) (by positivity)).mp
    have hr : ((Real.sqrt (2:ℝ)/2)^p)^2=(1/2:ℝ)^p := by
      rw [←pow_mul,Nat.mul_comm p 2,pow_mul,div_pow,h2]
      norm_num
    rw [pairCOMCoefficientReal_sq p i hi,mul_pow,mul_pow,inv_pow,
      Real.sq_sqrt (by positivity : (0:ℝ)≤p.choose i),h2,hr,pow_succ,div_pow,one_pow]
    field_simp
    <;> ring
  rw [he]
  simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,
    Complex.ofReal_div,Complex.ofReal_ofNat,pairDescendantCoeff,ChargeTwoScaling.scale] <;> ring

/-- Exact original all-core annihilator for every complete auxiliary column. -/
theorem natThreeAnnihilator_pair_spectator (G : Geometry) (theta : Twist) (R : ℂ)
    (p j : ℕ) (f : Core (OrbitalIndex G theta) ℂ) :
    natThreeAnnihilator G theta R (pairCOMSeed p*MvPolynomial.X j) f =
      singleJetAnnihilator G theta j R (pairDescendant G theta p R f) := by
  have hl : natThreeAnnihilator G theta R (pairCOMSeed p*MvPolynomial.X j) f =
      ∑ i ∈ Finset.range (p+1), (pairCOMCoefficientReal p i:ℂ) •
        singleJetAnnihilator G theta j R
          (singleJetAnnihilator G theta (p-i) R (singleJetAnnihilator G theta i R f)) := by
    rw [pairCOMSeed_eq_coefficient_sum,Finset.sum_mul,map_sum,LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_mul_assoc,LinearMap.map_smulₛₗ,LinearMap.smul_apply]
    change conj (pairCOMCoefficientReal p i:ℂ) •
      natThreeAnnihilator G theta R ((MvPolynomial.X i*MvPolynomial.X (p-i))*MvPolynomial.X j) f = _
    rw [Complex.conj_ofReal]
    exact congrArg (fun v => (pairCOMCoefficientReal p i:ℂ) • v)
      (natThreeAnnihilator_triple G theta R i (p-i) j f)
  rw [hl,pairDescendant_eq_raw,map_smul,map_sum,Finset.smul_sum]
  simp only [map_smul,smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pairCOMCoefficient_eq_descendant p i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]


end TorusLean.Shared.ThermalCoherentBosonRowAuxiliary
