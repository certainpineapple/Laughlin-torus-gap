import torus.shared.BosonNatFourAnnihilator

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourFiniteTrace
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.SpectatorControl
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Shared.ThermalCoherentFourBodyFrame
open TorusLean.Shared.BosonNatFourRemovalTrace TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Shared.BosonNormalizedNatSeeds
open MeasureTheory
open scoped BigOperators ComplexConjugate

local instance finiteTrace_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Finite Jacobi row sums use the genuine annihilation operators. Complex
coefficients are conjugated because the source-to-removal map is antilinear. -/
def finiteCOMRow {ι : Type*} (G : Geometry) (theta : Twist) (s : Finset ι)
    (p : ι → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4) (n : ι → ℕ)
    (c : ι → ℂ) (R : ℂ) (f : Core (OrbitalIndex G theta) ℂ) :=
  ∑ i ∈ s, conj (c i) • natFourRemoval G theta (p i) (hp i) (n i) R f

theorem finiteCOMRow_cross (ι : Type*) (G : Geometry) (theta : Twist) (s : Finset ι)
    (p : ι → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4) (n : ι → ℕ)
    (c : ι → ℂ) (R : ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    ip (finiteCOMRow G theta s p hp n c R f) (finiteCOMRow G theta s p hp n c R f) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * conj (c j)) *
        ip (natFourRemoval G theta (p i) (hp i) (n i) R f)
          (natFourRemoval G theta (p j) (hp j) (n j) R f) := by
  rw [finiteCOMRow,inner_sum_left]
  simp only [inner_sum_right,TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,
    starRingEnd_apply,star_star]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteCOMRow_integrable (ι : Type*) (G : Geometry) (theta : Twist) (s : Finset ι)
    (p : ι → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4) (n : ι → ℕ)
    (c : ι → ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ip (finiteCOMRow G theta s p hp n c R f)
      (finiteCOMRow G theta s p hp n c R f)) (cellMeasure G 2) := by
  simp_rw [finiteCOMRow_cross]
  exact integrable_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
    (natFourRemoval_cross_integrable G theta 2 (p i) (p j) (hp i) (hp j)
      (n i) (n j) f f).const_mul _

/-- Orthogonality eliminates distinct COM levels inside a genuine finite
source decomposition. No orthogonality between different relative seeds is
assumed; injectivity of the COM levels is the only finite combinatorial input. -/
theorem finiteCOMRow_integral_diagonal (ι : Type*) [DecidableEq ι]
    (G : Geometry) (theta : Twist) (s : Finset ι)
    (p : ι → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 4)
    (hL : ∀ i, canonicalCOMLowerNat (p i)=0) (n : ι → ℕ)
    (hn : Set.InjOn n (↑s : Set ι)) (c : ι → ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (finiteCOMRow G theta s p hp n c R f)
      (finiteCOMRow G theta s p hp n c R f) ∂cellMeasure G 2) =
    (2/4:ℂ) * ∑ i ∈ s, (c i * conj (c i)) *
      (∫ R, ip (natFourRemoval G theta (p i) (hp i) 0 R f)
        (natFourRemoval G theta (p i) (hp i) 0 R f) ∂cellMeasure G 4) := by
  have hi (i j : ι) := (natFourRemoval_cross_integrable G theta 2
    (p i) (p j) (hp i) (hp j) (n i) (n j) f f).const_mul (c i * conj (c j))
  simp_rw [finiteCOMRow_cross]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => hi i j))]
  simp_rw [integral_finsetSum s (fun j _ => hi _ j),integral_const_mul]
  simp_rw [natFourRemoval_com_integral G theta _ _ (hp _) (hp _) (hL _) (hL _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i his
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j hjs hji
    have hne : n i ≠ n j := fun h => hji (hn his hjs h).symm
    simp only [hne,ite_false,mul_zero]
  · exact fun h => (h his).elim

end TorusLean.Shared.BosonNatFourFiniteTrace
