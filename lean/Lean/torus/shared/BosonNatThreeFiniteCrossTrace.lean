import torus.shared.BosonNatThreeFiniteTrace

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeFiniteCrossTrace
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.SpectatorControl
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonNatThreeRemovalTrace TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNormalizedNatSeeds
open TorusLean.Shared.BosonNatThreeFiniteTrace
open MeasureTheory
open scoped BigOperators ComplexConjugate

local instance finiteTrace_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem finiteCOMRow_cross_two (ι : Type*) (G : Geometry) (theta : Twist) (s : Finset ι)
    (p : ι → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3) (n : ι → ℕ)
    (c d : ι → ℂ) (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (finiteCOMRow G theta s p hp n c R f) (finiteCOMRow G theta s p hp n d R g) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * conj (d j)) *
        ip (natThreeRemoval G theta (p i) (hp i) (n i) R f)
          (natThreeRemoval G theta (p j) (hp j) (n j) R g) := by
  simp only [finiteCOMRow,inner_sum_left]
  simp only [inner_sum_right,TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,
    starRingEnd_apply,star_star]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteCOMRow_cross_two_integrable (ι : Type*) (G : Geometry) (theta : Twist) (s : Finset ι)
    (p : ι → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3) (n : ι → ℕ)
    (c d : ι → ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ip (finiteCOMRow G theta s p hp n c R f)
      (finiteCOMRow G theta s p hp n d R g)) (cellMeasure G 2) := by
  simp_rw [finiteCOMRow_cross_two]
  exact integrable_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
    (natThreeRemoval_cross_integrable G theta 2 (p i) (p j) (hp i) (hp j)
      (n i) (n j) f g).const_mul _

/-- Orthogonality eliminates distinct COM levels inside a genuine finite
source decomposition. No orthogonality between different relative seeds is
assumed; injectivity of the COM levels is the only finite combinatorial input. -/
theorem finiteCOMRow_integral_cross_diagonal (ι : Type*) [DecidableEq ι]
    (G : Geometry) (theta : Twist) (s : Finset ι)
    (p : ι → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (hL : ∀ i, canonicalCOMLowerNat (p i)=0) (n : ι → ℕ)
    (hn : Set.InjOn n (↑s : Set ι)) (c d : ι → ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (finiteCOMRow G theta s p hp n c R f)
      (finiteCOMRow G theta s p hp n d R g) ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i ∈ s, (c i * conj (d i)) *
      (∫ R, ip (natThreeRemoval G theta (p i) (hp i) 0 R f)
        (natThreeRemoval G theta (p i) (hp i) 0 R g) ∂cellMeasure G 3) := by
  have hi (i j : ι) := (natThreeRemoval_cross_integrable G theta 2
    (p i) (p j) (hp i) (hp j) (n i) (n j) f g).const_mul (c i * conj (d j))
  simp_rw [finiteCOMRow_cross_two]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => hi i j))]
  simp_rw [integral_finsetSum s (fun j _ => hi _ j),integral_const_mul]
  simp_rw [natThreeRemoval_com_integral G theta _ _ (hp _) (hp _) (hL _) (hL _)]
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

end TorusLean.Shared.BosonNatThreeFiniteCrossTrace
