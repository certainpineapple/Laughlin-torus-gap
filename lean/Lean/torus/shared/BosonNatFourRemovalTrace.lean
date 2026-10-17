import torus.shared.BosonNormalizedNatSeeds
import torus.shared.ThermalCoherentInsertionFourLift

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.SpectatorControl
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.ThermalCoherentFourBodyFrame TorusLean.Shared.ThermalCoherentFourBodyLift TorusLean.Shared.ThermalCoherentInsertionFourLift
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open TorusLean.Shared.BosonNaturalWordSpan TorusLean.Shared.BosonNormalizedNatSeeds
open MeasureTheory
open scoped BigOperators ComplexConjugate

local instance natFourTrace_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def natFourSeed (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 4) (n : ℕ) (R : ℂ) : FourSector (OrbitalIndex G theta) :=
  ⟨anchoredSeedNat G theta R (normalizedNatSeed 4 n p),
    anchoredSeedNat_sector G theta 4 R _ (normalizedNatSeed_sector 4 n p hp)⟩

def natFourRemoval (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 4) (n : ℕ) (R : ℂ) :
    Core (OrbitalIndex G theta) ℂ →ₗ[ℂ] Core (OrbitalIndex G theta) ℂ :=
  fourSeedRemoval (natFourSeed G theta p hp n R)

theorem natFourRemoval_expansion (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 4) (n : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natFourRemoval G theta p hp n R f =
      ∑ a, conj (seedDualMapNat G theta (quadVacuum a).val (normalizedNatSeed 4 n p) R) •
        quadRemove a f := by
  simp only [natFourRemoval,fourSeedRemoval,LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact (occupationInner_conj_symm (fun _ => 1) (quadVacuum a).val
    (anchoredSeedNat G theta R (normalizedNatSeed 4 n p))).symm

theorem natFourRemoval_cross_expansion (G : Geometry) (theta : Twist) (p r : Core ℕ ℂ)
    (hp : p.IsHomogeneous 4) (hr : r.IsHomogeneous 4) (n m : ℕ) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (natFourRemoval G theta p hp n R f) (natFourRemoval G theta r hr m R g) =
      ∑ a, ∑ b, ip (quadRemove a f) (quadRemove b g) *
        (conj (seedDualMapNat G theta (quadVacuum b).val (normalizedNatSeed 4 m r) R) *
          seedDualMapNat G theta (quadVacuum a).val (normalizedNatSeed 4 n p) R) := by
  rw [natFourRemoval_expansion,natFourRemoval_expansion,inner_sum_left]
  simp only [inner_sum_right,TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,
    starRingEnd_apply,star_star]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem natFourRemoval_cross_integrable (G : Geometry) (theta : Twist) (charge : ℕ)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 4) (hr : r.IsHomogeneous 4) (n m : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ip (natFourRemoval G theta p hp n R f)
      (natFourRemoval G theta r hr m R g)) (cellMeasure G charge) := by
  simp_rw [natFourRemoval_cross_expansion]
  apply continuous_integrable_cellMeasure
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  have hpw := homogeneous_mem_naturalWordSpan 4 _ (normalizedNatSeed_sector 4 n p hp)
  have hrw := homogeneous_mem_naturalWordSpan 4 _ (normalizedNatSeed_sector 4 m r hr)
  exact continuous_const.mul
    (((seedDualNat_contDiff G theta 4 (quadVacuum b).val _ hrw).continuous.star).mul
      (seedDualNat_contDiff G theta 4 (quadVacuum a).val _ hpw).continuous)

theorem natFourRemoval_cross_integral (G : Geometry) (theta : Twist) (charge : ℕ)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 4) (hr : r.IsHomogeneous 4) (n m : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (natFourRemoval G theta p hp n R f) (natFourRemoval G theta r hr m R g)
      ∂cellMeasure G charge) =
      ∑ a, ∑ b, ip (quadRemove a f) (quadRemove b g) *
        cellInner G charge (seedDualMapNat G theta (quadVacuum b).val (normalizedNatSeed 4 m r))
          (seedDualMapNat G theta (quadVacuum a).val (normalizedNatSeed 4 n p)) := by
  have hpw := homogeneous_mem_naturalWordSpan 4 _ (normalizedNatSeed_sector 4 n p hp)
  have hrw := homogeneous_mem_naturalWordSpan 4 _ (normalizedNatSeed_sector 4 m r hr)
  have hi (a b : QuadIndex (OrbitalIndex G theta)) : Integrable (fun R =>
      ip (quadRemove a f) (quadRemove b g) *
        (conj (seedDualMapNat G theta (quadVacuum b).val (normalizedNatSeed 4 m r) R) *
          seedDualMapNat G theta (quadVacuum a).val (normalizedNatSeed 4 n p) R))
      (cellMeasure G charge) := by
    apply continuous_integrable_cellMeasure
    exact continuous_const.mul
      (((seedDualNat_contDiff G theta 4 (quadVacuum b).val _ hrw).continuous.star).mul
        (seedDualNat_contDiff G theta 4 (quadVacuum a).val _ hpw).continuous)
  simp_rw [natFourRemoval_cross_expansion]
  rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum Finset.univ (fun b _ => hi _ b),integral_const_mul]
  rfl

/-- True all-core COM orthogonality of the original normalized four-body
annihilation rows. No bound on the input particle number is introduced. -/
theorem natFourRemoval_com_integral (G : Geometry) (theta : Twist) (p r : Core ℕ ℂ)
    (hp : p.IsHomogeneous 4) (hr : r.IsHomogeneous 4)
    (hpL : canonicalCOMLowerNat p=0) (hrL : canonicalCOMLowerNat r=0)
    (n m : ℕ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (natFourRemoval G theta p hp n R f) (natFourRemoval G theta r hr m R g)
      ∂cellMeasure G 2) =
      if n=m then (2/4:ℂ) *
        (∫ R, ip (natFourRemoval G theta p hp 0 R f) (natFourRemoval G theta r hr 0 R g)
          ∂cellMeasure G 4) else 0 := by
  rw [natFourRemoval_cross_integral,natFourRemoval_cross_integral]
  simp_rw [anchored_normalizedNatSeed_mu2 G theta 4 _ _ r p hr hp hrL hpL m n]
  by_cases h : n=m
  · subst m
    simp only [ite_true,normalizedNatSeed_zero,Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_ofNat]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  · simp only [h,Ne.symm h,ite_false,mul_zero,Finset.sum_const_zero]

end TorusLean.Shared.BosonNatFourRemovalTrace
