import torus.shared.BosonNormalizedNatSeeds
import torus.shared.ThermalCoherentInsertionThreeLift

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.SpectatorControl
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.BosonThreeBodyLift TorusLean.Shared.ThermalCoherentInsertionThreeLift
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open TorusLean.Shared.BosonNaturalWordSpan TorusLean.Shared.BosonNormalizedNatSeeds
open MeasureTheory
open scoped BigOperators ComplexConjugate

local instance natThreeTrace_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def natThreeSeed (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (n : ℕ) (R : ℂ) : ThreeSector (OrbitalIndex G theta) :=
  ⟨anchoredSeedNat G theta R (normalizedNatSeed 3 n p),
    anchoredSeedNat_sector G theta 3 R _ (normalizedNatSeed_sector 3 n p hp)⟩

def natThreeRemoval (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (n : ℕ) (R : ℂ) :
    Core (OrbitalIndex G theta) ℂ →ₗ[ℂ] Core (OrbitalIndex G theta) ℂ :=
  threeSeedRemoval (natThreeSeed G theta p hp n R)

theorem natThreeRemoval_expansion (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (n : ℕ) (R : ℂ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natThreeRemoval G theta p hp n R f =
      ∑ a, conj (seedDualMapNat G theta (tripleVacuum a).val (normalizedNatSeed 3 n p) R) •
        tripleRemove a f := by
  simp only [natThreeRemoval,threeSeedRemoval,LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact (occupationInner_conj_symm (fun _ => 1) (tripleVacuum a).val
    (anchoredSeedNat G theta R (normalizedNatSeed 3 n p))).symm

theorem natThreeRemoval_cross_expansion (G : Geometry) (theta : Twist) (p r : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (hr : r.IsHomogeneous 3) (n m : ℕ) (R : ℂ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (natThreeRemoval G theta p hp n R f) (natThreeRemoval G theta r hr m R g) =
      ∑ a, ∑ b, ip (tripleRemove a f) (tripleRemove b g) *
        (conj (seedDualMapNat G theta (tripleVacuum b).val (normalizedNatSeed 3 m r) R) *
          seedDualMapNat G theta (tripleVacuum a).val (normalizedNatSeed 3 n p) R) := by
  rw [natThreeRemoval_expansion,natThreeRemoval_expansion,inner_sum_left]
  simp only [inner_sum_right,TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,
    starRingEnd_apply,star_star]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem natThreeRemoval_cross_integrable (G : Geometry) (theta : Twist) (charge : ℕ)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 3) (hr : r.IsHomogeneous 3) (n m : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => ip (natThreeRemoval G theta p hp n R f)
      (natThreeRemoval G theta r hr m R g)) (cellMeasure G charge) := by
  simp_rw [natThreeRemoval_cross_expansion]
  apply continuous_integrable_cellMeasure
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  have hpw := homogeneous_mem_naturalWordSpan 3 _ (normalizedNatSeed_sector 3 n p hp)
  have hrw := homogeneous_mem_naturalWordSpan 3 _ (normalizedNatSeed_sector 3 m r hr)
  exact continuous_const.mul
    (((seedDualNat_contDiff G theta 3 (tripleVacuum b).val _ hrw).continuous.star).mul
      (seedDualNat_contDiff G theta 3 (tripleVacuum a).val _ hpw).continuous)

theorem natThreeRemoval_cross_integral (G : Geometry) (theta : Twist) (charge : ℕ)
    (p r : Core ℕ ℂ) (hp : p.IsHomogeneous 3) (hr : r.IsHomogeneous 3) (n m : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (natThreeRemoval G theta p hp n R f) (natThreeRemoval G theta r hr m R g)
      ∂cellMeasure G charge) =
      ∑ a, ∑ b, ip (tripleRemove a f) (tripleRemove b g) *
        cellInner G charge (seedDualMapNat G theta (tripleVacuum b).val (normalizedNatSeed 3 m r))
          (seedDualMapNat G theta (tripleVacuum a).val (normalizedNatSeed 3 n p)) := by
  have hpw := homogeneous_mem_naturalWordSpan 3 _ (normalizedNatSeed_sector 3 n p hp)
  have hrw := homogeneous_mem_naturalWordSpan 3 _ (normalizedNatSeed_sector 3 m r hr)
  have hi (a b : TripleIndex (OrbitalIndex G theta)) : Integrable (fun R =>
      ip (tripleRemove a f) (tripleRemove b g) *
        (conj (seedDualMapNat G theta (tripleVacuum b).val (normalizedNatSeed 3 m r) R) *
          seedDualMapNat G theta (tripleVacuum a).val (normalizedNatSeed 3 n p) R))
      (cellMeasure G charge) := by
    apply continuous_integrable_cellMeasure
    exact continuous_const.mul
      (((seedDualNat_contDiff G theta 3 (tripleVacuum b).val _ hrw).continuous.star).mul
        (seedDualNat_contDiff G theta 3 (tripleVacuum a).val _ hpw).continuous)
  simp_rw [natThreeRemoval_cross_expansion]
  rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum Finset.univ (fun b _ => hi _ b),integral_const_mul]
  rfl

/-- True all-core COM orthogonality of the original normalized three-body
annihilation rows. No bound on the input particle number is introduced. -/
theorem natThreeRemoval_com_integral (G : Geometry) (theta : Twist) (p r : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hpL : canonicalCOMLowerNat p=0) (hrL : canonicalCOMLowerNat r=0)
    (n m : ℕ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ip (natThreeRemoval G theta p hp n R f) (natThreeRemoval G theta r hr m R g)
      ∂cellMeasure G 2) =
      if n=m then (2/3:ℂ) *
        (∫ R, ip (natThreeRemoval G theta p hp 0 R f) (natThreeRemoval G theta r hr 0 R g)
          ∂cellMeasure G 3) else 0 := by
  rw [natThreeRemoval_cross_integral,natThreeRemoval_cross_integral]
  simp_rw [anchored_normalizedNatSeed_mu2 G theta 3 _ _ r p hr hp hrL hpL m n]
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

end TorusLean.Shared.BosonNatThreeRemovalTrace
