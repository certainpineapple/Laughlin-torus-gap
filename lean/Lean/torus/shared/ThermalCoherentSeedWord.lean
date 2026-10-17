import torus.shared.ParameterRawJetWord
import torus.shared.BosonPeriodizedSeed

/-! Exact finite word coordinates of the actual anchored seed. The original
factorial occupation metric is retained. This is a finite algebraic bridge to
the already constructed raw parameter words, without COM or isometry premises. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSeedWord
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.BosonPeriodizedSeed
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterRawJetWord
open scoped BigOperators

/-- An ordered canonical oscillator word. Repeated labels and the empty word
are included, with no implicit unit normalization of the resulting polynomial. -/
def canonicalWord {ι : Type*} (k : ℕ) (j : Fin k → ι) : Core ι ℂ :=
  ∏ a, MvPolynomial.X (j a)

theorem canonicalWord_sector {ι : Type*} (k : ℕ) (j : Fin k → ι) :
    (canonicalWord k j).IsHomogeneous k := by
  simpa [canonicalWord] using MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun a : Fin k => MvPolynomial.X (j a) : Fin k → Core ι ℂ)
    (fun _ => 1) (fun a _ => MvPolynomial.isHomogeneous_X ℂ (j a))

/-- Exact product-of-sums expansion; all physical orbital assignments remain. -/
theorem modeLinear_word_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (u : Fin k → Orbital ι) :
    (∏ a, modeLinear (u a)) =
      ∑ w : Fin k → ι, (∏ a, u a (w a)) • canonicalWord k w := by
  simp only [modeLinear]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp only [canonicalWord, MvPolynomial.smul_eq_C_mul]

theorem anchoredSeed_word (G : Geometry) (theta : Twist) (K k : ℕ)
    (j : Fin k → Fin K) (R : ℂ) :
    anchoredSeed G theta K R (canonicalWord k j) =
      ∏ a, modeLinear ((orbitalBasis G theta).repr (rawPlaneJet G theta (j a).val R)) := by
  simp only [canonicalWord, map_prod, anchoredSeed_X]

theorem actualJetCoordinate_eq_dualRaw (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (i : OrbitalIndex G theta) :
    ((orbitalBasis G theta).repr (rawPlaneJet G theta j R)) i =
      dualRawJetScalar G theta (orbitalBasis G theta i) j R := by
  rw [OrthonormalBasis.repr_apply_apply]
  rfl

/-- The finite anchored seed itself, not just a formal coefficient surrogate,
is a sum of fixed physical occupation words times the true rawWord sections. -/
theorem anchoredSeed_word_expansion (G : Geometry) (theta : Twist) (K k : ℕ)
    (j : Fin k → Fin K) (R : ℂ) :
    anchoredSeed G theta K R (canonicalWord k j) =
      ∑ w : Fin k → OrbitalIndex G theta,
        rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val) R •
          canonicalWord k w := by
  rw [anchoredSeed_word, modeLinear_word_expansion]
  simp only [rawWord, actualJetCoordinate_eq_dualRaw]

/-- Dual orientation agrees with the parameter-word convention: the first
occupation argument is fixed and the true anchored seed is the second. -/
theorem anchoredSeed_word_dual_expansion (G : Geometry) (theta : Twist) (K k : ℕ)
    (j : Fin k → Fin K) (q : Core (OrbitalIndex G theta) ℂ) (R : ℂ) :
    occupationInner (fun _ => 1) q (anchoredSeed G theta K R (canonicalWord k j)) =
      ∑ w : Fin k → OrbitalIndex G theta,
        occupationInner (fun _ => 1) q (canonicalWord k w) *
          rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val) R := by
  rw [anchoredSeed_word_expansion]
  have hs (s : Finset (Fin k → OrbitalIndex G theta))
      (g : (Fin k → OrbitalIndex G theta) → Core (OrbitalIndex G theta) ℂ) :
      occupationInner (fun _ => 1) q (∑ w ∈ s, g w) =
        ∑ w ∈ s, occupationInner (fun _ => 1) q (g w) := by
    induction s using Finset.induction_on with
    | empty => simp [occupationInner_zero_right]
    | @insert w s hw ih => simp [hw, occupationInner_add_right, ih]
  rw [hs]
  simp only [occupationInner_smul_right, mul_comm]

/-- Full physical carrier version of the same exact finite dual analysis. -/
theorem physicalAnchoredSeed_word_dual_expansion (G : Geometry) (theta : Twist) (K k : ℕ)
    (j : Fin k → Fin K) (q : PhysicalBosonCarrier G theta k) (R : ℂ) :
    sectorInner G k q.val
      (physicalAnchoredSeed G theta K k R (canonicalWord k j) (canonicalWord_sector k j)).val =
      ∑ w : Fin k → OrbitalIndex G theta,
        occupationInner (fun _ => 1) ((physicalSectorEquiv G theta k).symm q).val
          (canonicalWord k w) *
            rawWord G theta k (fun a => orbitalBasis G theta (w a)) (fun a => (j a).val) R := by
  rw [physicalSectorEquiv_inner]
  have h : ((physicalSectorEquiv G theta k).symm
      (physicalAnchoredSeed G theta K k R (canonicalWord k j) (canonicalWord_sector k j))).val =
      anchoredSeed G theta K R (canonicalWord k j) :=
    congrArg Subtype.val ((physicalSectorEquiv G theta k).symm_apply_apply _)
  rw [h]
  exact anchoredSeed_word_dual_expansion G theta K k j _ R

end TorusLean.Shared.ThermalCoherentSeedWord
