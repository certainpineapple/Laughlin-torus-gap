import torus.shared.ThermalCoherentSeedWord

/-! Genuine smooth dual parameter sections of finite anchored word families.
The domain fields are consequences of the actual raw-word expansion and the
original boundary law. No ladder-action or COM identity is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSeedDomain
open TorusLean.Boson TorusLean.Geometry
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.BosonPeriodizedSeed
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetWord
open TorusLean.Shared.ThermalCoherentSeedWord
open scoped BigOperators ComplexConjugate ContDiff

/-- Finite complex linear combinations retain the same original dual charge
and twist; there is no assumption of individual periodicity. -/
theorem hasDualBoundary_finset_linear {I : Type*} (G : Geometry) (theta : Twist) (k : ℕ)
    (s : Finset I) (c : I → ℂ) (f : I → ℂ → ℂ)
    (hf : ∀ i ∈ s, HasDualBoundary G theta k (f i)) :
    HasDualBoundary G theta k (fun R => ∑ i ∈ s, c i * f i R) := by
  intro p
  funext R
  simp only [magneticTranslate, map_sum, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrFun (hf i hi p) R
  simp only [magneticTranslate] at h
  calc
    _ = conj (c i) * (Complex.exp (magneticExponent (k:ℝ) R
      (latticePeriod G.omega1 G.omega2 p)) * conj (f i (R-latticePeriod G.omega1 G.omega2 p))) := by ring
    _ = _ := by rw [h]; ring

theorem anchoredSeed_word_dual_contDiff (G : Geometry) (theta : Twist) (K k : ℕ)
    (j : Fin k → Fin K) (q : Core (OrbitalIndex G theta) ℂ) :
    ContDiff ℝ ∞ (fun R => occupationInner (fun _ => 1) q
      (anchoredSeed G theta K R (canonicalWord k j))) := by
  simp_rw [anchoredSeed_word_dual_expansion]
  apply ContDiff.sum
  intro w hw
  exact contDiff_const.mul (rawWord_contDiff G theta k _ _)

theorem anchoredSeed_word_dual_boundary (G : Geometry) (theta : Twist) (K k : ℕ)
    (j : Fin k → Fin K) (q : Core (OrbitalIndex G theta) ℂ) :
    HasDualBoundary G theta k (fun R => occupationInner (fun _ => 1) q
      (anchoredSeed G theta K R (canonicalWord k j))) := by
  simp_rw [anchoredSeed_word_dual_expansion]
  exact hasDualBoundary_finset_linear G theta k Finset.univ _ _
    (fun w _ => rawWord_hasDualBoundary G theta k _ _)

/-- The actual finite canonical seed polynomial, with fixed coefficients. -/
def finiteWordSeed {I : Type*} (K k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → Fin K) : Core (Fin K) ℂ :=
  ∑ i ∈ s, c i • canonicalWord k (j i)

theorem finiteWordSeed_sector {I : Type*} (K k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → Fin K) :
    (finiteWordSeed K k s c j).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  rw [MvPolynomial.smul_eq_C_mul]
  exact (canonicalWord_sector k (j i)).C_mul _

theorem anchoredSeed_finiteWord_dual_expansion {I : Type*} (G : Geometry) (theta : Twist)
    (K k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → Fin K)
    (q : Core (OrbitalIndex G theta) ℂ) (R : ℂ) :
    occupationInner (fun _ => 1) q (anchoredSeed G theta K R (finiteWordSeed K k s c j)) =
      ∑ i ∈ s, c i * occupationInner (fun _ => 1) q
        (anchoredSeed G theta K R (canonicalWord k (j i))) := by
  classical
  simp only [finiteWordSeed, map_sum, map_smul]
  induction s using Finset.induction_on with
  | empty => simp [occupationInner_zero_right]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, occupationInner_add_right,
      occupationInner_smul_right, ih]

theorem anchoredSeed_finiteWord_dual_contDiff {I : Type*} (G : Geometry) (theta : Twist)
    (K k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → Fin K)
    (q : Core (OrbitalIndex G theta) ℂ) :
    ContDiff ℝ ∞ (fun R => occupationInner (fun _ => 1) q
      (anchoredSeed G theta K R (finiteWordSeed K k s c j))) := by
  simp_rw [anchoredSeed_finiteWord_dual_expansion]
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul (anchoredSeed_word_dual_contDiff G theta K k (j i) q)

theorem anchoredSeed_finiteWord_dual_boundary {I : Type*} (G : Geometry) (theta : Twist)
    (K k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → Fin K)
    (q : Core (OrbitalIndex G theta) ℂ) :
    HasDualBoundary G theta k (fun R => occupationInner (fun _ => 1) q
      (anchoredSeed G theta K R (finiteWordSeed K k s c j))) := by
  simp_rw [anchoredSeed_finiteWord_dual_expansion]
  exact hasDualBoundary_finset_linear G theta k s c _
    (fun i _ => anchoredSeed_word_dual_boundary G theta K k (j i) q)

theorem physicalAnchoredSeed_finiteWord_dual_eq {I : Type*} (G : Geometry) (theta : Twist)
    (K k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → Fin K)
    (q : PhysicalBosonCarrier G theta k) (R : ℂ) :
    sectorInner G k q.val (physicalAnchoredSeed G theta K k R
      (finiteWordSeed K k s c j) (finiteWordSeed_sector K k s c j)).val =
      occupationInner (fun _ => 1) ((physicalSectorEquiv G theta k).symm q).val
        (anchoredSeed G theta K R (finiteWordSeed K k s c j)) := by
  rw [physicalSectorEquiv_inner]
  have h : ((physicalSectorEquiv G theta k).symm (physicalAnchoredSeed G theta K k R
      (finiteWordSeed K k s c j) (finiteWordSeed_sector K k s c j))).val =
      anchoredSeed G theta K R (finiteWordSeed K k s c j) :=
    congrArg Subtype.val ((physicalSectorEquiv G theta k).symm_apply_apply _)
  rw [h]

theorem physicalAnchoredSeed_finiteWord_dual_contDiff {I : Type*} (G : Geometry) (theta : Twist)
    (K k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → Fin K)
    (q : PhysicalBosonCarrier G theta k) :
    ContDiff ℝ ∞ (fun R => sectorInner G k q.val (physicalAnchoredSeed G theta K k R
      (finiteWordSeed K k s c j) (finiteWordSeed_sector K k s c j)).val) := by
  simp_rw [physicalAnchoredSeed_finiteWord_dual_eq]
  exact anchoredSeed_finiteWord_dual_contDiff G theta K k s c j _

theorem physicalAnchoredSeed_finiteWord_dual_boundary {I : Type*} (G : Geometry) (theta : Twist)
    (K k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → Fin K)
    (q : PhysicalBosonCarrier G theta k) :
    HasDualBoundary G theta k (fun R => sectorInner G k q.val (physicalAnchoredSeed G theta K k R
      (finiteWordSeed K k s c j) (finiteWordSeed_sector K k s c j)).val) := by
  simp_rw [physicalAnchoredSeed_finiteWord_dual_eq]
  exact anchoredSeed_finiteWord_dual_boundary G theta K k s c j _

end TorusLean.Shared.ThermalCoherentSeedDomain
