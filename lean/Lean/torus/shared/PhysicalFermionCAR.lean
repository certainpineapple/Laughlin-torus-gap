import torus.shared.PhysicalFermionCarrier
import torus.shared.LLLThetaGaugeInverse
import torus.shared.PlaneJetReproducing
import RawCARNorm

/-!
# Actual torus orbitals in the existing OAI exterior CAR representation

Only the actual one-particle LLL is coordinatized here, by its actual cell ON
basis. `physicalQ = finrank - 1` is merely the index convention required by
OAI's `Fin (Q+1)` orbital type; it is not a sphere flux identification.
The untouched OAI declarations are loaded through the explicitly documented
import-only adaptation. No many-body physical/exterior isometry is claimed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionCAR

open MeasureTheory TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.PlaneJetMembership
open scoped ComplexConjugate

/-- The OAI address parameter, derived from the actual torus orbital dimension. -/
def physicalQ (G : Geometry) (theta : Twist) : ℕ :=
  Module.finrank ℂ (LLL G theta 1) - 1

theorem physicalQ_succ (G : Geometry) (theta : Twist) :
    physicalQ G theta + 1 = Module.finrank ℂ (LLL G theta 1) :=
  Nat.sub_add_cancel (lll_finrank_pos G theta 1)

def physicalIndexEquiv (G : Geometry) (theta : Twist) :
    Fin (physicalQ G theta + 1) ≃ OrbitalIndex G theta := finCongr (physicalQ_succ G theta)

/-- A genuine onto linear coordinate equivalence, from the physical LLL,
rather than a supplied finite vector model. -/
def physicalOrbitalCoordinates (G : Geometry) (theta : Twist) :
    LLL G theta 1 ≃ₗ[ℂ] Orbital (physicalQ G theta) :=
  (orbitalBasis G theta).toBasis.equivFun.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (physicalQ G theta+1) => ℂ)
      (physicalIndexEquiv G theta).symm)

theorem physicalOrbitalCoordinates_apply (G : Geometry) (theta : Twist)
    (v : LLL G theta 1) (i : Fin (physicalQ G theta + 1)) :
    physicalOrbitalCoordinates G theta v i =
      inner ℂ (orbitalBasis G theta (physicalIndexEquiv G theta i)) v := by
  change (orbitalBasis G theta).toBasis.equivFun v (physicalIndexEquiv G theta i) = _
  rw [Module.Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]

/-- The OAI CAR contraction is exactly the original cell inner product. -/
theorem physicalOrbitalCoordinates_gram (G : Geometry) (theta : Twist)
    (v w : LLL G theta 1) :
    rawGram (physicalQ G theta) (physicalOrbitalCoordinates G theta v)
      (physicalOrbitalCoordinates G theta w) = cellInner G 1 v.val w.val := by
  rw [rawGram_eq_sum]
  simp only [physicalOrbitalCoordinates_apply, Complex.star_def]
  have h := Equiv.sum_comp (physicalIndexEquiv G theta)
    (fun i => conj (inner ℂ (orbitalBasis G theta i) v) * inner ℂ (orbitalBasis G theta i) w)
  rw [h]
  simp_rw [inner_conj_symm]
  rw [OrthonormalBasis.sum_inner_mul_inner, lll_inner_eq_cellInner]

/-- Physical creation uses the same exterior left multiplication as OAI. -/
def physicalCreate (G : Geometry) (theta : Twist) (v : LLL G theta 1) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  rawCreate (physicalQ G theta) (physicalOrbitalCoordinates G theta v)

def physicalAnnihilate (G : Geometry) (theta : Twist) (v : LLL G theta 1) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  vectorAnnihilate (physicalQ G theta) (physicalOrbitalCoordinates G theta v)

/-- Exact CAR for arbitrary actual torus LLL functions, without normalizing
raw coherent/jet vectors or replacing their Gram by the identity. -/
theorem physical_CAR (G : Geometry) (theta : Twist) (v w : LLL G theta 1) :
    physicalAnnihilate G theta v * physicalCreate G theta w =
      cellInner G 1 v.val w.val • (1 : Module.End ℂ (Space (physicalQ G theta))) -
        physicalCreate G theta w * physicalAnnihilate G theta v := by
  unfold physicalAnnihilate physicalCreate
  rw [raw_annihilate_create, physicalOrbitalCoordinates_gram]

theorem physicalCreate_adjoint (G : Geometry) (theta : Twist) (v : LLL G theta 1)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) (physicalCreate G theta v x) y =
      occupationInner (physicalQ G theta) x (physicalAnnihilate G theta v y) :=
  rawCreate_adjoint _ _ _ _

/-- Actual original periodized jets in the same complete finite coordinates. -/
def physicalJetCoordinates (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    Orbital (physicalQ G theta) :=
  physicalOrbitalCoordinates G theta (rawPlaneJet G theta j R)

/-- Jet contraction retains the actual canonical derivative coefficient. -/
theorem physicalJetCoordinates_reproduces (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (v : LLL G theta 1) :
    rawGram (physicalQ G theta) (physicalJetCoordinates G theta j R)
      (physicalOrbitalCoordinates G theta v) = rawJetCoefficient G theta v j R := by
  rw [physicalJetCoordinates, physicalOrbitalCoordinates_gram]
  exact rawPlaneJet_cell_reproduces G theta v j R

/-- The physical jet CAR scalar is its derivative evaluation, not δij. -/
theorem physical_jet_CAR (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (v : LLL G theta 1) :
    physicalAnnihilate G theta (rawPlaneJet G theta j R) * physicalCreate G theta v =
      rawJetCoefficient G theta v j R • (1 : Module.End ℂ (Space (physicalQ G theta))) -
        physicalCreate G theta v * physicalAnnihilate G theta (rawPlaneJet G theta j R) := by
  have hrep : cellInner G 1 (rawPlaneJet G theta j R).val v.val = rawJetCoefficient G theta v j R :=
    rawPlaneJet_cell_reproduces G theta v j R
  rw [physical_CAR, hrep]

/-- Pair CAR keeps the unnormalized determinant of the actual physical Gram. -/
theorem physical_pair_gram (G : Geometry) (theta : Twist) (a b c d : LLL G theta 1) :
    rawPairGram (physicalQ G theta)
      (physicalOrbitalCoordinates G theta a) (physicalOrbitalCoordinates G theta b)
      (physicalOrbitalCoordinates G theta c) (physicalOrbitalCoordinates G theta d) =
      cellInner G 1 a.val c.val * cellInner G 1 b.val d.val -
        cellInner G 1 b.val c.val * cellInner G 1 a.val d.val := by
  simp only [rawPairGram, physicalOrbitalCoordinates_gram]

/-- Coordinate square norm is exactly the original one-particle cell integral. -/
theorem physicalOrbitalCoordinates_normSq (G : Geometry) (theta : Twist)
    (v : LLL G theta 1) :
    (∑ i, ‖physicalOrbitalCoordinates G theta v i‖^2) =
      ∫ z, ‖v.val z‖^2 ∂cellMeasure G 1 := by
  have h := physicalOrbitalCoordinates_gram G theta v v
  rw [rawGram_self_eq_coordinateNormSq, cellInner_self] at h
  simpa only [Complex.ofReal_re] using congrArg Complex.re h

/-- Existing generic CAR norm theorem instantiated with actual physical
orbital norm, not the default sup norm of OAI's raw Pi coordinates. -/
theorem physical_CAR_normSq (G : Geometry) (theta : Twist)
    (v : LLL G theta 1) (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (physicalAnnihilate G theta v x) +
      occupationNormSq (physicalQ G theta) (physicalCreate G theta v x) =
      (∫ z, ‖v.val z‖^2 ∂cellMeasure G 1) * occupationNormSq (physicalQ G theta) x := by
  unfold physicalAnnihilate physicalCreate
  rw [raw_CAR_normSq_identity, physicalOrbitalCoordinates_normSq]

#print axioms physicalOrbitalCoordinates_normSq
#print axioms physical_CAR_normSq

#print axioms physicalQ_succ
#print axioms physicalOrbitalCoordinates_apply
#print axioms physicalOrbitalCoordinates_gram
#print axioms physical_CAR
#print axioms physicalCreate_adjoint
#print axioms physicalJetCoordinates_reproduces
#print axioms physical_jet_CAR
#print axioms physical_pair_gram

end TorusLean.Shared.PhysicalFermionCAR
