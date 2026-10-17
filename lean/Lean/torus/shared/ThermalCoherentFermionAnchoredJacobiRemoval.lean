import torus.shared.ThermalCoherentFermionAnchoredSource

/-! Occupation adjoints of actual exterior insertion. This is a finite
coordinate construction on the existing CAR space, with its existing inner
product. It introduces no exterior norm or isometry. The final cross-form
identity records explicitly the reversed Hermitian slots of the seed duals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.FermionLocalJet
open TorusLean.Shared.ThermalCoherentFermionAnchored
open scoped BigOperators ComplexConjugate

abbrev Occupation (Q : ℕ) := Finset (Fin (Q+1))

/-- Explicit occupation adjoint of an arbitrary finite exterior linear map. -/
def occupationAdjoint (Q : ℕ) (L : Module.End ℂ (Space Q)) (x : Space Q) : Space Q :=
  ∑ A : Occupation Q, occupationInner Q (L (occupationBasis Q A)) x • occupationBasis Q A

theorem occupationAdjoint_coordinate (Q : ℕ) (L : Module.End ℂ (Space Q))
    (x : Space Q) (A : Occupation Q) :
    (occupationBasis Q).repr (occupationAdjoint Q L x) A =
      occupationInner Q (L (occupationBasis Q A)) x := by
  classical
  simp [occupationAdjoint,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.single_apply]

theorem occupationAdjoint_adjoint (Q : ℕ) (L : Module.End ℂ (Space Q))
    (x y : Space Q) :
    occupationInner Q (L x) y=occupationInner Q x (occupationAdjoint Q L y) := by
  classical
  calc
    _ = ∑ A : Occupation Q, star ((occupationBasis Q).repr x A)*
        occupationInner Q (L (occupationBasis Q A)) y := by
      conv_lhs => rw [← (occupationBasis Q).sum_repr x]
      simp only [map_sum,map_smul,occupationInner_sum_left,occupationInner_smul_left]
    _ = _ := by
      conv_rhs => unfold occupationInner
      simp_rw [occupationAdjoint_coordinate]

theorem occupationInner_ext_right (Q : ℕ) (x y : Space Q)
    (h : ∀ q, occupationInner Q q x=occupationInner Q q y) : x=y := by
  classical
  apply (occupationBasis Q).repr.injective
  ext A
  have he := h (occupationBasis Q A)
  simpa [occupationInner,Finsupp.single_apply] using he

def sourceRemoval (Q : ℕ) (v x : Space Q) : Space Q :=
  occupationAdjoint Q (LinearMap.mulLeft ℂ v) x

theorem sourceRemoval_coordinate (Q : ℕ) (v x : Space Q) (A : Occupation Q) :
    (occupationBasis Q).repr (sourceRemoval Q v x) A =
      occupationInner Q (v*occupationBasis Q A) x :=
  occupationAdjoint_coordinate Q (LinearMap.mulLeft ℂ v) x A

theorem sourceRemoval_adjoint (Q : ℕ) (v x y : Space Q) :
    occupationInner Q (v*x) y=occupationInner Q x (sourceRemoval Q v y) :=
  occupationAdjoint_adjoint Q (LinearMap.mulLeft ℂ v) x y

/-- Uniqueness lets literal CAR formulae identify the construction. -/
theorem sourceRemoval_eq_of_adjoint (Q : ℕ) (v y z : Space Q)
    (h : ∀ x, occupationInner Q (v*x) y=occupationInner Q x z) :
    sourceRemoval Q v y=z := by
  apply occupationInner_ext_right
  intro x
  rw [← sourceRemoval_adjoint]
  exact h x

theorem sourceRemoval_zero (Q : ℕ) (x : Space Q) : sourceRemoval Q 0 x=0 := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  simp [occupationInner]

theorem sourceRemoval_smul (Q : ℕ) (c : ℂ) (v x : Space Q) :
    sourceRemoval Q (c • v) x=conj c • sourceRemoval Q v x := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  simp only [smul_mul_assoc,occupationInner_smul_left,occupationInner_smul_right,
    ← sourceRemoval_adjoint,Complex.star_def]

theorem sourceRemoval_sub (Q : ℕ) (v w x : Space Q) :
    sourceRemoval Q (v-w) x=sourceRemoval Q v x-sourceRemoval Q w x := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  have hl (a b c : Space Q) : occupationInner Q (a-b) c=
      occupationInner Q a c-occupationInner Q b c := by
    simp [occupationInner,sub_mul,Finset.sum_sub_distrib]
  have hr (a b c : Space Q) : occupationInner Q a (b-c)=
      occupationInner Q a b-occupationInner Q a c := by
    simp [occupationInner,mul_sub,Finset.sum_sub_distrib]
  rw [sub_mul,hl,hr,← sourceRemoval_adjoint,← sourceRemoval_adjoint]

/-- Source coefficients are conjugated by removal, exactly as required by CAR. -/
theorem sourceRemoval_sum_smul {I : Type*} (Q : ℕ) (s : Finset I)
    (c : I → ℂ) (v : I → Space Q) (x : Space Q) :
    sourceRemoval Q (∑ i∈s, c i • v i) x =
      ∑ i∈s, conj (c i) • sourceRemoval Q (v i) x := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
    occupationInner_smul_left,occupationInner_sum_right,occupationInner_smul_right,
    ← sourceRemoval_adjoint,Complex.star_def]

/-- A fixed right-core adjoint, independent of the external source parameter. -/
def rightCoreAdjoint (Q : ℕ) (A : Occupation Q) (x : Space Q) : Space Q :=
  occupationAdjoint Q (LinearMap.mulRight ℂ (occupationBasis Q A)) x

theorem rightCoreAdjoint_adjoint (Q : ℕ) (A : Occupation Q) (v x : Space Q) :
    occupationInner Q (v*occupationBasis Q A) x=
      occupationInner Q v (rightCoreAdjoint Q A x) :=
  occupationAdjoint_adjoint Q (LinearMap.mulRight ℂ (occupationBasis Q A)) v x

theorem sourceRemoval_coordinate_dual (Q : ℕ) (v x : Space Q) (A : Occupation Q) :
    (occupationBasis Q).repr (sourceRemoval Q v x) A =
      conj (occupationInner Q (rightCoreAdjoint Q A x) v) := by
  rw [sourceRemoval_coordinate,rightCoreAdjoint_adjoint]
  exact (TorusLean.Shared.PhysicalFermionNormalSquare.occupationInner_star Q
    (rightCoreAdjoint Q A x) v).symm

/-- Genuine full-Fock removal cross form. Notice that the seed dual for
(w,y) is the conjugated first slot, whereas the dual for (v,x) is second. -/
theorem sourceRemoval_cross_dual_sum (Q : ℕ) (v w x y : Space Q) :
    occupationInner Q (sourceRemoval Q v x) (sourceRemoval Q w y) =
      ∑ A : Occupation Q,
        conj (occupationInner Q (rightCoreAdjoint Q A y) w)*
          occupationInner Q (rightCoreAdjoint Q A x) v := by
  change (∑ A : Occupation Q,
    star ((occupationBasis Q).repr (sourceRemoval Q v x) A)*
      (occupationBasis Q).repr (sourceRemoval Q w y) A) = _
  simp only [sourceRemoval_coordinate_dual,Complex.star_def,Complex.conj_conj,mul_comm]

def formalRemoval (G : Geometry) (theta : Twist) (R : ℂ)
    (v : FormalExterior) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  sourceRemoval (physicalQ G theta) (rawJetExteriorMap G theta R v) x

theorem formalRemoval_zero (G : Geometry) (theta : Twist) (R : ℂ)
    (x : Space (physicalQ G theta)) : formalRemoval G theta R 0 x=0 := by
  simp only [formalRemoval,map_zero,sourceRemoval_zero]

theorem formalRemoval_smul (G : Geometry) (theta : Twist) (R c : ℂ)
    (v : FormalExterior) (x : Space (physicalQ G theta)) :
    formalRemoval G theta R (c • v) x=conj c • formalRemoval G theta R v x := by
  simp only [formalRemoval,map_smul,sourceRemoval_smul]

theorem formalRemoval_sub (G : Geometry) (theta : Twist) (R : ℂ)
    (v w : FormalExterior) (x : Space (physicalQ G theta)) :
    formalRemoval G theta R (v-w) x=
      formalRemoval G theta R v x-formalRemoval G theta R w x := by
  simp only [formalRemoval,map_sub,sourceRemoval_sub]

theorem formalRemoval_sum_smul {I : Type*} (G : Geometry) (theta : Twist)
    (R : ℂ) (s : Finset I) (c : I → ℂ) (v : I → FormalExterior)
    (x : Space (physicalQ G theta)) :
    formalRemoval G theta R (∑ i∈s, c i • v i) x=
      ∑ i∈s, conj (c i) • formalRemoval G theta R (v i) x := by
  simp only [formalRemoval,map_sum,map_smul,sourceRemoval_sum_smul]

theorem formalRemoval_adjoint (G : Geometry) (theta : Twist) (R : ℂ)
    (v : FormalExterior) (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) (rawJetExteriorMap G theta R v*x) y=
      occupationInner (physicalQ G theta) x (formalRemoval G theta R v y) :=
  sourceRemoval_adjoint _ _ _ _

theorem formalRemoval_three (G : Geometry) (theta : Twist) (R : ℂ)
    (p j : ℕ) (x : Space (physicalQ G theta)) :
    formalRemoval G theta R (formalThreeSeed p j) x=
      localJetAnnihilate G theta j R (pairDescendant G theta p R x) := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  exact formalThreeSeed_image_mul_adjoint G theta R p j y x

theorem formalRemoval_coupled (G : Geometry) (theta : Twist) (R : ℂ)
    (D : ℕ) (r : OddMode D) (x : Space (physicalQ G theta)) :
    formalRemoval G theta R (formalCoupledColumn D r) x=
      coupledFourAmplitude G theta D r R x := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  exact physicalCoupledColumn_mul_adjoint G theta D r R y x

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
