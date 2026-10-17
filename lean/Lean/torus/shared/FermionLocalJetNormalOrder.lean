import torus.shared.FermionLocalJetMetricIntegral

/-! Exact normal ordering of the literal seven-row physical comparison square.
The same decoded alpha, lambda, true B_p, and unorthogonalized raw jets enter
both sides. The sole CAR contraction produces the actual Gram matrix, whose
identity part and metric remainder are then separated algebraically. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open scoped BigOperators ComplexConjugate

private theorem occ_add_left (Q : ℕ) (x y z : Space Q) :
    occupationInner Q (x+y) z = occupationInner Q x z + occupationInner Q y z := by
  simp [occupationInner,add_mul,Finset.sum_add_distrib]
private theorem occ_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y + occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]
private theorem occ_sub_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y-z) = occupationInner Q x y - occupationInner Q x z := by
  simp [occupationInner,mul_sub,Finset.sum_sub_distrib]

/-- The original row F_r, before collecting entries by the auxiliary index. -/
def certificateRowApply (G : Geometry) (theta : Twist) (r : CertificateRow)
    (R : ℂ) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  (certificateLambda r : ℂ) • pairDescendant G theta (certificateRowData r).1 R x +
    ∑ a : CertificateEntry r, (certificateAlpha r a : ℂ) •
      physicalCreate G theta (rawPlaneJet G theta (certificateJetIndex r a) R)
        (certificateAmplitude G theta r a R x)

theorem certificateRowApply_grouped (G : Geometry) (theta : Twist) (r : CertificateRow)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    certificateRowApply G theta r R x =
      (certificateLambda r : ℂ) • pairDescendant G theta (certificateRowData r).1 R x +
        ∑ i : Fin 9, physicalCreate G theta (rawPlaneJet G theta i R)
          (certificateRowOutput G theta r R x i) := by
  classical
  unfold certificateRowApply
  congr 1
  symm
  calc
    _ = ∑ i : Fin 9, ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry r => certificateEntryJet r a=i),
      (certificateAlpha r a : ℂ) • physicalCreate G theta
        (rawPlaneJet G theta (certificateJetIndex r a) R) (certificateAmplitude G theta r a R x) := by
      simp only [certificateRowOutput,map_sum,map_smul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      have he := (Finset.mem_filter.mp ha).2
      have hv : certificateJetIndex r a = i.val := congrArg Fin.val he
      rw [hv]
    _ = _ := certificate_group_sum r _

theorem localJetCreate_adjoint_right (G : Geometry) (theta : Twist) (i : ℕ) (R : ℂ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x (physicalCreate G theta (rawPlaneJet G theta i R) y) =
      occupationInner (physicalQ G theta) (localJetAnnihilate G theta i R x) y :=
  rawCreate_adjoint_right _ _ _ _

/-- The actual single CAR contraction, with its four-body minus sign. -/
theorem localJetCreate_cross_normal_order (G : Geometry) (theta : Twist) (i k : ℕ) (R : ℂ)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta)
      (physicalCreate G theta (rawPlaneJet G theta i R) x)
      (physicalCreate G theta (rawPlaneJet G theta k R) y) =
      inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) *
        occupationInner (physicalQ G theta) x y -
      occupationInner (physicalQ G theta) (localJetAnnihilate G theta k R x)
        (localJetAnnihilate G theta i R y) := by
  rw [physicalCreate_adjoint]
  have hc := LinearMap.congr_fun (localJet_CAR G theta i k R) y
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply] at hc
  change occupationInner (physicalQ G theta) x
    (localJetAnnihilate G theta i R (physicalCreate G theta (rawPlaneJet G theta k R) y)) = _
  rw [hc,occ_sub_right,occupationInner_smul_right,localJetCreate_adjoint_right]

def certificateCrossAt (G : Geometry) (theta : Twist) (r : CertificateRow)
    (R : ℂ) (x : Space (physicalQ G theta)) : ℂ :=
  (certificateLambda r : ℂ) * ∑ i : Fin 9,
    (occupationInner (physicalQ G theta)
      (localJetAnnihilate G theta i R (pairDescendant G theta (certificateRowData r).1 R x))
      (certificateRowOutput G theta r R x i) +
    occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
      (localJetAnnihilate G theta i R (pairDescendant G theta (certificateRowData r).1 R x)))

def certificateNormalThreeAt (G : Geometry) (theta : Twist) (r : CertificateRow)
    (R : ℂ) (x : Space (physicalQ G theta)) : ℂ :=
  certificateCrossAt G theta r R x + ∑ i : Fin 9, ∑ k : Fin 9,
    inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) *
      occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
        (certificateRowOutput G theta r R x k)

def certificateNormalFourAt (G : Geometry) (theta : Twist) (r : CertificateRow)
    (R : ℂ) (x : Space (physicalQ G theta)) : ℂ :=
  -(∑ i : Fin 9, ∑ k : Fin 9, occupationInner (physicalQ G theta)
    (localJetAnnihilate G theta k R (certificateRowOutput G theta r R x i))
    (localJetAnnihilate G theta i R (certificateRowOutput G theta r R x k)))

/-- Paper normal2/normal3/normal4, on every original Fock state and all seven rows. -/
theorem certificateRow_normal_order (G : Geometry) (theta : Twist) (r : CertificateRow)
    (R : ℂ) (x : Space (physicalQ G theta)) :
    (occupationNormSq (physicalQ G theta) (certificateRowApply G theta r R x) : ℂ) =
      ((certificateLambda r)^2 * occupationNormSq (physicalQ G theta)
        (pairDescendant G theta (certificateRowData r).1 R x) : ℝ) +
      certificateNormalThreeAt G theta r R x + certificateNormalFourAt G theta r R x := by
  have hgram : (∑ k : Fin 9, ∑ i : Fin 9,
      inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) *
        occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
          (certificateRowOutput G theta r R x k)) =
      ∑ i : Fin 9, ∑ k : Fin 9,
        inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) *
          occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
            (certificateRowOutput G theta r R x k) := Finset.sum_comm
  have hfour : (∑ k : Fin 9, ∑ i : Fin 9,
      occupationInner (physicalQ G theta)
        (physicalAnnihilate G theta (rawPlaneJet G theta k R) (certificateRowOutput G theta r R x i))
        (physicalAnnihilate G theta (rawPlaneJet G theta i R) (certificateRowOutput G theta r R x k))) =
      ∑ i : Fin 9, ∑ k : Fin 9,
        occupationInner (physicalQ G theta)
          (physicalAnnihilate G theta (rawPlaneJet G theta k R) (certificateRowOutput G theta r R x i))
          (physicalAnnihilate G theta (rawPlaneJet G theta i R) (certificateRowOutput G theta r R x k)) :=
    Finset.sum_comm
  rw [← occupationInner_self,certificateRowApply_grouped]
  simp only [occ_add_left,occ_add_right,occupationInner_smul_left,occupationInner_smul_right,
    Complex.star_def,Complex.conj_ofReal,occupationInner_sum_left,occupationInner_sum_right]
  simp_rw [localJetCreate_cross_normal_order]
  simp_rw [physicalCreate_adjoint,localJetCreate_adjoint_right]
  simp only [Finset.sum_sub_distrib,occupationInner_self,certificateNormalThreeAt,
    certificateNormalFourAt,certificateCrossAt,Finset.sum_add_distrib,← Finset.mul_sum,localJetAnnihilate]
  push_cast
  rw [hgram,hfour]
  ring

def certificateNormalThreeZeroAt (G : Geometry) (theta : Twist) (R : ℂ)
    (x : Space (physicalQ G theta)) : ℝ :=
  ∑ r : CertificateRow, ((certificateCrossAt G theta r R x).re +
    ∑ i : Fin 9, occupationNormSq (physicalQ G theta) (certificateRowOutput G theta r R x i))

/-- The metric term proved above is exactly the actual Gram-minus-delta part. -/
theorem certificate_normal_three_metric_split (G : Geometry) (theta : Twist) (R : ℂ)
    (x : Space (physicalQ G theta)) :
    (∑ r : CertificateRow, (certificateNormalThreeAt G theta r R x).re) =
      certificateNormalThreeZeroAt G theta R x + certificateMetricAt G theta R x := by
  classical
  unfold certificateNormalThreeZeroAt certificateMetricAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have he : (∑ i : Fin 9, ∑ k : Fin 9,
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) - if i=k then 1 else 0) *
        occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
          (certificateRowOutput G theta r R x k)) =
      (∑ i : Fin 9, ∑ k : Fin 9, inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) *
        occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
          (certificateRowOutput G theta r R x k)) -
      ∑ i : Fin 9, (occupationNormSq (physicalQ G theta) (certificateRowOutput G theta r R x i) : ℂ) := by
    simp [sub_mul,Finset.sum_sub_distrib,occupationInner_self]
  rw [he]
  simp only [certificateNormalThreeAt,Complex.add_re,Complex.sub_re,Complex.re_sum,Complex.ofReal_re]
  ring

theorem certificate_positive_square (G : Geometry) (theta : Twist) (R : ℂ)
    (x : Space (physicalQ G theta)) :
    0 ≤ ∑ r : CertificateRow, occupationNormSq (physicalQ G theta) (certificateRowApply G theta r R x) :=
  Finset.sum_nonneg fun r hr => occupationNormSq_nonneg _ _

#print axioms certificateRowApply_grouped
#print axioms localJetCreate_adjoint_right
#print axioms localJetCreate_cross_normal_order
#print axioms certificateRow_normal_order
#print axioms certificate_normal_three_metric_split
#print axioms certificate_positive_square
end TorusLean.Shared.FermionLocalJet
