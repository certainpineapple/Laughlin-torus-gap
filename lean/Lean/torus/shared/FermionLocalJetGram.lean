import torus.shared.PlaneJetFiniteGram
import torus.shared.RelativeJetFrameAsymptotic

/-! The manuscript e_J is the supremum of the operator norm of the actual
raw-jet Gram matrix minus identity, on the genuine Euclidean coefficient space.
It is not an entrywise norm and is not the unrelated three-body coefficient e_z.
All physical jets and the original geometry and twist are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open TorusLean.Geometry TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetFiniteGram TorusLean.Fermion.LatticePacking
open Filter Topology
open scoped BigOperators ComplexConjugate

abbrev JetCoefficients (J : ℕ) := EuclideanSpace ℂ (Fin (J+1))

/-- The literal physical raw-jet Gram matrix acts in the Euclidean norm. -/
def localGramLinear (G : Geometry) (theta : Twist) (J : ℕ) (R : ℂ) :
    JetCoefficients J →ₗ[ℂ] JetCoefficients J where
  toFun x := WithLp.toLp 2 (fun i => ∑ j : Fin (J+1),
    inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) * x j)
  map_add' x y := by
    ext i
    change (∑ j : Fin (J+1), _ * (x j+y j)) = (∑ j, _ * x j)+(∑ j, _ * y j)
    simp only [mul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    change (∑ j : Fin (J+1), _ * (c*x j)) = c*(∑ j, _ * x j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def localGramOperator (G : Geometry) (theta : Twist) (J : ℕ) (R : ℂ) :
    JetCoefficients J →L[ℂ] JetCoefficients J :=
  (localGramLinear G theta J R).toContinuousLinearMap

theorem localGramOperator_apply (G : Geometry) (theta : Twist) (J : ℕ) (R : ℂ)
    (x : JetCoefficients J) (i : Fin (J+1)) :
    localGramOperator G theta J R x i = ∑ j : Fin (J+1),
      inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) * x j := rfl

def localGramErrorOperator (G : Geometry) (theta : Twist) (J : ℕ) (R : ℂ) :
    JetCoefficients J →L[ℂ] JetCoefficients J :=
  localGramOperator G theta J R - ContinuousLinearMap.id ℂ (JetCoefficients J)

theorem localGramErrorOperator_apply (G : Geometry) (theta : Twist) (J : ℕ) (R : ℂ)
    (x : JetCoefficients J) (i : Fin (J+1)) :
    localGramErrorOperator G theta J R x i = ∑ j : Fin (J+1),
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * x j := by
  classical
  change (∑ j : Fin (J+1), _ * x j)-x i = _
  simp [sub_mul,Finset.sum_sub_distrib]

/-- Shape-, twist- and center-independent budget from actual mixed raw jets. -/
def localJetBudget (J : ℕ) (L : ℝ) : ℝ :=
  PlaneJetFiniteGram.finiteGramError J L * (J+1 : ℕ)

theorem localJetBudget_nonneg (J : ℕ) (L : ℝ) : 0 ≤ localJetBudget J L :=
  mul_nonneg (PlaneJetFiniteGram.finiteGramError_nonneg J L) (Nat.cast_nonneg _)

theorem localGramErrorOperator_norm_le (G : Geometry) (theta : Twist) (J : ℕ)
    (R : ℂ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖localGramErrorOperator G theta J R‖ ≤ localJetBudget J L := by
  classical
  simpa only [localJetBudget,Fintype.card_fin] using
    RelativeJetFrameAsymptotic.operator_matrix_opNorm_le
      (localGramErrorOperator G theta J R)
      (fun i j : Fin (J+1) =>
        (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
          if i = j then 1 else 0) • ContinuousLinearMap.id ℂ ℂ)
      (PlaneJetFiniteGram.finiteGramError J L)
      (PlaneJetFiniteGram.finiteGramError_nonneg J L)
      (fun i j => by
        simpa only [norm_smul,ContinuousLinearMap.norm_id,mul_one] using
          finite_gram_entry_error G theta J R L hL1 hL i j)
      (fun x i => by simpa only [ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul] using
          localGramErrorOperator_apply G theta J R x i)

/-- The paper's genuine uniform local-jet error e_J. -/
def localJetError (G : Geometry) (theta : Twist) (J : ℕ) : ℝ :=
  sSup (Set.range (fun R : ℂ => ‖localGramErrorOperator G theta J R‖))

theorem localGramErrorValues_bddAbove (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) :
    BddAbove (Set.range (fun R : ℂ => ‖localGramErrorOperator G theta J R‖)) := by
  refine ⟨localJetBudget J 1,?_⟩
  rintro v ⟨R,rfl⟩
  exact localGramErrorOperator_norm_le G theta J R 1 le_rfl hG

theorem localGramErrorOperator_norm_le_error (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) (R : ℂ) :
    ‖localGramErrorOperator G theta J R‖ ≤ localJetError G theta J :=
  le_csSup (localGramErrorValues_bddAbove G theta J hG) ⟨R,rfl⟩

theorem localJetError_nonneg (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) : 0 ≤ localJetError G theta J :=
  (norm_nonneg _).trans (localGramErrorOperator_norm_le_error G theta J hG 0)

theorem localJetError_le_budget (G : Geometry) (theta : Twist) (J : ℕ)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    localJetError G theta J ≤ localJetBudget J L := by
  apply csSup_le (Set.range_nonempty _)
  rintro v ⟨R,rfl⟩
  exact localGramErrorOperator_norm_le G theta J R L hL1 hL

/-- Scalar quadratic form of the exact matrix, bounded by its actual e_J. -/
theorem localJetError_scalar_form (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) (R : ℂ) (c : Fin (J+1) → ℂ) :
    ‖∑ i : Fin (J+1), ∑ j : Fin (J+1), conj (c i) *
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * c j‖ ≤
      localJetError G theta J * ∑ i, ‖c i‖^2 := by
  let x : JetCoefficients J := WithLp.toLp 2 c
  let E := localGramErrorOperator G theta J R
  have he : (∑ i : Fin (J+1), ∑ j : Fin (J+1), conj (c i) *
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta j R) -
        if i = j then 1 else 0) * c j) = inner ℂ x (E x) := by
    rw [PiLp.inner_apply]
    simp only [E,localGramErrorOperator_apply,RCLike.inner_apply',Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    change conj (c i) * _ * c j = conj (c i) * (_ * c j)
    ring
  rw [he]
  calc
    _ ≤ ‖x‖ * ‖E x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (localJetError G theta J * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((E.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (localGramErrorOperator_norm_le_error G theta J hG R)
          (norm_nonneg _))) (norm_nonneg _)
    _ = localJetError G theta J * ‖x‖^2 := by ring
    _ = _ := by rw [PiLp.norm_sq_eq_of_L2]

/-- The actual finite synthesis has the whole Gram budget, including cross terms. -/
theorem localJetSynthesis_norm_error (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) (R : ℂ) (c : Fin (J+1) → ℂ) :
    |‖jetSynthesis G theta J R c‖^2 - ∑ j, ‖c j‖^2| ≤
      localJetError G theta J * ∑ j, ‖c j‖^2 := by
  have h := localJetError_scalar_form G theta J hG R c
  rw [← jetSynthesis_inner_error] at h
  have hn : ‖jetSynthesis G theta J R c‖^2 =
      (inner ℂ (jetSynthesis G theta J R c) (jetSynthesis G theta J R c)).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  have hr := (Complex.abs_re_le_norm
    (inner ℂ (jetSynthesis G theta J R c) (jetSynthesis G theta J R c) -
      ((∑ j, ‖c j‖^2 : ℝ) : ℂ))).trans h
  simpa only [Complex.sub_re,Complex.ofReal_re,← hn] using hr

theorem localJetSynthesis_norm_le (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) (R : ℂ) (c : Fin (J+1) → ℂ) :
    ‖jetSynthesis G theta J R c‖^2 ≤
      (1+localJetError G theta J) * ∑ j, ‖c j‖^2 := by
  have h := (abs_le.mp (localJetSynthesis_norm_error G theta J hG R c)).2
  nlinarith

theorem rawPlaneJet_norm_sq_le_localJetError (G : Geometry) (theta : Twist) (J : ℕ)
    (hG : 1 ≤ systole G) (R : ℂ) (j : ℕ) (hj : j ≤ J) :
    ‖rawPlaneJet G theta j R‖^2 ≤ 1+localJetError G theta J := by
  classical
  let i : Fin (J+1) := ⟨j,Nat.lt_succ_of_le hj⟩
  have h := localJetSynthesis_norm_le G theta J hG R (fun k => if k=i then 1 else 0)
  have hc : (∑ k : Fin (J+1), ‖(if k=i then (1 : ℂ) else 0)‖^2) = 1 := by
    calc
      _ = ∑ k : Fin (J+1), if k=i then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ = 1 := by simp
  rw [hc,mul_one] at h
  simpa [jetSynthesis,i] using h

#print axioms localGramOperator_apply
#print axioms localGramErrorOperator_apply
#print axioms localJetBudget_nonneg
#print axioms localGramErrorOperator_norm_le
#print axioms localGramErrorValues_bddAbove
#print axioms localGramErrorOperator_norm_le_error
#print axioms localJetError_nonneg
#print axioms localJetError_le_budget
#print axioms localJetError_scalar_form
#print axioms localJetSynthesis_norm_error
#print axioms localJetSynthesis_norm_le
#print axioms rawPlaneJet_norm_sq_le_localJetError
end TorusLean.Shared.FermionLocalJet
