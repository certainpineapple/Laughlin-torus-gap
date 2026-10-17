import torus.shared.PhysicalFermionNormalSquare

/-! Actual two-cell integrals behind the normal square. All integration is in
the original μ₂, and all functions are proved integrable rather than relying
on the totalized value of an undefined Bochner integral. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionNormalSquare
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open scoped BigOperators ComplexConjugate

lemma rawPairCreate_expansion (Q : ℕ) (a b : Orbital Q) :
    rawPairCreate Q a b =
      ∑ p : PairIndex Q, (a p.1 * b p.2) • modePairCreate Q p := by
  classical
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.ι ℂ a * (ExteriorAlgebra.ι ℂ b * x) = _
  rw [vectorCreate_sum]
  simp only [create, LinearMap.coe_mk, AddHom.coe_mk]
  rw [vectorCreate_sum]
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, Fintype.sum_prod_type,
    modePairCreate, rawPairCreate, Module.End.mul_apply, rawCreate,
    LinearMap.coe_mk, AddHom.coe_mk, create]

lemma pairCreateAt_expansion (G : Geometry) (theta : Twist) (R : ℂ) :
    pairCreateAt G theta R = ∑ p, star (jetPairCoefficient G theta p R) •
      modePairCreate (physicalQ G theta) p := by
  rw [pairCreateAt, rawPairCreate_expansion]
  simp only [jetPairCoefficient, star_mul, star_star, mul_comm]

/-- A complex matrix-entry functional; no norm on the algebraic exterior
carrier is silently substituted for the physical occupation norm. -/
def operatorForm (Q : ℕ) (x y : Space Q) : Module.End ℂ (Space Q) →ₗ[ℂ] ℂ where
  toFun T := occupationInner Q x (T y)
  map_add' T U := by simp [occupationInner, mul_add, Finset.sum_add_distrib]
  map_smul' c T := by
    simp only [LinearMap.smul_apply, occupationInner_smul_right, smul_eq_mul, RingHom.id_apply]

def coefficientKernel (G : Geometry) (theta : Twist)
    (p q : PairIndex (physicalQ G theta)) (R : ℂ) : ℂ :=
  star (jetPairCoefficient G theta p R) * jetPairCoefficient G theta q R

lemma coefficientKernel_continuous (G : Geometry) (theta : Twist)
    (p q : PairIndex (physicalQ G theta)) : Continuous (coefficientKernel G theta p q) :=
  (jetPairCoefficient_continuous G theta p).star.mul (jetPairCoefficient_continuous G theta q)

lemma coefficientKernel_integrable (G : Geometry) (theta : Twist)
    (p q : PairIndex (physicalQ G theta)) :
    Integrable (coefficientKernel G theta p q) (cellMeasure G 2) :=
  contactMatrix_integrable G theta p q

def twoCenterExpansion (G : Geometry) (theta : Twist)
    (T : PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) →
      PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) → ℂ)
    (R S : ℂ) : ℂ :=
  ∑ p, ∑ q, ∑ r, ∑ s,
    (coefficientKernel G theta p q R * coefficientKernel G theta r s S) * T p q r s

lemma twoCenterExpansion_integrable (G : Geometry) (theta : Twist)
    (T : PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) →
      PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) → ℂ) :
    Integrable (fun z : ℂ × ℂ => twoCenterExpansion G theta T z.1 z.2)
      ((cellMeasure G 2).prod (cellMeasure G 2)) := by
  unfold twoCenterExpansion
  exact integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_prod
        (coefficientKernel_integrable G theta r s)).mul_const _))))

lemma twoCenterExpansion_slice_integrable (G : Geometry) (theta : Twist)
    (T : PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) →
      PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) → ℂ) (R : ℂ) :
    Integrable (twoCenterExpansion G theta T R) (cellMeasure G 2) := by
  apply continuous_integrable_cellMeasure G 2
  unfold twoCenterExpansion
  exact continuous_finsetSum _ (fun p _ => continuous_finsetSum _ (fun q _ =>
    continuous_finsetSum _ (fun r _ => continuous_finsetSum _ (fun s _ =>
      ((coefficientKernel_continuous G theta r s).const_mul _).mul_const _))))

lemma twoCenterExpansion_inner_integral (G : Geometry) (theta : Twist)
    (T : PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) →
      PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) → ℂ) (R : ℂ) :
    (∫ S, twoCenterExpansion G theta T R S ∂cellMeasure G 2) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (coefficientKernel G theta p q R * contactMatrix G theta r s) * T p q r s := by
  unfold twoCenterExpansion
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta r s).const_mul _).mul_const _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- Fubini-compatible genuine double-cell coefficient calculation. -/
theorem twoCenterExpansion_integral (G : Geometry) (theta : Twist)
    (T : PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) →
      PairIndex (physicalQ G theta) → PairIndex (physicalQ G theta) → ℂ) :
    (∫ R, ∫ S, twoCenterExpansion G theta T R S ∂cellMeasure G 2 ∂cellMeasure G 2) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (contactMatrix G theta p q * contactMatrix G theta r s) * T p q r s := by
  simp_rw [twoCenterExpansion_inner_integral]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun s _ =>
      ((coefficientKernel_integrable G theta p q).mul_const _).mul_const _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const, integral_mul_const]
  rfl

lemma densityAt_expansion (G : Geometry) (theta : Twist) (R : ℂ) :
    pairCreateAt G theta R * pairAt G theta R =
      ∑ p, ∑ q, coefficientKernel G theta p q R •
        (modePairCreate (physicalQ G theta) p * modePairAnnihilate (physicalQ G theta) q) := by
  classical
  rw [pairCreateAt_expansion]
  simp only [Finset.sum_mul]
  simp only [pairAt_expansion, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [coefficientKernel, mul_comm]

lemma density_product_expansion (G : Geometry) (theta : Twist) (R S : ℂ)
    (x y : Space (physicalQ G theta)) :
    operatorForm (physicalQ G theta) x y
      ((pairCreateAt G theta R * pairAt G theta R) *
        (pairCreateAt G theta S * pairAt G theta S)) =
      twoCenterExpansion G theta (fun p q r s => operatorForm (physicalQ G theta) x y
        ((modePairCreate (physicalQ G theta) p * modePairAnnihilate (physicalQ G theta) q) *
          (modePairCreate (physicalQ G theta) r * modePairAnnihilate (physicalQ G theta) s))) R S := by
  classical
  rw [densityAt_expansion G theta R]
  simp only [Finset.sum_mul]
  rw [densityAt_expansion G theta S]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_sum, map_smul, smul_eq_mul, twoCenterExpansion]
  simp only [mul_comm]

lemma fourBody_density_expansion (G : Geometry) (theta : Twist) (R S : ℂ)
    (x y : Space (physicalQ G theta)) :
    operatorForm (physicalQ G theta) x y
      (pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) =
      twoCenterExpansion G theta (fun p q r s => operatorForm (physicalQ G theta) x y
        (modePairCreate (physicalQ G theta) p * modePairCreate (physicalQ G theta) r *
          modePairAnnihilate (physicalQ G theta) q * modePairAnnihilate (physicalQ G theta) s)) R S := by
  classical
  rw [pairCreateAt_expansion G theta R]
  simp only [Finset.sum_mul]
  rw [pairCreateAt_expansion G theta S]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [pairAt_expansion G theta R]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [pairAt_expansion G theta S]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_sum, map_smul, smul_eq_mul, twoCenterExpansion, coefficientKernel]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The full Hamiltonian square is a genuine integrable two-cell density
product, with both center measures exactly μ₂. -/
theorem physicalHamiltonian_square_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (physicalHamiltonian G theta (physicalHamiltonian G theta y)) =
      ∫ R, ∫ S, occupationInner (physicalQ G theta) x
        ((pairCreateAt G theta R * pairAt G theta R *
          (pairCreateAt G theta S * pairAt G theta S)) y)
        ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  change operatorForm (physicalQ G theta) x y
    (physicalHamiltonian G theta * physicalHamiltonian G theta) =
      ∫ R, ∫ S, operatorForm (physicalQ G theta) x y
        ((pairCreateAt G theta R * pairAt G theta R) *
          (pairCreateAt G theta S * pairAt G theta S)) ∂cellMeasure G 2 ∂cellMeasure G 2
  simp_rw [density_product_expansion]
  rw [twoCenterExpansion_integral]
  change operatorForm (physicalQ G theta) x y
    ((∑ p, ∑ q, contactMatrix G theta p q •
      (modePairCreate (physicalQ G theta) p * modePairAnnihilate (physicalQ G theta) q)) *
        physicalHamiltonian G theta) = _
  simp only [Finset.sum_mul]
  simp only [physicalHamiltonian, matrixHamiltonian, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul, map_sum, map_smul, smul_eq_mul]
  simp only [mul_comm]

theorem matrixFourBody_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixFourBody (physicalQ G theta) (contactMatrix G theta) y) =
      ∫ R, ∫ S, occupationInner (physicalQ G theta) x
        ((pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) y)
        ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  change operatorForm (physicalQ G theta) x y
    (matrixFourBody (physicalQ G theta) (contactMatrix G theta)) =
      ∫ R, ∫ S, operatorForm (physicalQ G theta) x y
        (pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S)
        ∂cellMeasure G 2 ∂cellMeasure G 2
  simp_rw [fourBody_density_expansion]
  rw [twoCenterExpansion_integral]
  simp only [matrixFourBody, map_sum, map_smul, smul_eq_mul]

def pairGramAt (G : Geometry) (theta : Twist) (R S : ℂ) : ℂ :=
  rawPairGram (physicalQ G theta)
    (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R)
    (-physicalJetCoordinates G theta 0 S) (physicalJetCoordinates G theta 1 S)

lemma modePairCreate_vacuum_inner (Q : ℕ) (q r : PairIndex Q) :
    occupationInner Q (modePairCreate Q q 1) (modePairCreate Q r 1) =
      rawPairGram Q (mode q.1) (mode q.2) (mode r.1) (mode r.2) :=
  (rawPairGram_eq_inner _ _ _ _ _).symm

lemma pairGramAt_expansion (G : Geometry) (theta : Twist) (R S : ℂ) :
    pairGramAt G theta R S = ∑ q, ∑ r,
      (jetPairCoefficient G theta q R * star (jetPairCoefficient G theta r S)) *
        rawPairGram (physicalQ G theta) (mode q.1) (mode q.2) (mode r.1) (mode r.2) := by
  unfold pairGramAt
  rw [rawPairGram_eq_inner]
  change occupationInner (physicalQ G theta) (pairCreateAt G theta R 1) (pairCreateAt G theta S 1) = _
  rw [pairCreateAt_expansion, pairCreateAt_expansion]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, occupationInner_sum_left,
    occupationInner_sum_right, occupationInner_smul_left, occupationInner_smul_right,
    Finset.mul_sum, star_star, modePairCreate_vacuum_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma double_density_expansion (G : Geometry) (theta : Twist) (R S : ℂ)
    (x y : Space (physicalQ G theta)) :
    operatorForm (physicalQ G theta) x y
      (pairGramAt G theta R S • (pairCreateAt G theta R * pairAt G theta S)) =
      twoCenterExpansion G theta (fun p q r s =>
        rawPairGram (physicalQ G theta) (mode q.1) (mode q.2) (mode r.1) (mode r.2) *
          operatorForm (physicalQ G theta) x y
            (modePairCreate (physicalQ G theta) p * modePairAnnihilate (physicalQ G theta) s)) R S := by
  classical
  rw [map_smul, pairGramAt_expansion]
  simp only [smul_eq_mul, Finset.sum_mul]
  rw [pairCreateAt_expansion]
  simp only [Finset.sum_mul]
  rw [pairAt_expansion]
  simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    map_sum, map_smul, smul_eq_mul, Finset.mul_sum, twoCenterExpansion, coefficientKernel]
  simp_rw [show ∀ q r,
    (∑ p, ∑ s,
      (jetPairCoefficient G theta q R * star (jetPairCoefficient G theta r S) *
        rawPairGram (physicalQ G theta) (mode q.1) (mode q.2) (mode r.1) (mode r.2)) *
      ((jetPairCoefficient G theta s S * star (jetPairCoefficient G theta p R)) *
        operatorForm (physicalQ G theta) x y
          (modePairCreate (physicalQ G theta) p * modePairAnnihilate (physicalQ G theta) s))) =
    (∑ p, ∑ s,
      (star (jetPairCoefficient G theta p R) * jetPairCoefficient G theta q R *
        (star (jetPairCoefficient G theta r S) * jetPairCoefficient G theta s S)) *
      (rawPairGram (physicalQ G theta) (mode q.1) (mode q.2) (mode r.1) (mode r.2) *
        operatorForm (physicalQ G theta) x y
          (modePairCreate (physicalQ G theta) p * modePairAnnihilate (physicalQ G theta) s))) by
    intro q r
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro s _
    ring]
  conv_lhs =>
    arg 2
    ext q
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem matrixDoubleContraction_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta) y) =
      ∫ R, ∫ S, pairGramAt G theta R S * occupationInner (physicalQ G theta) x
        ((pairCreateAt G theta R * pairAt G theta S) y)
        ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  change operatorForm (physicalQ G theta) x y
    (matrixDoubleContraction (physicalQ G theta) (contactMatrix G theta)) = _
  have heq (R S : ℂ) : pairGramAt G theta R S * occupationInner (physicalQ G theta) x
      ((pairCreateAt G theta R * pairAt G theta S) y) =
      operatorForm (physicalQ G theta) x y
        (pairGramAt G theta R S • (pairCreateAt G theta R * pairAt G theta S)) := by
    rw [map_smul]
    rfl
  simp_rw [heq, double_density_expansion]
  rw [twoCenterExpansion_integral]
  simp only [matrixDoubleContraction, map_sum, map_smul, smul_eq_mul, mul_assoc]

def singleContractionAt (G : Geometry) (theta : Twist) (R S : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  pairCreateAt G theta R *
    rawSingleContraction (physicalQ G theta)
      (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R)
      (-physicalJetCoordinates G theta 0 S) (physicalJetCoordinates G theta 1 S) *
    pairAt G theta S

lemma single_density_expansion (G : Geometry) (theta : Twist) (R S : ℂ)
    (x y : Space (physicalQ G theta)) :
    operatorForm (physicalQ G theta) x y (singleContractionAt G theta R S) =
      twoCenterExpansion G theta (fun p q r s => operatorForm (physicalQ G theta) x y
        (modePairCreate (physicalQ G theta) p *
          rawSingleContraction (physicalQ G theta) (mode q.1) (mode q.2) (mode r.1) (mode r.2) *
          modePairAnnihilate (physicalQ G theta) s)) R S := by
  have h := congrArg (operatorForm (physicalQ G theta) x y)
    (physical_density_normal_order G theta R S)
  change operatorForm (physicalQ G theta) x y
    ((pairCreateAt G theta R * pairAt G theta R) * (pairCreateAt G theta S * pairAt G theta S)) =
      operatorForm (physicalQ G theta) x y
        ((pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) +
          singleContractionAt G theta R S +
            pairGramAt G theta R S • (pairCreateAt G theta R * pairAt G theta S)) at h
  simp only [map_add] at h
  rw [density_product_expansion, fourBody_density_expansion, double_density_expansion] at h
  simp only [twoCenterExpansion, mode_pair_sandwich, map_add, map_smul, smul_eq_mul,
    mul_add, Finset.sum_add_distrib] at h ⊢
  exact (add_left_cancel (add_right_cancel h)).symm

theorem physical_square_density_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    Integrable (fun z : ℂ × ℂ => occupationInner (physicalQ G theta) x
      (((pairCreateAt G theta z.1 * pairAt G theta z.1) *
        (pairCreateAt G theta z.2 * pairAt G theta z.2)) y))
      ((cellMeasure G 2).prod (cellMeasure G 2)) := by
  change Integrable (fun z : ℂ × ℂ => operatorForm (physicalQ G theta) x y
      ((pairCreateAt G theta z.1 * pairAt G theta z.1) *
        (pairCreateAt G theta z.2 * pairAt G theta z.2))) _
  simp_rw [density_product_expansion]
  exact twoCenterExpansion_integrable G theta _

theorem physical_fourBody_density_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    Integrable (fun z : ℂ × ℂ => occupationInner (physicalQ G theta) x
      ((pairCreateAt G theta z.1 * pairCreateAt G theta z.2 *
        pairAt G theta z.1 * pairAt G theta z.2) y))
      ((cellMeasure G 2).prod (cellMeasure G 2)) := by
  change Integrable (fun z : ℂ × ℂ => operatorForm (physicalQ G theta) x y
      (pairCreateAt G theta z.1 * pairCreateAt G theta z.2 *
        pairAt G theta z.1 * pairAt G theta z.2)) _
  simp_rw [fourBody_density_expansion]
  exact twoCenterExpansion_integrable G theta _

theorem physical_double_density_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    Integrable (fun z : ℂ × ℂ => pairGramAt G theta z.1 z.2 *
      occupationInner (physicalQ G theta) x ((pairCreateAt G theta z.1 * pairAt G theta z.2) y))
      ((cellMeasure G 2).prod (cellMeasure G 2)) := by
  have heq (R S : ℂ) : pairGramAt G theta R S * occupationInner (physicalQ G theta) x
      ((pairCreateAt G theta R * pairAt G theta S) y) =
      operatorForm (physicalQ G theta) x y
        (pairGramAt G theta R S • (pairCreateAt G theta R * pairAt G theta S)) := by
    rw [map_smul]
    rfl
  simp_rw [heq, double_density_expansion]
  exact twoCenterExpansion_integrable G theta _

theorem physical_single_density_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    Integrable (fun z : ℂ × ℂ => occupationInner (physicalQ G theta) x
      (singleContractionAt G theta z.1 z.2 y))
      ((cellMeasure G 2).prod (cellMeasure G 2)) := by
  change Integrable (fun z : ℂ × ℂ => operatorForm (physicalQ G theta) x y
    (singleContractionAt G theta z.1 z.2)) _
  simp_rw [single_density_expansion]
  exact twoCenterExpansion_integrable G theta _

theorem matrixSingleContraction_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y) =
      ∫ R, ∫ S, occupationInner (physicalQ G theta) x
        (singleContractionAt G theta R S y) ∂cellMeasure G 2 ∂cellMeasure G 2 := by
  change operatorForm (physicalQ G theta) x y
    (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta)) =
      ∫ R, ∫ S, operatorForm (physicalQ G theta) x y
        (singleContractionAt G theta R S) ∂cellMeasure G 2 ∂cellMeasure G 2
  simp_rw [single_density_expansion]
  rw [twoCenterExpansion_integral]
  simp only [matrixSingleContraction, map_sum, map_smul, smul_eq_mul]

/-- Actual physical normal square in the original two cell integrals. The
three displayed integrands have independent product-measure integrability
proofs above, and the double term retains the actual raw pair Gram. -/
theorem physicalHamiltonian_normal_square_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (physicalHamiltonian G theta (physicalHamiltonian G theta y)) =
      (∫ R, ∫ S, occupationInner (physicalQ G theta) x
        ((pairCreateAt G theta R * pairCreateAt G theta S * pairAt G theta R * pairAt G theta S) y)
        ∂cellMeasure G 2 ∂cellMeasure G 2) +
      (∫ R, ∫ S, occupationInner (physicalQ G theta) x
        (singleContractionAt G theta R S y) ∂cellMeasure G 2 ∂cellMeasure G 2) +
      (∫ R, ∫ S, pairGramAt G theta R S * occupationInner (physicalQ G theta) x
        ((pairCreateAt G theta R * pairAt G theta S) y)
        ∂cellMeasure G 2 ∂cellMeasure G 2) := by
  change operatorForm (physicalQ G theta) x y
    (physicalHamiltonian G theta * physicalHamiltonian G theta) = _
  rw [physicalHamiltonian_normal_square, map_add, map_add]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (matrixFourBody_integral G theta x y)
      (matrixSingleContraction_integral G theta x y))
    (matrixDoubleContraction_integral G theta x y)

#print axioms pairCreateAt_expansion
#print axioms pairGramAt_expansion
#print axioms twoCenterExpansion_integrable
#print axioms twoCenterExpansion_integral
#print axioms physicalHamiltonian_square_integral
#print axioms matrixFourBody_integral
#print axioms matrixDoubleContraction_integral
#print axioms matrixSingleContraction_integral
#print axioms physical_square_density_integrable
#print axioms physical_fourBody_density_integrable
#print axioms physical_double_density_integrable
#print axioms physical_single_density_integrable
#print axioms physicalHamiltonian_normal_square_integral

end TorusLean.Shared.PhysicalFermionNormalSquare
