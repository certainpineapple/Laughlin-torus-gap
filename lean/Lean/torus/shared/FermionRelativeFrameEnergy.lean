import torus.shared.FermionRelativeFrameTensor

/-! Exact norm of the full spectator tensor, in the unchanged physical
spectator measure, equals the previously constructed true four-body CAR form.
All integrations below are finite sums of proved integrable cross terms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.PhysicalFermionPairContraction TorusLean.Shared.PhysicalFermionNormalSquare
open scoped TensorProduct ComplexConjugate BigOperators

lemma tensorFunction_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (c d : Word G theta N → ℂ) :
    Integrable (fun z => conj (tensorFunction G theta N c z) * tensorFunction G theta N d z)
      (sectorMeasure G N) := by
  classical
  have h := integrable_finsetSum Finset.univ (fun w _ =>
    integrable_finsetSum Finset.univ (fun v _ =>
      scaled_word_inner_integrable G theta N w v (c w) (d v)))
  convert h using 1
  funext z
  simp only [tensorFunction_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma physicalExteriorLinear_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (x y : Exterior (Fin (physicalQ G theta+1)) N) :
    Integrable (fun z => conj (physicalExteriorLinear G theta N x z) *
      physicalExteriorLinear G theta N y z) (sectorMeasure G N) := by
  change Integrable (fun z => conj ((physicalExteriorEquiv G theta N x).val z) *
    (physicalExteriorEquiv G theta N y).val z) _
  rw [physicalExteriorEquiv_apply, physicalExteriorEquiv_apply]
  exact tensorFunction_cross_integrable G theta N _ _

lemma doubleSpectator_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) (a c b d : PairIndex G theta) :
    Integrable (fun z => conj (doubleSpectator G theta N x a c z) *
      doubleSpectator G theta N x b d z) (sectorMeasure G N) :=
  physicalExteriorLinear_cross_integrable G theta N _ _

def sectionKernel (G : Geometry) (theta : Twist)
    (a b : PairIndex G theta) (R : ℂ) : ℂ :=
  conj ((pairSection G theta a).val R) * (pairSection G theta b).val R

lemma sectionKernel_integrable (G : Geometry) (theta : Twist) (a b : PairIndex G theta) :
    Integrable (sectionKernel G theta a b) (cellMeasure G 2) :=
  cellInner_integrable G 2 _ _ (rawLLL_continuous G theta 2 (pairSection G theta a))
    (rawLLL_continuous G theta 2 (pairSection G theta b))

lemma sectionKernel_integral (G : Geometry) (theta : Twist) (a b : PairIndex G theta) :
    (∫ R, sectionKernel G theta a b R ∂cellMeasure G 2) =
      inner ℂ (pairSection G theta a) (pairSection G theta b) := rfl

/-- Auxiliary finite Gram expression, derived twice below from independent
physical and CAR integrals. -/
def doublePairGramForm (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) : ℂ :=
  ∑ a : PairIndex G theta, ∑ c : PairIndex G theta,
    ∑ b : PairIndex G theta, ∑ d : PairIndex G theta,
      (inner ℂ (pairSection G theta a) (pairSection G theta b) *
        inner ℂ (pairSection G theta c) (pairSection G theta d)) *
      occupationInner (physicalQ G theta)
        (modePairAnnihilate (physicalQ G theta) c (modePairAnnihilate (physicalQ G theta) a x))
        (modePairAnnihilate (physicalQ G theta) d (modePairAnnihilate (physicalQ G theta) b x))

theorem doublePairTensor_inner_expansion (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) (z : Configuration N) :
    inner ℂ (doublePairTensor G theta N x z) (doublePairTensor G theta N x z) =
      ∑ a : PairIndex G theta, ∑ c : PairIndex G theta,
        ∑ b : PairIndex G theta, ∑ d : PairIndex G theta,
          (conj (doubleSpectator G theta N x a c z) * doubleSpectator G theta N x b d z) *
            (inner ℂ (pairSection G theta a) (pairSection G theta b) *
              inner ℂ (pairSection G theta c) (pairSection G theta d)) := by
  simp only [doublePairTensor]
  simp only [sum_inner]
  simp only [inner_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  rw [inner_smul_left (pairSection G theta a ⊗ₜ[ℂ] pairSection G theta c)
    (doubleSpectator G theta N x b d z •
      (pairSection G theta b ⊗ₜ[ℂ] pairSection G theta d)) _,
    inner_smul_right (pairSection G theta a ⊗ₜ[ℂ] pairSection G theta c)
      (pairSection G theta b ⊗ₜ[ℂ] pairSection G theta d) _, TensorProduct.inner_tmul]
  ring

theorem doublePairTensor_inner_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    Integrable (fun z => inner ℂ (doublePairTensor G theta N x z)
      (doublePairTensor G theta N x z)) (sectorMeasure G N) := by
  simp_rw [doublePairTensor_inner_expansion]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun c _ =>
    integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ =>
      (doubleSpectator_cross_integrable G theta N x a c b d).mul_const _))))

theorem doublePairTensor_normSq_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    Integrable (fun z => ‖doublePairTensor G theta N x z‖^2) (sectorMeasure G N) := by
  simp_rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact (doublePairTensor_inner_integrable G theta N x).re

theorem doublePairTensor_integrated_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    (∫ z, inner ℂ (doublePairTensor G theta N x z) (doublePairTensor G theta N x z)
      ∂sectorMeasure G N) = doublePairGramForm G theta x := by
  classical
  simp_rw [doublePairTensor_inner_expansion]
  unfold doublePairGramForm
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun c _ =>
    integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ =>
      (doubleSpectator_cross_integrable G theta N x a c b d).mul_const _))))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun b _ =>
    integrable_finsetSum _ (fun d _ =>
      (doubleSpectator_cross_integrable G theta N x a c b d).mul_const _)))]
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ =>
    (doubleSpectator_cross_integrable G theta N x a c b d).mul_const _))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun d _ =>
    (doubleSpectator_cross_integrable G theta N x a c b d).mul_const _)]
  apply Finset.sum_congr rfl
  intro d _
  rw [integral_mul_const]
  have h := physicalExteriorEquiv_inner G theta N
    (exteriorModePair G theta N c (exteriorModePair G theta (N+2) a x))
    (exteriorModePair G theta N d (exteriorModePair G theta (N+2) b x))
  change (∫ z, conj (doubleSpectator G theta N x a c z) *
    doubleSpectator G theta N x b d z ∂sectorMeasure G N) = _ at h
  rw [h]
  simp only [exteriorModePair_coe]
  ring

/-- The actual pairAt double output, with all four CAR contractions kept. -/
theorem doublePairCAR_inner_expansion (G : Geometry) (theta : Twist) (R S : ℂ)
    (x : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) (pairAt G theta S (pairAt G theta R x))
      (pairAt G theta S (pairAt G theta R x)) =
      ∑ a : PairIndex G theta, ∑ c : PairIndex G theta,
        ∑ b : PairIndex G theta, ∑ d : PairIndex G theta,
          (sectionKernel G theta a b R * sectionKernel G theta c d S) *
          occupationInner (physicalQ G theta)
            (modePairAnnihilate (physicalQ G theta) c (modePairAnnihilate (physicalQ G theta) a x))
            (modePairAnnihilate (physicalQ G theta) d (modePairAnnihilate (physicalQ G theta) b x)) := by
  classical
  have heq : pairAt G theta S (pairAt G theta R x) =
      ∑ a : PairIndex G theta, ∑ c : PairIndex G theta,
        ((pairSection G theta a).val R * (pairSection G theta c).val S) •
          modePairAnnihilate (physicalQ G theta) c
            (modePairAnnihilate (physicalQ G theta) a x) := by
    rw [pairAt_section_expansion G theta R]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    rw [pairAt_section_expansion G theta S]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [heq]
  simp only [occupationInner_sum_left]
  simp only [occupationInner_sum_right]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  simp only [occupationInner_smul_left, occupationInner_smul_right, sectionKernel,
    map_mul, Complex.star_def]
  ring

def sectionGram (G : Geometry) (theta : Twist) (a b : PairIndex G theta) : ℂ :=
  ∫ R, sectionKernel G theta a b R ∂cellMeasure G 2

def sectionExpansion (G : Geometry) (theta : Twist)
    (T : PairIndex G theta → PairIndex G theta → PairIndex G theta → PairIndex G theta → ℂ)
    (R S : ℂ) : ℂ :=
  ∑ p, ∑ q, ∑ r, ∑ s,
    (sectionKernel G theta p q R * sectionKernel G theta r s S) * T p q r s

lemma sectionExpansion_inner_integral (G : Geometry) (theta : Twist)
    (T : PairIndex G theta → PairIndex G theta →
      PairIndex G theta → PairIndex G theta → ℂ) (R : ℂ) :
    (∫ S, sectionExpansion G theta T R S ∂cellMeasure G 2) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (sectionKernel G theta p q R * sectionGram G theta r s) * T p q r s := by
  unfold sectionExpansion
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta r s).const_mul _).mul_const _))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta r s).const_mul _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta r s).const_mul _).mul_const _))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta r s).const_mul _).mul_const _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- Fubini-compatible genuine double-cell coefficient calculation. -/
theorem sectionExpansion_integral (G : Geometry) (theta : Twist)
    (T : PairIndex G theta → PairIndex G theta →
      PairIndex G theta → PairIndex G theta → ℂ) :
    (∫ R, ∫ S, sectionExpansion G theta T R S ∂cellMeasure G 2 ∂cellMeasure G 2) =
      ∑ p, ∑ q, ∑ r, ∑ s,
        (sectionGram G theta p q * sectionGram G theta r s) * T p q r s := by
  simp_rw [sectionExpansion_inner_integral]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta p q).mul_const _).mul_const _))))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta p q).mul_const _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta p q).mul_const _).mul_const _))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun s _ =>
      ((sectionKernel_integrable G theta p q).mul_const _).mul_const _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const, integral_mul_const]
  rfl


/-- Identification with the previously defined physical four-body operator,
not a new surrogate definition of S4. -/
theorem doublePairGramForm_eq_matrixFourBody (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    doublePairGramForm G theta x =
      occupationInner (physicalQ G theta) x
        (matrixFourBody (physicalQ G theta) (contactMatrix G theta) x) := by
  rw [matrixFourBody_integral]
  simp_rw [fourBody_density_normSq, ← occupationInner_self, doublePairCAR_inner_expansion]
  have heq (R S : ℂ) :
      (∑ a : PairIndex G theta, ∑ c : PairIndex G theta,
        ∑ b : PairIndex G theta, ∑ d : PairIndex G theta,
          (sectionKernel G theta a b R * sectionKernel G theta c d S) *
          occupationInner (physicalQ G theta)
            (modePairAnnihilate (physicalQ G theta) c (modePairAnnihilate (physicalQ G theta) a x))
            (modePairAnnihilate (physicalQ G theta) d (modePairAnnihilate (physicalQ G theta) b x))) =
      sectionExpansion G theta (fun a b c d => occupationInner (physicalQ G theta)
        (modePairAnnihilate (physicalQ G theta) c (modePairAnnihilate (physicalQ G theta) a x))
        (modePairAnnihilate (physicalQ G theta) d (modePairAnnihilate (physicalQ G theta) b x))) R S := by
    unfold sectionExpansion
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  simp_rw [heq]
  rw [sectionExpansion_integral]
  unfold doublePairGramForm
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

/-- Every physical spectator tensor has exactly the true original S4 norm. -/
theorem physicalDoublePairTensor_integrated_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) :
    (∫ z, ‖physicalDoublePairTensor G theta N f z‖^2 ∂sectorMeasure G N) =
      (occupationInner (physicalQ G theta)
        ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta))
        (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
          ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta)))).re := by
  unfold physicalDoublePairTensor
  simp_rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [integral_re (doublePairTensor_inner_integrable G theta N _),
    doublePairTensor_integrated_inner, doublePairGramForm_eq_matrixFourBody]
  rfl

#print axioms physicalExteriorLinear_cross_integrable
#print axioms doublePairTensor_normSq_integrable
#print axioms doublePairTensor_integrated_inner
#print axioms doublePairCAR_inner_expansion
#print axioms doublePairGramForm_eq_matrixFourBody
#print axioms physicalDoublePairTensor_integrated_normSq
end TorusLean.Shared.FermionRelativeFrame
