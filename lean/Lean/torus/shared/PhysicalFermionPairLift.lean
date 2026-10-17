import torus.shared.PhysicalFermionExterior
import torus.shared.PhysicalFermionPairContraction
import torus.shared.PhysicalFermionJetPair
import torus.shared.PhysicalFermionPairAnchor

/-! Identification of the literal physical m=1 pair anchor with the original
raw CAR pair, including all factorial and unordered-pair normalizations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionPairLift
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionM1Contact TorusLean.Shared.PhysicalFermionJetPair
open TorusLean.Shared.PhysicalFermionPairAnchor TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.PhysicalFermionPairContraction
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.NormalJetBridge

/-- The original physical pair count and m=1 derivative scale give exactly
 the normalized exterior factorial ratio. -/
theorem pairAnchorScale_jetScale (N : ℕ) :
    pairAnchorScale N * (jetScale 1 1 1)⁻¹ = sqrtFactorial (N+2) / sqrtFactorial N := by
  unfold pairAnchorScale jetScale sqrtFactorial
  norm_num [relativeCharge]
  rw [← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  rw [← Real.sqrt_div (Nat.cast_nonneg ((N+2).factorial))]
  congr 1
  have hn : (N.factorial : ℝ) ≠ 0 := by positivity
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hn]
  ring

lemma physicalOrbitalCoordinates_basis (G : Geometry) (theta : Twist)
    (i : Fin (physicalQ G theta+1)) :
    physicalOrbitalCoordinates G theta (orbitalBasis G theta (physicalIndexEquiv G theta i)) =
      mode i := by
  classical
  funext j
  rw [physicalOrbitalCoordinates_apply, OrthonormalBasis.inner_eq_ite]
  simp [mode, Pi.single_apply, eq_comm]

lemma physicalPairAnchor_coefficient (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (c : (Fin (N+2) → Fin (physicalQ G theta+1)) → ℂ) (w : Word G theta N) :
    pairAnchorScale N * m1SpectatorCoefficients G theta N R
      (fun v => c ((physicalIndexEquiv G theta).symm ∘ v)) w =
    (sqrtFactorial (N+2) / sqrtFactorial N / 2) *
      ∑ i, ∑ j, rawPairGram (physicalQ G theta)
        (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R)
        (mode i) (mode j) * c (Fin.cons i (Fin.cons j ((physicalIndexEquiv G theta).symm ∘ w))) := by
  classical
  let e := physicalIndexEquiv G theta
  unfold m1SpectatorCoefficients
  rw [← Equiv.sum_comp e (fun i => ∑ j,
    c (e.symm ∘ Fin.cons i (Fin.cons j w)) * pairM1 G theta i j R)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Equiv.sum_comp e (fun j =>
    pairAnchorScale N * (c (e.symm ∘ Fin.cons (e i) (Fin.cons j w)) * pairM1 G theta (e i) j R))]
  apply Finset.sum_congr rfl
  intro j _
  have he : e.symm ∘ Fin.cons (e i) (Fin.cons (e j) w) =
      Fin.cons i (Fin.cons j (e.symm ∘ w)) := by
    funext k
    refine Fin.cases ?_ (fun k => Fin.cases ?_ ?_ k) k
    · simp
    · simp
    · intro k; simp
  rw [he, pairM1_eq_rawM1PairCoefficient]
  have hp : rawM1PairCoefficient G theta (e i) (e j) R =
      rawPairGram (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
        (physicalJetCoordinates G theta 1 R) (mode i) (mode j) := by
    simp only [rawM1PairCoefficient, e, physicalOrbitalCoordinates_basis]
  rw [hp]
  have hscale := pairAnchorScale_jetScale N
  calc
    _ = (pairAnchorScale N * (jetScale 1 1 1)⁻¹) / 2 *
      (rawPairGram (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
        (physicalJetCoordinates G theta 1 R) (mode i) (mode j) *
          c (Fin.cons i (Fin.cons j (e.symm ∘ w)))) := by ring
    _ = _ := by rw [hscale]

/-- Pointwise full-carrier intertwining: the physical derivative anchor is
exactly the original unrenormalized CAR pair annihilation. -/
theorem physicalM1PairSection_intertwine (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) (N+2)) :
    physicalM1PairSection G theta N R (physicalExteriorEquiv G theta (N+2) x) =
      physicalExteriorEquiv G theta N
        (exteriorPairAnnihilate (-physicalJetCoordinates G theta 0 R)
          (physicalJetCoordinates G theta 1 R) x) := by
  classical
  apply Subtype.ext
  funext y
  change pairAnchorScale N * m1Contact N
    (tensorFunction G theta (N+2) (fun v =>
      (normalizedExterior (Fin (physicalQ G theta+1)) (N+2) x).val
        ((physicalIndexEquiv G theta).symm ∘ v))) (R,y) =
    tensorFunction G theta N (fun w =>
      (normalizedExterior (Fin (physicalQ G theta+1)) N
        (exteriorPairAnnihilate (-physicalJetCoordinates G theta 0 R)
          (physicalJetCoordinates G theta 1 R) x)).val
        ((physicalIndexEquiv G theta).symm ∘ w)) y
  rw [m1Contact_spectator_tensor]
  simp only [tensorFunction_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [← mul_assoc, physicalPairAnchor_coefficient, exteriorPairAnnihilate_ordered_determinant]

/-- The inverse complete physical map intertwines literal contact with the
same CAR pair on the ambient OAI exterior algebra. -/
theorem fullCarrier_m1_pair_CAR (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) :
    ((physicalExteriorEquiv G theta N).symm (physicalM1PairSection G theta N R f) :
      Space (physicalQ G theta)) =
      rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
        (physicalJetCoordinates G theta 1 R)
        ((physicalExteriorEquiv G theta (N+2)).symm f : Space (physicalQ G theta)) := by
  have h := physicalM1PairSection_intertwine G theta N R
    ((physicalExteriorEquiv G theta (N+2)).symm f)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply, exteriorPairAnnihilate_coe]

/-- Pointwise Parseval for the actual derivative output, before integration in R. -/
theorem fullCarrier_m1_pair_normSq (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) :
    (∫ y, ‖physicalM1PairFunction N R f.val y‖^2 ∂sectorMeasure G N) =
      occupationNormSq (physicalQ G theta)
        (rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
          (physicalJetCoordinates G theta 1 R)
          ((physicalExteriorEquiv G theta (N+2)).symm f : Space (physicalQ G theta))) := by
  have h := physicalExteriorEquiv_normSq G theta N
    ((physicalExteriorEquiv G theta N).symm (physicalM1PairSection G theta N R f))
  rw [Equiv.apply_symm_apply, fullCarrier_m1_pair_CAR] at h
  exact h

/-- The raw CAR energy density is actually integrable in the unchanged COM
cell measure; the quadratic-form equality is not a totalized-integral artifact. -/
theorem fullCarrier_m1_CAR_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    Integrable (fun R => occupationNormSq (physicalQ G theta)
      (rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
        (physicalJetCoordinates G theta 1 R)
        ((physicalExteriorEquiv G theta (N+2)).symm f : Space (physicalQ G theta))))
      (cellMeasure G 2) := by
  have hi := (fullCarrier_m1_normSq_integrable G theta N f).const_mul (‖pairAnchorScale N‖^2)
  have hp : Integrable (fun x : ℂ × Configuration N =>
      ‖physicalM1PairFunction N x.1 f.val x.2‖^2)
      ((cellMeasure G 2).prod (sectorMeasure G N)) := by
    simpa only [physicalM1PairFunction, norm_mul, mul_pow, PhysicalBosonDiagonal.contactMeasure,
      sectorMeasure, Prod.eta] using hi
  have heq : (fun R => ∫ y, ‖physicalM1PairFunction N R f.val y‖^2 ∂sectorMeasure G N) =
      (fun R => occupationNormSq (physicalQ G theta)
        (rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
          (physicalJetCoordinates G theta 1 R)
          ((physicalExteriorEquiv G theta (N+2)).symm f : Space (physicalQ G theta)))) := by
    funext R
    exact fullCarrier_m1_pair_normSq G theta N R f
  rw [← heq]
  exact hp.integral_prod_left

/-- The original integral over all literal m=1 particle-pair contacts equals
 the original raw-CAR pair quadratic form on every physical fixed-N state. -/
theorem fullCarrier_m1_energy_CAR (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    actualFermionM1Energy G (N+2) f.val =
      ∫ R, occupationNormSq (physicalQ G theta)
        (rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
          (physicalJetCoordinates G theta 1 R)
          ((physicalExteriorEquiv G theta (N+2)).symm f : Space (physicalQ G theta)))
        ∂cellMeasure G 2 := by
  rw [← physicalM1Pair_anchor_energy G theta N f]
  apply integral_congr_ae
  filter_upwards [] with R
  exact fullCarrier_m1_pair_normSq G theta N R f

/-- Zero physical contact energy is exactly the a.e. raw-pair CAR kernel. -/
theorem fullCarrier_m1_zero_iff_CAR_ae (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    actualFermionM1Energy G (N+2) f.val = 0 ↔
      (fun R => rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
        (physicalJetCoordinates G theta 1 R)
        ((physicalExteriorEquiv G theta (N+2)).symm f : Space (physicalQ G theta)))
        =ᵐ[cellMeasure G 2] 0 := by
  rw [fullCarrier_m1_energy_CAR, integral_eq_zero_iff_of_nonneg
    (fun R => occupationNormSq_nonneg (physicalQ G theta) _)
    (fullCarrier_m1_CAR_integrable G theta N f)]
  simp only [Filter.EventuallyEq, Pi.zero_apply, occupationNormSq_eq_zero]

lemma vectorAnnihilate_zero_sector {Q : ℕ} (a : Orbital Q)
    (x : Exterior (Fin (Q+1)) 0) : vectorAnnihilate Q a (x : Space Q) = 0 := by
  classical
  apply (occupationBasis Q).repr.injective
  ext A
  rw [vectorAnnihilate_sum]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    map_zero, Finsupp.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [annihilate_coordinate]
  split_ifs with hi
  · simp
  · have hc : (insert i A).card ≠ 0 := by simp
    rw [occupation_repr_exterior_other x (insert i A) hc]
    simp

lemma rawPairAnnihilate_zero_sector {Q : ℕ} (a b : Orbital Q)
    (x : Exterior (Fin (Q+1)) 0) : rawPairAnnihilate Q a b (x : Space Q) = 0 := by
  simp only [rawPairAnnihilate, Module.End.mul_apply, vectorAnnihilate_zero_sector, map_zero]

lemma rawPairAnnihilate_one_sector {Q : ℕ} (a b : Orbital Q)
    (x : Exterior (Fin (Q+1)) 1) : rawPairAnnihilate Q a b (x : Space Q) = 0 := by
  exact vectorAnnihilate_zero_sector b (exteriorAnnihilate a x)

/-- Uniform all-N original-energy identity, including the scalar vacuum and
one-particle sectors, where the original CAR pair itself vanishes. -/
theorem fullCarrier_m1_energy_CAR_all (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) :
    actualFermionM1Energy G N f.val =
      ∫ R, occupationNormSq (physicalQ G theta)
        (rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
          (physicalJetCoordinates G theta 1 R)
          ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)))
        ∂cellMeasure G 2 := by
  match N with
  | 0 => simp [rawPairAnnihilate_zero_sector, actualFermionM1Energy, occupationNormSq]
  | 1 => simp [rawPairAnnihilate_one_sector, actualFermionM1Energy, occupationNormSq]
  | N+2 => exact fullCarrier_m1_energy_CAR G theta N f

#print axioms physicalPairAnchor_coefficient
#print axioms physicalM1PairSection_intertwine
#print axioms fullCarrier_m1_pair_CAR
#print axioms fullCarrier_m1_pair_normSq
#print axioms fullCarrier_m1_CAR_integrable
#print axioms fullCarrier_m1_energy_CAR
#print axioms fullCarrier_m1_zero_iff_CAR_ae

#print axioms rawPairAnnihilate_zero_sector
#print axioms rawPairAnnihilate_one_sector
#print axioms fullCarrier_m1_energy_CAR_all
#print axioms pairAnchorScale_jetScale
end TorusLean.Shared.PhysicalFermionPairLift
