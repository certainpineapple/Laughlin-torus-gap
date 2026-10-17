import torus.shared.PhysicalBosonPolarization
import torus.shared.LLLThetaGaugeInverse
import PhysicalContactLiftCandidate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace TorusLean.Shared.PhysicalBosonContactForm

open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.Sym2Evaluation TorusLean.Boson.SpectatorControl
open TorusLean.Boson.ContactHilbertBridge
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonDiagonal
open TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Boson.PhysicalContactLiftCandidate
open scoped BigOperators ComplexConjugate TensorProduct

/-- Some existing TwoBodyLift APIs retain a nonempty mode-index instance.
Here it is derived from the already proved actual physical LLL dimension,
and is local to this concrete physical leaf rather than a theorem premise. -/
local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem physicalCoordinates_basis (G : Geometry) (theta : Twist)
    (i : PhysicalBosonSector.OrbitalIndex G theta) :
    physicalOrbitalCoordinates G theta (orbitalBasis G theta i) =
      EuclideanSpace.single i 1 := by
  change (orbitalBasis G theta).repr (orbitalBasis G theta i) = _
  exact (orbitalBasis G theta).repr_self i

theorem compressedPair_eq_symTensor (G : Geometry) (theta : Twist)
    (a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :
    TwoBodyLift.compressedPair a =
      symTensor (EuclideanSpace.single a.1 1) (EuclideanSpace.single a.2 1) := by
  rcases a with ⟨i, j⟩
  apply Subtype.ext
  simp only [TwoBodyLift.compressedPair, symTensor, TwoBodyLift.tensorBasis_apply]

theorem inverseTransport_compressedPair (G : Geometry) (theta : Twist)
    (a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :
    (sym2Transport (physicalOrbitalCoordinates G theta)).symm (TwoBodyLift.compressedPair a) =
      symTensor (orbitalBasis G theta a.1) (orbitalBasis G theta a.2) := by
  apply (sym2Transport (physicalOrbitalCoordinates G theta)).injective
  rw [LinearIsometryEquiv.apply_symm_apply, sym2Transport_symTensor,
    physicalCoordinates_basis, physicalCoordinates_basis, compressedPair_eq_symTensor]

/-- The coefficient is exactly the unchanged physical candidate's same Q†Q. -/
theorem contactPairKernel_actual (G : Geometry) (theta : Twist)
    (a b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :
    TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b =
      cellInner G 2 (pairProduct G theta a.1 a.2) (pairProduct G theta b.1 b.2) := by
  rw [TwoBodyLift.pairKernel_apply, contactPairCoordinates_inner,
    inverseTransport_compressedPair, inverseTransport_compressedPair,
    ← pairProduct_inner_same_h]

theorem modePair_evaluation_expansion (G : Geometry) (theta : Twist) (R : ℂ)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    modePair (evaluationCoordinates G theta R) f =
      ∑ a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        pairProduct G theta a.1 a.2 R • TwoBodyLift.pairRemove a f := by
  rw [TwoBodyLift.modePair_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  simp only [star_mul, Complex.star_def, evaluationCoordinates_conj, pairProduct]
  ring

theorem modePair_evaluation_inner_expansion (G : Geometry) (theta : Twist) (R : ℂ)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    occupationInner (fun _ => 1) (modePair (evaluationCoordinates G theta R) f)
      (modePair (evaluationCoordinates G theta R) f) =
      ∑ a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
          conj (pairProduct G theta a.1 a.2 R) * pairProduct G theta b.1 b.2 R *
            occupationInner (fun _ => 1) (TwoBodyLift.pairRemove a f)
              (TwoBodyLift.pairRemove b f) := by
  rw [modePair_evaluation_expansion]
  change ip _ _ = _
  simp only [TwoBodyLift.inner_sum_left, TwoBodyLift.inner_sum_right,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right, Complex.star_def,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change _ = _
  simp only [ip]
  ring

theorem pairProduct_cross_integrable (G : Geometry) (theta : Twist)
    (a b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) (c : ℂ) :
    Integrable (fun R => conj (pairProduct G theta a.1 a.2 R) *
      pairProduct G theta b.1 b.2 R * c) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2
    (((Complex.continuous_conj.comp (pairProduct_continuous G theta a.1 a.2)).mul
      (pairProduct_continuous G theta b.1 b.2)).mul continuous_const)

/-- Exact integrated normalized-pair form of the already existing same-h
lift; every finite occupation input is included, with no supplied budget. -/
theorem integrated_modePair_inner_same_lift (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    (∫ R, occupationInner (fun _ => 1) (modePair (evaluationCoordinates G theta R) f)
      (modePair (evaluationCoordinates G theta R) f) ∂cellMeasure G 2) =
        occupationInner (fun _ => 1) f (contactCoreHamiltonian G theta f) := by
  classical
  simp_rw [modePair_evaluation_inner_expansion]
  rw [integral_finsetSum Finset.univ (fun a ha =>
    integrable_finsetSum Finset.univ (fun b hb => pairProduct_cross_integrable G theta a b _))]
  have hf (a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :
      (∫ R, ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        conj (pairProduct G theta a.1 a.2 R) * pairProduct G theta b.1 b.2 R *
          occupationInner (fun _ => 1) (TwoBodyLift.pairRemove a f)
            (TwoBodyLift.pairRemove b f) ∂cellMeasure G 2) =
      ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b *
          occupationInner (fun _ => 1) (TwoBodyLift.pairRemove a f)
            (TwoBodyLift.pairRemove b f) := by
    rw [integral_finsetSum Finset.univ (fun b hb => pairProduct_cross_integrable G theta a b _)]
    apply Finset.sum_congr rfl
    intro b hb
    rw [integral_mul_const, contactPairKernel_actual]
    rfl
  simp_rw [hf]
  rw [← TwoBodyLift.twoBodyLift_inner]
  rfl

theorem integrated_modePair_normSq_same_lift (G : Geometry) (theta : Twist)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    (∫ R, occupationMetricNormSq (fun _ => 1)
      (modePair (evaluationCoordinates G theta R) f) ∂cellMeasure G 2) =
        (occupationInner (fun _ => 1) f (contactCoreHamiltonian G theta f)).re := by
  have h := integrated_modePair_inner_same_lift G theta f
  simp only [occupationInner_self] at h
  rw [integral_complex_ofReal] at h
  simpa only [Complex.ofReal_re] using congrArg Complex.re h

/-! The next bridge uses the literal cover diagonal and the original product
measure. Finite sums are integrated only after proving their actual cross
terms integrable; no Fock-to-function identity is supplied as an assumption. -/

theorem coreFunction_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun z => conj (coreFunction G theta N f z) *
      coreFunction G theta N g z) (sectorMeasure G N) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    induction g using MvPolynomial.induction_on' with
    | monomial m d =>
      simpa only [coreFunction_monomial, Pi.smul_apply, smul_eq_mul] using
        scaled_occupation_inner_integrable G theta N n m c d
    | add g h hg hh =>
      apply (hg.add hh).congr
      filter_upwards [] with z
      simp only [map_add, Pi.add_apply, mul_add]
  | add f h hf hh =>
    apply (hf.add hh).congr
    filter_upwards [] with z
    simp only [map_add, Pi.add_apply, add_mul]

theorem contactInner_const_mul (G : Geometry) (N : ℕ) (c d : ℂ)
    (F H : ContactConfiguration N → ℂ) :
    contactInner G N (fun x => c * F x) (fun x => d * H x) =
      conj c * d * contactInner G N F H := by
  unfold contactInner
  simp only [map_mul]
  simp_rw [show ∀ x : ContactConfiguration N,
    conj c * conj (F x) * (d * H x) =
      (conj c * d) * (conj (F x) * H x) by intro x; ring]
  exact integral_const_mul _ _

theorem contactInner_finiteSums {A B : Type*} (G : Geometry) (N : ℕ)
    (s : Finset A) (t : Finset B)
    (F : A → ContactConfiguration N → ℂ) (H : B → ContactConfiguration N → ℂ)
    (hi : ∀ a ∈ s, ∀ b ∈ t,
      Integrable (fun x => conj (F a x) * H b x) (contactMeasure G N)) :
    contactInner G N (fun x => ∑ a ∈ s, F a x) (fun x => ∑ b ∈ t, H b x) =
      ∑ a ∈ s, ∑ b ∈ t, contactInner G N (F a) (H b) := by
  classical
  simp only [contactInner, map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum s (fun a ha =>
    integrable_finsetSum t (fun b hb => hi a ha b hb))]
  apply Finset.sum_congr rfl
  intro a ha
  exact integral_finsetSum t (fun b hb => hi a ha b hb)

theorem separated_pair_core_cross_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (a b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta))
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun x : ContactConfiguration N =>
      conj (pairProduct G theta a.1 a.2 x.1 * coreFunction G theta N f x.2) *
        (pairProduct G theta b.1 b.2 x.1 * coreFunction G theta N g x.2))
      (contactMeasure G N) := by
  have hp : Integrable (fun R => conj (pairProduct G theta a.1 a.2 R) *
      pairProduct G theta b.1 b.2 R) (cellMeasure G 2) := by
    simpa only [mul_one] using pairProduct_cross_integrable G theta a b 1
  have h := hp.mul_prod (coreFunction_cross_integrable G theta N f g)
  unfold contactMeasure
  convert h using 1
  funext x
  simp only [map_mul]
  ring

theorem separated_pair_core_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (a b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta))
    (f g : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    contactInner G N
      (fun x => pairProduct G theta a.1 a.2 x.1 * coreFunction G theta N f x.2)
      (fun x => pairProduct G theta b.1 b.2 x.1 * coreFunction G theta N g x.2) =
      cellInner G 2 (pairProduct G theta a.1 a.2) (pairProduct G theta b.1 b.2) *
        sectorInner G N (coreFunction G theta N f) (coreFunction G theta N g) := by
  unfold contactInner
  simp only [map_mul]
  simp_rw [show ∀ x : ContactConfiguration N,
    conj (pairProduct G theta a.1 a.2 x.1) *
        conj (coreFunction G theta N f x.2) *
          (pairProduct G theta b.1 b.2 x.1 * coreFunction G theta N g x.2) =
      (conj (pairProduct G theta a.1 a.2 x.1) * pairProduct G theta b.1 b.2 x.1) *
        (conj (coreFunction G theta N f x.2) * coreFunction G theta N g x.2)
      by intro x; ring]
  simpa only [contactMeasure, cellInner, sectorInner] using
    integral_prod_mul (μ := cellMeasure G 2) (ν := sectorMeasure G N)
      (fun R => conj (pairProduct G theta a.1 a.2 R) * pairProduct G theta b.1 b.2 R)
      (fun z => conj (coreFunction G theta N f z) * coreFunction G theta N g z)

/-- Literal particle restriction has precisely the standard finite-sector
pair factor times the existing same-h normal-ordered form. The spectators
remain actual orbital functions integrated in the original mu_1^N. -/
theorem diagonal_coreFunction_inner_same_lift (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N + 2)) :
    contactInner G N (diagonalMap N (coreFunction G theta (N + 2) f))
      (diagonalMap N (coreFunction G theta (N + 2) f)) =
      (Complex.normSq (pairDiagonalFactor N) : ℂ) *
        occupationInner (fun _ => 1) f (contactCoreHamiltonian G theta f) := by
  classical
  let F : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta) →
      ContactConfiguration N → ℂ := fun a x =>
    pairProduct G theta a.1 a.2 x.1 * coreFunction G theta N (TwoBodyLift.pairRemove a f) x.2
  have hdiag : diagonalMap N (coreFunction G theta (N + 2) f) =
      fun x => pairDiagonalFactor N * ∑ a, F a x := by
    funext x
    rw [coreFunction_diagonal_pair, modePair_evaluation_expansion]
    simp only [map_sum, map_smul, LinearMap.sum_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, F]
  have hsum : contactInner G N (fun x => ∑ a, F a x) (fun x => ∑ a, F a x) =
      occupationInner (fun _ => 1) f (contactCoreHamiltonian G theta f) := by
    rw [contactInner_finiteSums G N Finset.univ Finset.univ F F
      (fun a ha b hb => separated_pair_core_cross_integrable G theta N a b _ _)]
    simp only [F]
    simp_rw [separated_pair_core_inner]
    have hgram (a b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta)) :
        sectorInner G N (coreFunction G theta N (TwoBodyLift.pairRemove a f))
          (coreFunction G theta N (TwoBodyLift.pairRemove b f)) =
        occupationInner (fun _ => 1) (TwoBodyLift.pairRemove a f)
          (TwoBodyLift.pairRemove b f) :=
      coreFunction_inner G theta N _ _ (TwoBodyLift.pairRemove_sector a N f hf)
        (TwoBodyLift.pairRemove_sector b N f hf)
    simp_rw [hgram, ← contactPairKernel_actual]
    exact (TwoBodyLift.twoBodyLift_inner (contactPairCoordinates G theta) f).symm
  rw [hdiag, contactInner_const_mul, hsum, ← Complex.normSq_eq_conj_mul_self]

theorem diagonal_coreFunction_normSq_same_lift (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N + 2)) :
    (∫ x, ‖diagonalMap N (coreFunction G theta (N + 2) f) x‖ ^ 2
      ∂contactMeasure G N) =
      (2 * (N.factorial : ℝ) / ((N + 2).factorial : ℝ)) *
        (occupationInner (fun _ => 1) f (contactCoreHamiltonian G theta f)).re := by
  have hself : (contactInner G N
      (diagonalMap N (coreFunction G theta (N + 2) f))
      (diagonalMap N (coreFunction G theta (N + 2) f))).re =
      ∫ x, ‖diagonalMap N (coreFunction G theta (N + 2) f) x‖ ^ 2
        ∂contactMeasure G N := by
    have h : contactInner G N
        (diagonalMap N (coreFunction G theta (N + 2) f))
        (diagonalMap N (coreFunction G theta (N + 2) f)) =
        ((∫ x, ‖diagonalMap N (coreFunction G theta (N + 2) f) x‖ ^ 2
          ∂contactMeasure G N : ℝ) : ℂ) := by
      simp only [contactInner, Complex.conj_mul', ← Complex.ofReal_pow]
      exact integral_complex_ofReal
    rw [h, Complex.ofReal_re]
  rw [← hself, diagonal_coreFunction_inner_same_lift G theta N f hf]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [pairDiagonalFactor_normSq]

/-- An explicit permutation of actual particle labels. For distinct a,b it
takes canonical slots 0,1 to a,b; its other slots enumerate all spectators. -/
def particlePairPermutation (N : ℕ) (a b : Fin (N + 2)) : Equiv.Perm (Fin (N + 2)) :=
  Equiv.swap 0 a * Equiv.swap 1 (Equiv.swap 0 a b)

theorem particlePairPermutation_zero (N : ℕ) (a b : Fin (N + 2)) (hab : a ≠ b) :
    particlePairPermutation N a b 0 = a := by
  have hc : Equiv.swap 0 a b ≠ (0 : Fin (N + 2)) := by
    intro h
    have hba : b = a := (Equiv.swap 0 a).injective
      (h.trans (Equiv.swap_apply_right 0 a).symm)
    exact hab hba.symm
  unfold particlePairPermutation
  rw [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne Fin.zero_ne_one (Ne.symm hc), Equiv.swap_apply_left]

theorem particlePairPermutation_one (N : ℕ) (a b : Fin (N + 2)) :
    particlePairPermutation N a b 1 = b := by
  simp only [particlePairPermutation, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- Literal restriction to the actual pair a,b, keeping actual spectator
coordinates. This is defined by coordinate insertion, before using symmetry. -/
def insertParticlePairDiagonal (N : ℕ) (a b : Fin (N + 2))
    (x : ContactConfiguration N) : Configuration (N + 2) :=
  insertDiagonal N x ∘ (particlePairPermutation N a b).symm

theorem insertParticlePairDiagonal_left (N : ℕ) (a b : Fin (N + 2)) (hab : a ≠ b)
    (x : ContactConfiguration N) : insertParticlePairDiagonal N a b x a = x.1 := by
  have h : (particlePairPermutation N a b).symm a = 0 := by
    apply (particlePairPermutation N a b).injective
    rw [Equiv.apply_symm_apply, particlePairPermutation_zero N a b hab]
  simp only [insertParticlePairDiagonal, Function.comp_apply, h, insertDiagonal,
    Fin.cons_zero]

theorem insertParticlePairDiagonal_right (N : ℕ) (a b : Fin (N + 2))
    (x : ContactConfiguration N) : insertParticlePairDiagonal N a b x b = x.1 := by
  have h : (particlePairPermutation N a b).symm b = 1 := by
    apply (particlePairPermutation N a b).injective
    rw [Equiv.apply_symm_apply, particlePairPermutation_one]
  simp only [insertParticlePairDiagonal, Function.comp_apply, h, insertDiagonal,
    Fin.cons_one, Fin.cons_zero]

theorem insertParticlePairDiagonal_spectator (N : ℕ) (a b : Fin (N + 2))
    (x : ContactConfiguration N) (c : Fin N) :
    insertParticlePairDiagonal N a b x
      (particlePairPermutation N a b c.succ.succ) = x.2 c := by
  simp only [insertParticlePairDiagonal, Function.comp_apply, Equiv.symm_apply_apply,
    insertDiagonal, Fin.cons_succ]

theorem coreFunction_particlePairDiagonal (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (a b : Fin (N + 2)) (x : ContactConfiguration N) :
    coreFunction G theta (N + 2) f (insertParticlePairDiagonal N a b x) =
      diagonalMap N (coreFunction G theta (N + 2) f) x := by
  exact coreFunction_permute_configuration G theta (N + 2) f
    (particlePairPermutation N a b).symm (insertDiagonal N x)

/-- Actual sorted particle-pair counting, including empty low sectors. The
factor counts a<b in Fin M and is independent of any Hamiltonian. -/
theorem sorted_particle_pair_sum (M : ℕ) (c : ℝ) :
    (∑ a : Fin M, ∑ b : Fin M, if a < b then c else 0) =
      (M : ℝ) * ((M : ℝ) - 1) / 2 * c := by
  induction M with
  | zero => simp
  | succ M ih =>
    simp only [Fin.sum_univ_succ, lt_self_iff_false, if_false, Fin.succ_pos,
      if_true, Fin.not_lt_zero, Fin.succ_lt_succ_iff, zero_add, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ih]
    push_cast
    ring

theorem sorted_particle_pair_sum_low (M : ℕ) (hM : M < 2)
    (e : Fin M → Fin M → ℝ) :
    (∑ a : Fin M, ∑ b : Fin M, if a < b then e a b else 0) = 0 := by
  have hab (a b : Fin M) : ¬a < b := by
    have ha := a.isLt
    have hb := b.isLt
    change ¬a.val < b.val
    omega
  simp only [hab, if_false, Finset.sum_const_zero]

/-- The physical energy is the sum of actual literal a<b restrictions,
each in mu_2 times the original spectator product measure. -/
def particlePairContactEnergy (G : Geometry) (N : ℕ)
    (F : Configuration (N + 2) → ℂ) : ℝ :=
  ∑ a : Fin (N + 2), ∑ b : Fin (N + 2),
    if a < b then
      ∫ x, ‖F (insertParticlePairDiagonal N a b x)‖ ^ 2 ∂contactMeasure G N
    else 0

/-- The actual finite-particle pair sum equals the original same-h lift
form. Its combinatorial factor cancels exactly against the proved sector
factorial ratio; there is no cell-mass, eigenvalue or sqrt(2) adjustment. -/
theorem particlePairContactEnergy_same_lift (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous (N + 2)) :
    particlePairContactEnergy G N (coreFunction G theta (N + 2) f) =
      (occupationInner (fun _ => 1) f (contactCoreHamiltonian G theta f)).re := by
  unfold particlePairContactEnergy
  simp_rw [coreFunction_particlePairDiagonal]
  rw [sorted_particle_pair_sum, diagonal_coreFunction_normSq_same_lift G theta N f hf]
  have hfac : ((N + 2).factorial : ℝ) =
      ((N + 2 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) := by
    rw [show N + 2 = (N + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have h0 : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have h1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  push_cast at h1 h2
  field_simp [h0, h1, h2]
  <;> ring

/-- All-N actual pair energy. The two low sectors have an empty actual
sorted-pair index, as proved separately above; every higher sector uses the
literal coordinate insertion definition. -/
def actualParticleContactEnergy (G : Geometry) :
    (M : ℕ) → (Configuration M → ℂ) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | N + 2, F => particlePairContactEnergy G N F

theorem actualParticleContactEnergy_low (G : Geometry) (M : ℕ) (hM : M < 2)
    (F : Configuration M → ℂ) : actualParticleContactEnergy G M F = 0 := by
  cases M with
  | zero => rfl
  | succ M =>
    cases M with
    | zero => rfl
    | succ N => omega

/-- Equality of the actual particle-contact form and the existing same-h
occupation Hamiltonian on every physical sector image, including N=0,1.
This asserts no surjectivity onto a larger physical carrier. -/
theorem actualParticleContactEnergy_same_lift (G : Geometry) (theta : Twist) (M : ℕ)
    (f : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous M) :
    actualParticleContactEnergy G M (coreFunction G theta M f) =
      (occupationInner (fun _ => 1) f (contactCoreHamiltonian G theta f)).re := by
  cases M with
  | zero =>
    have hz : contactCoreHamiltonian G theta f = 0 :=
      TwoBodyLift.twoBodyLift_low_sector (contactPairCoordinates G theta) 0 (by omega) f hf
    simp only [actualParticleContactEnergy, hz, occupationInner_zero_right, Complex.zero_re]
  | succ M =>
    cases M with
    | zero =>
      have hz : contactCoreHamiltonian G theta f = 0 :=
        TwoBodyLift.twoBodyLift_low_sector (contactPairCoordinates G theta) 1 (by omega) f hf
      simp only [actualParticleContactEnergy, hz, occupationInner_zero_right, Complex.zero_re]
    | succ N =>
      exact particlePairContactEnergy_same_lift G theta N f hf

end TorusLean.Shared.PhysicalBosonContactForm
