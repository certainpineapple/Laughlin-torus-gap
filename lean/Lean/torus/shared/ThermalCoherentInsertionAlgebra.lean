import Sym2Evaluation

/-! Finite tensor-to-Fock insertion maps in the existing factorial metric.
The spectator 1/2 is derived from the actual Sym² map, independently of
any center-of-mass change of variables or infinite thermal transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentInsertionAlgebra
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl
open TorusLean.Boson.Sym2Evaluation
open scoped TensorProduct ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem fockCoherentPair_comm (u v : Orbital ι) :
    fockCoherentPair u v = fockCoherentPair v u := by
  simp only [fockCoherentPair, modeCreate_apply, mul_one]
  rw [mul_comm]

/-- Sym² is the actual flip-fixed Hilbert tensor subspace, and its existing
isometric Fock map gives precisely 1/sqrt(2), including equal/nonorthogonal modes. -/
theorem fockSym2Map_symTensor (u v : Orbital ι) :
    fockSym2Map (symTensor u v) = fockCoherentPair u v := by
  change fockPairMap (symTensor u v).val = _
  rw [symTensor_val, map_smul, map_add, fockPairMap_tmul, fockPairMap_tmul,
    fockCoherentPair_comm v u, ← two_smul ℂ (fockCoherentPair u v), smul_smul]
  norm_num

/-- Creation by a genuine physical Sym² vector on the unchanged polynomial core. -/
def sym2Insert (w : Sym2Evaluation.Sym2 (Orbital ι)) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  LinearMap.mulLeft ℂ (fockSym2Map w)

theorem sym2Insert_symTensor_apply (u v : Orbital ι) (f : Core ι ℂ) :
    sym2Insert (symTensor u v) f =
      ((Real.sqrt 2)⁻¹ : ℂ) • modeCreate u (modeCreate v f) := by
  simp only [sym2Insert, LinearMap.mulLeft_apply, fockSym2Map_symTensor,
    fockCoherentPair, modeCreate_apply, mul_one, smul_mul_assoc, mul_assoc]

/-- The adjoint row is derived from actual creation/annihilation adjointness. -/
theorem sym2Insert_symTensor_adjoint (u v : Orbital ι) (f p : Core ι ℂ) :
    occupationInner (fun _ => 1) (sym2Insert (symTensor u v) f) p =
      occupationInner (fun _ => 1) f
        (((Real.sqrt 2)⁻¹ : ℂ) • spectatorPair u v p) := by
  rw [sym2Insert_symTensor_apply, occupationInner_smul_left,
    mode_create_adjoint, mode_create_adjoint, occupationInner_smul_right]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal,
    spectatorPair, LinearMap.comp_apply]

theorem sym2Insert_same_adjoint (u : Orbital ι) (f p : Core ι ℂ) :
    occupationInner (fun _ => 1) (sym2Insert (symTensor u u) f) p =
      occupationInner (fun _ => 1) f (modePair u p) := by
  simpa only [modePair, LinearMap.smul_apply, LinearMap.comp_apply, spectatorPair]
    using sym2Insert_symTensor_adjoint u u f p

def threeInsertionBilinear : Sym2Evaluation.Sym2 (Orbital ι) →ₗ[ℂ] Orbital ι →ₗ[ℂ] Core ι ℂ where
  toFun w := (sym2Insert w).comp modeLinearMap
  map_add' w z := by
    ext u
    simp [sym2Insert, map_add, add_mul]
  map_smul' c w := by
    ext u
    simp [sym2Insert, map_smul, smul_mul_assoc]

def fourInsertionBilinear : Sym2Evaluation.Sym2 (Orbital ι) →ₗ[ℂ] Sym2Evaluation.Sym2 (Orbital ι) →ₗ[ℂ] Core ι ℂ where
  toFun w := (sym2Insert w).comp fockSym2Map
  map_add' w z := by
    ext u
    simp [sym2Insert, map_add, add_mul]
  map_smul' c w := by
    ext u
    simp [sym2Insert, map_smul, smul_mul_assoc]

/-- Distinguished-pair insertion followed by the actual Fock multiplication. -/
def threeInsertion : (Sym2Evaluation.Sym2 (Orbital ι) ⊗[ℂ] Orbital ι) →ₗ[ℂ] Core ι ℂ :=
  TensorProduct.lift threeInsertionBilinear

def fourInsertion : (Sym2Evaluation.Sym2 (Orbital ι) ⊗[ℂ] Sym2Evaluation.Sym2 (Orbital ι)) →ₗ[ℂ] Core ι ℂ :=
  TensorProduct.lift fourInsertionBilinear

theorem threeInsertion_tmul (w : Sym2Evaluation.Sym2 (Orbital ι)) (v : Orbital ι) :
    threeInsertion (w ⊗ₜ[ℂ] v) = fockSym2Map w * modeLinear v := by
  simp [threeInsertion, threeInsertionBilinear, sym2Insert, modeLinearMap]

theorem fourInsertion_tmul (w v : Sym2Evaluation.Sym2 (Orbital ι)) :
    fourInsertion (w ⊗ₜ[ℂ] v) = fockSym2Map w * fockSym2Map v := by
  simp [fourInsertion, fourInsertionBilinear, sym2Insert]

theorem threeInsertion_sector (w : Sym2Evaluation.Sym2 (Orbital ι) ⊗[ℂ] Orbital ι) :
    (threeInsertion w).IsHomogeneous 3 := by
  induction w using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) 3)
  | add w z hw hz => simpa only [map_add] using hw.add hz
  | tmul w u =>
    rw [threeInsertion_tmul]
    exact (fockPairMap_sector w.val).mul (modeLinear_sector u)

theorem fourInsertion_sector (w : Sym2Evaluation.Sym2 (Orbital ι) ⊗[ℂ] Sym2Evaluation.Sym2 (Orbital ι)) :
    (fourInsertion w).IsHomogeneous 4 := by
  induction w using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) 4)
  | add w z hw hz => simpa only [map_add] using hw.add hz
  | tmul w u =>
    rw [fourInsertion_tmul]
    exact (fockPairMap_sector w.val).mul (fockPairMap_sector u.val)

/-- Actual annihilation row of the coherent three-body insertion, on every core. -/
theorem threeInsertion_coherent_adjoint (u v : Orbital ι) (f p : Core ι ℂ) :
    occupationInner (fun _ => 1)
      (threeInsertion (symTensor u u ⊗ₜ[ℂ] v) * f) p =
      occupationInner (fun _ => 1) f (modeAnnihilate v (modePair u p)) := by
  rw [threeInsertion_tmul, mul_assoc, ← modeCreate_apply v f]
  change occupationInner (fun _ => 1)
    (sym2Insert (symTensor u u) (modeCreate v f)) p = _
  rw [sym2Insert_same_adjoint, mode_create_adjoint]

/-- The two-spectator annihilation row retains exactly its Sym² 1/sqrt(2).
There is no COM normalization in this finite tensor identity. -/
def normalizedDoubleRemoval (u v w : Orbital ι) (p : Core ι ℂ) : Core ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • spectatorPair v w (modePair u p)

theorem fourInsertion_coherent_adjoint (u v w : Orbital ι) (f p : Core ι ℂ) :
    occupationInner (fun _ => 1)
      (fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w) * f) p =
      occupationInner (fun _ => 1) f (normalizedDoubleRemoval u v w p) := by
  rw [fourInsertion_tmul, mul_assoc]
  change occupationInner (fun _ => 1)
    (sym2Insert (symTensor u u) (sym2Insert (symTensor v w) f)) p = _
  rw [sym2Insert_same_adjoint, sym2Insert_symTensor_adjoint]
  rfl

/-- The unique spectator 1/2 follows by squaring the actual Sym² amplitude. -/
theorem normalizedDoubleRemoval_normSq (u v w : Orbital ι) (p : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (normalizedDoubleRemoval u v w p) =
      (1/2 : ℝ) * occupationMetricNormSq (fun _ => 1) (spectatorPair v w (modePair u p)) := by
  unfold normalizedDoubleRemoval
  rw [← q, canonical_normSq_smul]
  have hs : Complex.normSq (((Real.sqrt 2)⁻¹ : ℂ)) = 1/2 := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [hs]

/-- Primal seed analysis and the actual annihilation row agree on the vacuum. -/
theorem threeInsertion_coherent_analysis (u v : Orbital ι) (p : Core ι ℂ) :
    occupationInner (fun _ => 1) (threeInsertion (symTensor u u ⊗ₜ[ℂ] v)) p =
      occupationInner (fun _ => 1) (1 : Core ι ℂ) (modeAnnihilate v (modePair u p)) := by
  simpa only [mul_one] using threeInsertion_coherent_adjoint u v 1 p

theorem fourInsertion_coherent_analysis (u v w : Orbital ι) (p : Core ι ℂ) :
    occupationInner (fun _ => 1) (fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w)) p =
      occupationInner (fun _ => 1) (1 : Core ι ℂ) (normalizedDoubleRemoval u v w p) := by
  simpa only [mul_one] using fourInsertion_coherent_adjoint u v w 1 p

#print axioms fockSym2Map_symTensor
#print axioms sym2Insert_symTensor_adjoint
#print axioms threeInsertion_sector
#print axioms fourInsertion_sector
#print axioms threeInsertion_coherent_adjoint
#print axioms fourInsertion_coherent_adjoint
#print axioms normalizedDoubleRemoval_normSq
#print axioms threeInsertion_coherent_analysis
#print axioms fourInsertion_coherent_analysis
end TorusLean.Shared.ThermalCoherentInsertionAlgebra
