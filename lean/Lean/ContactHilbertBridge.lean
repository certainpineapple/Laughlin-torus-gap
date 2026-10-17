import TwoBodyLift

/-! Hilbert-space Q†Q and evaluation comparison, before instantiation of the
root-owned physical cell/LLL candidates. All hypotheses below are explicit:
Q and point evaluation are actual continuous maps, with their actual Riesz
identity. No all-N budget, physical H, dimension equality or flux is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TorusLean.Boson.ContactHilbertBridge

open scoped ComplexConjugate ComplexOrder TensorProduct BigOperators
open TorusLean.Boson.UnitaryTransport TorusLean.Boson.Sym2Evaluation

noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

/-- The actual same contact operator, not a supplied energy budget. -/
def adjointSquare (Q : E →L[ℂ] F) : E →L[ℂ] E := Q.adjoint.comp Q

def rieszRankOne (v : E) : E →L[ℂ] E := InnerProductSpace.rankOne ℂ v v

theorem adjointSquare_positive (Q : E →L[ℂ] F) :
    (adjointSquare Q).IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self Q

theorem adjointSquare_inner (Q : E →L[ℂ] F) (ψ φ : E) :
    inner ℂ ψ (adjointSquare Q φ) = inner ℂ (Q ψ) (Q φ) := by
  exact ContinuousLinearMap.adjoint_inner_right Q ψ (Q φ)

theorem adjointSquare_energy (Q : E →L[ℂ] F) (ψ : E) :
    (inner ℂ ψ (adjointSquare Q ψ)).re = ‖Q ψ‖ ^ 2 := by
  rw [adjointSquare_inner]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem rieszRankOne_energy (v ψ : E) :
    (inner ℂ ψ (rieszRankOne v ψ)).re = ‖inner ℂ v ψ‖ ^ 2 := by
  simp only [rieszRankOne, InnerProductSpace.rankOne_apply, inner_smul_right]
  rw [← inner_conj_symm (𝕜 := ℂ) ψ v]
  change (inner ℂ v ψ * conj (inner ℂ v ψ)).re = ‖inner ℂ v ψ‖ ^ 2
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
    congrArg Complex.re (Complex.mul_conj' (inner ℂ v ψ))

/-- A true point-evaluation norm bound relative to the same actual Q†Q. -/
theorem evaluation_relative_bound (Q : E →L[ℂ] F) (ev : F →L[ℂ] ℂ)
    (v : E) (hv : ∀ ψ : E, ev (Q ψ) = inner ℂ v ψ) (ψ : E) :
    ‖inner ℂ v ψ‖ ^ 2 ≤ ‖ev‖ ^ 2 * (inner ℂ ψ (adjointSquare Q ψ)).re := by
  rw [← hv ψ, adjointSquare_energy]
  have hb := ev.le_opNorm (Q ψ)
  calc
    _ ≤ (‖ev‖ * ‖Q ψ‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hb
    _ = _ := by ring

/-- The two-body difference is proved positive from actual evaluation, not assumed for each N. -/
theorem evaluation_rankOne_difference_positive (Q : E →L[ℂ] F) (ev : F →L[ℂ] ℂ)
    (v : E) (hv : ∀ ψ : E, ev (Q ψ) = inner ℂ v ψ) :
    (((‖ev‖ ^ 2 : ℝ) : ℂ) • adjointSquare Q - rieszRankOne v).IsPositive := by
  have hc : (0 : ℂ) ≤ ((‖ev‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (sq_nonneg ‖ev‖)
  have hsym := ((adjointSquare_positive Q).smul_of_nonneg hc).isSymmetric.sub
    (InnerProductSpace.isPositive_rankOne_self v).isSymmetric
  refine ⟨hsym, ?_⟩
  intro ψ
  change 0 ≤ (inner ℂ
    ((((‖ev‖ ^ 2 : ℝ) : ℂ) • adjointSquare Q - rieszRankOne v) ψ) ψ).re
  have hr : (inner ℂ
      ((((‖ev‖ ^ 2 : ℝ) : ℂ) • adjointSquare Q - rieszRankOne v) ψ) ψ).re =
      (inner ℂ ψ
      ((((‖ev‖ ^ 2 : ℝ) : ℂ) • adjointSquare Q - rieszRankOne v) ψ)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hr]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [rieszRankOne_energy]
  exact sub_nonneg.mpr (evaluation_relative_bound Q ev v hv ψ)

/-- Official tensor isometry commutes with exchanging the identical factors. -/
theorem tensorTransport_comm (U : E ≃ₗᵢ[ℂ] F) (w : E ⊗[ℂ] E) :
    (TensorProduct.comm ℂ F F) (TensorProduct.congrIsometry U U w) =
      TensorProduct.congrIsometry U U ((TensorProduct.comm ℂ E E) w) := by
  exact (TensorProduct.map_comm U.toLinearMap U.toLinearMap w).symm

/-- Actual restriction of a unitary orbital change to the actual Sym² spaces. -/
def sym2Transport (U : E ≃ₗᵢ[ℂ] F) :
    Sym2Evaluation.Sym2 E ≃ₗᵢ[ℂ] Sym2Evaluation.Sym2 F where
  toFun ψ := ⟨TensorProduct.congrIsometry U U ψ.val, by
    rw [mem_Sym2, tensorTransport_comm, (mem_Sym2 ψ.val).mp ψ.property]⟩
  invFun ψ := ⟨TensorProduct.congrIsometry U.symm U.symm ψ.val, by
    rw [mem_Sym2, tensorTransport_comm, (mem_Sym2 ψ.val).mp ψ.property]⟩
  left_inv ψ := by
    apply Subtype.ext
    exact (TensorProduct.congrIsometry U U).symm_apply_apply ψ.val
  right_inv ψ := by
    apply Subtype.ext
    exact (TensorProduct.congrIsometry U U).apply_symm_apply ψ.val
  map_add' ψ φ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c ψ := by apply Subtype.ext; exact map_smul _ _ _
  norm_map' ψ := (TensorProduct.congrIsometry U U).norm_map ψ.val

theorem sym2Transport_val (U : E ≃ₗᵢ[ℂ] F) (ψ : Sym2Evaluation.Sym2 E) :
    (sym2Transport U ψ).val = TensorProduct.congrIsometry U U ψ.val := rfl

theorem sym2Transport_symTensor (U : E ≃ₗᵢ[ℂ] F) (u v : E) :
    sym2Transport U (symTensor u v) = symTensor (U u) (U v) := by
  apply Subtype.ext
  simp only [sym2Transport_val, symTensor, symProject_apply, map_smul, map_add,
    TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul, TensorProduct.comm_tmul]
  rfl

end

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Old canonical lift positivity also covers a zero-dimensional orbital space. -/
theorem twoBodyLift_nonneg_all (h : TwoBodyLift.PairSpace ι →ₗ[ℂ] TwoBodyLift.PairSpace ι)
    (hh : LinearMap.IsPositive (𝕜 := ℂ) (E := TwoBodyLift.PairSpace ι) h)
    (f : Core ι ℂ) : 0 ≤ (SpectatorControl.ip f (TwoBodyLift.twoBodyLift h f)).re := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    letI := hempty
    simp [TwoBodyLift.twoBodyLift, SpectatorControl.ip, occupationInner_zero_right]
  | inr hnonempty =>
    letI := hnonempty
    exact TwoBodyLift.twoBodyLift_nonneg h hh f

/-- No unproved positive physical dimension is needed for the canonical pair comparison. -/
theorem modePair_le_scaled_lift_all (u : Orbital ι)
    (h : TwoBodyLift.PairSpace ι →ₗ[ℂ] TwoBodyLift.PairSpace ι) (c : ℝ)
    (hd : LinearMap.IsPositive (𝕜 := ℂ) (E := TwoBodyLift.PairSpace ι)
      ((c : ℂ) • h - TwoBodyLift.coherentRankOne u)) (f : Core ι ℂ) :
    SpectatorControl.q (modePair u f) ≤ c * (SpectatorControl.ip f (TwoBodyLift.twoBodyLift h f)).re := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    letI := hempty
    simp [modePair, modeAnnihilate, TwoBodyLift.twoBodyLift,
      SpectatorControl.ip, occupationInner_zero_right,
      SpectatorControl.q, occupationMetricNormSq]
  | inr hnonempty =>
    letI := hnonempty
    exact TwoBodyLift.modePair_le_scaled_lift u h c hd f

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  [FiniteDimensional ℂ E]

local instance sym2Complete : CompleteSpace (Sym2Evaluation.Sym2 E) :=
  FiniteDimensional.complete ℂ (Sym2Evaluation.Sym2 E)

local instance pairSpaceComplete : CompleteSpace (TwoBodyLift.PairSpace ι) :=
  FiniteDimensional.complete ℂ (TwoBodyLift.PairSpace ι)

/-- Pull back the exact Q along the actual induced Sym² orbital isometry. -/
noncomputable def coordinateQ (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) : TwoBodyLift.PairSpace ι →L[ℂ] F :=
  Q.comp (sym2Transport U).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem coordinateQ_apply (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (ψ : TwoBodyLift.PairSpace ι) :
    coordinateQ U Q ψ = Q ((sym2Transport U).symm ψ) := rfl

/-- Exact Q-coordinate adjoint square, using the actual same Hilbert norms. -/
noncomputable def coordinatePairOperator (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) :
    TwoBodyLift.PairSpace ι →ₗ[ℂ] TwoBodyLift.PairSpace ι :=
  (adjointSquare (E := TwoBodyLift.PairSpace ι) (F := F) (coordinateQ U Q)).toLinearMap

theorem coordinatePairOperator_inner (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (ψ φ : TwoBodyLift.PairSpace ι) :
    inner ℂ ψ (coordinatePairOperator U Q φ) =
      inner ℂ ((sym2Transport U).symm ψ)
        (adjointSquare Q ((sym2Transport U).symm φ)) := by
  calc
    _ = inner ℂ (coordinateQ U Q ψ) (coordinateQ U Q φ) :=
      adjointSquare_inner (E := TwoBodyLift.PairSpace ι) (F := F) _ ψ φ
    _ = _ := (adjointSquare_inner (E := Sym2Evaluation.Sym2 E) (F := F)
      Q ((sym2Transport U).symm ψ) ((sym2Transport U).symm φ)).symm

theorem coordinatePairOperator_positive (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := TwoBodyLift.PairSpace ι)
      (coordinatePairOperator U Q) := by
  have hform (ψ φ : TwoBodyLift.PairSpace ι) :
      inner ℂ ψ (coordinatePairOperator U Q φ) =
        inner ℂ (coordinateQ U Q ψ) (coordinateQ U Q φ) :=
    adjointSquare_inner (E := TwoBodyLift.PairSpace ι) (F := F) _ ψ φ
  constructor
  · intro ψ φ
    have hc := congrArg (starRingEnd ℂ) (hform φ ψ)
    simp only [inner_conj_symm] at hc
    rw [hc, hform]
  · intro ψ
    change 0 ≤ (inner ℂ (coordinatePairOperator U Q ψ) ψ).re
    have hr : (inner ℂ (coordinatePairOperator U Q ψ) ψ).re =
        (inner ℂ ψ (coordinatePairOperator U Q ψ)).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hr, hform]
    exact inner_self_nonneg (𝕜 := ℂ)

/-- The Riesz identity transports with its exact complex phase. -/
theorem coordinateQ_evaluation (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (ev : F →L[ℂ] ℂ) (v : E)
    (hv : ∀ ψ : Sym2Evaluation.Sym2 E, ev (Q ψ) = inner ℂ (symTensor v v) ψ)
    (ψ : TwoBodyLift.PairSpace ι) :
    ev (coordinateQ U Q ψ) = inner ℂ (symTensor (U v) (U v)) ψ := by
  rw [coordinateQ_apply, hv]
  have hi := TensorProduct.inner_map_map (𝕜 := ℂ)
    U.toLinearIsometry U.toLinearIsometry (symTensor v v).val ((sym2Transport U).symm ψ).val
  change inner ℂ (sym2Transport U (symTensor v v))
    (sym2Transport U ((sym2Transport U).symm ψ)) =
    inner ℂ (symTensor v v) ((sym2Transport U).symm ψ) at hi
  simpa only [sym2Transport_symTensor, LinearIsometryEquiv.apply_symm_apply] using hi.symm

/-- A derived actual two-body positive difference, not a family of sector hypotheses. -/
theorem coordinate_pair_difference_positive (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (ev : F →L[ℂ] ℂ) (v : E)
    (hv : ∀ ψ : Sym2Evaluation.Sym2 E, ev (Q ψ) = inner ℂ (symTensor v v) ψ) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := TwoBodyLift.PairSpace ι)
      ((((‖ev‖ ^ 2 : ℝ) : ℂ) • coordinatePairOperator U Q) -
        TwoBodyLift.coherentRankOne (U v)) := by
  have hp := evaluation_rankOne_difference_positive (E := TwoBodyLift.PairSpace ι) (F := F) (coordinateQ U Q) ev
    (symTensor (U v) (U v)) (coordinateQ_evaluation U Q ev v hv)
  simpa only [coordinatePairOperator, rieszRankOne, TwoBodyLift.coherentRankOne,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul] using hp.toLinearMap

/-- Worker-owned lift of the actual same Q; root owns its physical H name. -/
noncomputable def coordinateHamiltonian (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  TwoBodyLift.twoBodyLift (coordinatePairOperator U Q)

theorem coordinateHamiltonian_nonneg (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (f : Core ι ℂ) :
    0 ≤ (SpectatorControl.ip f (coordinateHamiltonian U Q f)).re :=
  twoBodyLift_nonneg_all _ (coordinatePairOperator_positive U Q) f

/-- Actual same-Q finite-core pair control with the derived charge-two evaluation norm. -/
theorem coordinate_pair_bound (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (ev : F →L[ℂ] ℂ) (v : E)
    (hv : ∀ ψ : Sym2Evaluation.Sym2 E, ev (Q ψ) = inner ℂ (symTensor v v) ψ)
    (f : Core ι ℂ) :
    SpectatorControl.q (modePair (U v) f) ≤ ‖ev‖ ^ 2 *
      (SpectatorControl.ip f (coordinateHamiltonian U Q f)).re :=
  modePair_le_scaled_lift_all (U v) _ _ (coordinate_pair_difference_positive U Q ev v hv) f

theorem coordinateHamiltonian_sym2_inner (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (ψ φ : TwoBodyLift.PairSpace ι) :
    SpectatorControl.ip (fockPairMap ψ.val) (coordinateHamiltonian U Q (fockPairMap φ.val)) =
      inner ℂ ((sym2Transport U).symm ψ)
        (adjointSquare Q ((sym2Transport U).symm φ)) := by
  classical
  rw [← coordinatePairOperator_inner]
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    letI := hempty
    have hz : φ = 0 := Subsingleton.elim _ _
    subst φ
    simp [coordinateHamiltonian, SpectatorControl.ip, occupationInner_zero_right]
  | inr hnonempty =>
    letI := hnonempty
    exact TwoBodyLift.twoBodyLift_sym2_inner _ ψ φ

theorem coordinateHamiltonian_sector (U : E ≃ₗᵢ[ℂ] Orbital ι)
    (Q : Sym2Evaluation.Sym2 E →L[ℂ] F) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) : (coordinateHamiltonian U Q f).IsHomogeneous N := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    letI := hempty
    have hz : coordinateHamiltonian U Q f = 0 := by
      simp [coordinateHamiltonian, TwoBodyLift.twoBodyLift]
    rw [hz]
    exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) N
  | inr hnonempty =>
    letI := hnonempty
    exact TwoBodyLift.twoBodyLift_sector_all _ N f hf

end Coordinates
end TorusLean.Boson.ContactHilbertBridge
