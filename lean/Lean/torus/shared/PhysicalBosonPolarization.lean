import torus.shared.PhysicalBosonDiagonal

/-! Concrete Riesz-polynomial representation of the already proved physical
sector function. This supplies a route to the all-N actual diagonal/removal
identity using the existing polynomial adjointness, without assuming it. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace TorusLean.Shared.PhysicalBosonPolarization

open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector
open scoped BigOperators ComplexConjugate

def evaluationCoordinates (G : Geometry) (theta : Twist) (R : ℂ) :
    Orbital (OrbitalIndex G theta) :=
  (orbitalBasis G theta).repr (evaluationKernel G theta 1 R)

/-- With the existing conjugate-first inner product, raw Riesz coordinates
are conjugates of orbital values. No sign or normalization is changed. -/
theorem evaluationCoordinates_conj (G : Geometry) (theta : Twist) (R : ℂ)
    (i : OrbitalIndex G theta) :
    conj (evaluationCoordinates G theta R i) = (orbitalBasis G theta i).val R := by
  rw [evaluationCoordinates, OrthonormalBasis.repr_apply_apply]
  rw [inner_conj_symm, evaluationKernel_reproduces]

def kernelPolynomial (G : Geometry) (theta : Twist) (N : ℕ)
    (z : Configuration N) : Core (OrbitalIndex G theta) ℂ :=
  ∏ a, modeLinear (evaluationCoordinates G theta (z a))

theorem permutation_word_card (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N) :
    Fintype.card {σ : Equiv.Perm (Fin N) // w ∘ σ = v} =
      if wordOccupation G theta N w = wordOccupation G theta N v then
        occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w)
      else 0 := by
  classical
  by_cases h : wordOccupation G theta N w = wordOccupation G theta N v
  · rw [if_pos h]
    obtain ⟨σ, hσ⟩ := (wordOccupation_eq_iff G theta N v w).mp h.symm
    rw [← hσ]
    let e : {τ : Equiv.Perm (Fin N) // w ∘ τ = w ∘ σ} ≃
        {τ : Equiv.Perm (Fin N) // w ∘ σ = w ∘ τ} :=
      Equiv.subtypeEquivRight (fun _ => eq_comm)
    rw [Fintype.card_congr e, permutation_match_card]
  · rw [if_neg h]
    letI : IsEmpty {σ : Equiv.Perm (Fin N) // w ∘ σ = v} := ⟨fun σ =>
      h (by rw [← wordOccupation_comp_perm G theta N w σ.val, σ.property])⟩
    simp

/-- The standard repeated-label permutation sum equals the factorial weight
times the distinct word fiber. This is proved from the real stabilizer count. -/
theorem permutation_word_sum (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (z : Configuration N) :
    (∑ σ : Equiv.Perm (Fin N), wordFunction G theta N (w ∘ σ) z) =
      (occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) : ℂ) *
        ∑ v : Word G theta N,
          if wordOccupation G theta N v = wordOccupation G theta N w then
            wordFunction G theta N v z else 0 := by
  classical
  have hc (v : Word G theta N) :
      (∑ σ : Equiv.Perm (Fin N), if w ∘ σ = v then wordFunction G theta N v z else 0) =
        (if wordOccupation G theta N w = wordOccupation G theta N v then
          (occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) : ℂ)
        else 0) * wordFunction G theta N v z := by
    have ht : (∑ σ : Equiv.Perm (Fin N),
        if w ∘ σ = v then wordFunction G theta N v z else 0) =
        (∑ σ : Equiv.Perm (Fin N), if w ∘ σ = v then (1 : ℂ) else 0) *
          wordFunction G theta N v z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      split_ifs <;> simp
    rw [ht, Finset.sum_boole, ← Fintype.card_subtype, permutation_word_card]
    split_ifs <;> simp
  calc
    _ = ∑ σ : Equiv.Perm (Fin N), ∑ v : Word G theta N,
        if w ∘ σ = v then wordFunction G theta N v z else 0 := by simp
    _ = ∑ v : Word G theta N, ∑ σ : Equiv.Perm (Fin N),
        if w ∘ σ = v then wordFunction G theta N v z else 0 := Finset.sum_comm
    _ = _ := by
      simp_rw [hc]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases h : wordOccupation G theta N w = wordOccupation G theta N v
      · simp only [h, ite_true]
      · simp only [h, Ne.symm h, ite_false, mul_zero, zero_mul]

theorem occupationFunction_fiber (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) (z : Configuration N) :
    occupationFunction G theta N n z =
      (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
        (occupationMetricWeight (fun _ => 1) n : ℂ) *
          ∑ v : Word G theta N,
            if wordOccupation G theta N v = n then wordFunction G theta N v z else 0 := by
  classical
  by_cases hn : n.degree = N
  · rw [occupationFunction, dif_pos hn, symWordFunction, permutation_word_sum,
      occupationWord_spec, mul_assoc]
  · rw [occupationFunction, dif_neg hn]
    have hv (v : Word G theta N) : wordOccupation G theta N v ≠ n := by
      intro h
      apply hn
      rw [← h, wordOccupation_degree]
    simp [hv]

theorem kernelPolynomial_expansion (G : Geometry) (theta : Twist) (N : ℕ)
    (z : Configuration N) :
    kernelPolynomial G theta N z =
      ∑ w : Word G theta N, MvPolynomial.monomial (wordOccupation G theta N w)
        (∏ a, evaluationCoordinates G theta (z a) (w a)) := by
  classical
  unfold kernelPolynomial modeLinear
  simp_rw [MvPolynomial.C_mul_X_eq_monomial]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w hw
  exact (MvPolynomial.monomial_sum_prod Finset.univ
    (fun a => Finsupp.single (w a) 1)
    (fun a => evaluationCoordinates G theta (z a) (w a))).symm

theorem kernelPolynomial_coeff_conj (G : Geometry) (theta : Twist) (N : ℕ)
    (z : Configuration N) (n : OrbitalIndex G theta →₀ ℕ) :
    conj ((kernelPolynomial G theta N z).coeff n) =
      ∑ w : Word G theta N,
        if wordOccupation G theta N w = n then wordFunction G theta N w z else 0 := by
  classical
  rw [kernelPolynomial_expansion]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, map_sum,
    apply_ite, map_zero, map_prod, evaluationCoordinates_conj, wordFunction, eq_comm]

theorem occupationInner_monomial_right (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (n : OrbitalIndex G theta →₀ ℕ) (c : ℂ) :
    occupationInner (fun _ => 1) p (MvPolynomial.monomial n c) =
      (occupationMetricWeight (fun _ => 1) n : ℂ) * conj (p.coeff n) * c := by
  have h := occupationInner_conj_symm (fun _ => 1) (MvPolynomial.monomial n c) p
  rw [occupationInner_monomial_left] at h
  rw [← h]
  simp only [star_mul, star_star, star_natCast, Complex.star_def, Complex.conj_conj]
  ring

/-- Concrete polarization formula for the actual all-N physical function
map, with precisely the original factorial pairing and Riesz conjugation. -/
theorem coreFunction_eq_kernel_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (z : Configuration N) :
    coreFunction G theta N f z =
      (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
        occupationInner (fun _ => 1) (kernelPolynomial G theta N z) f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [coreFunction_monomial, Pi.smul_apply, smul_eq_mul, occupationFunction_fiber,
      occupationInner_monomial_right, kernelPolynomial_coeff_conj]
    ring
  | add f g hf hg =>
    simp only [map_add, Pi.add_apply, occupationInner_add_right, hf, hg, mul_add]

open TorusLean.Shared.PhysicalBosonDiagonal

theorem kernelPolynomial_diagonal (G : Geometry) (theta : Twist) (N : ℕ)
    (x : ContactConfiguration N) :
    kernelPolynomial G theta (N + 2) (insertDiagonal N x) =
      modeLinear (evaluationCoordinates G theta x.1) *
        modeLinear (evaluationCoordinates G theta x.1) *
          kernelPolynomial G theta N x.2 := by
  simp only [kernelPolynomial, insertDiagonal, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
  ring

theorem coreFunction_diagonal_raw (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (x : ContactConfiguration N) :
    diagonalMap N (coreFunction G theta (N + 2) f) x =
      (((Real.sqrt ((N + 2).factorial : ℝ))⁻¹ : ℝ) : ℂ) *
        occupationInner (fun _ => 1) (kernelPolynomial G theta N x.2)
          (modeAnnihilate (evaluationCoordinates G theta x.1)
            (modeAnnihilate (evaluationCoordinates G theta x.1) f)) := by
  change coreFunction G theta (N + 2) f (insertDiagonal N x) = _
  rw [coreFunction_eq_kernel_inner, kernelPolynomial_diagonal]
  have hc : modeLinear (evaluationCoordinates G theta x.1) *
      modeLinear (evaluationCoordinates G theta x.1) * kernelPolynomial G theta N x.2 =
      modeCreate (evaluationCoordinates G theta x.1)
        (modeCreate (evaluationCoordinates G theta x.1) (kernelPolynomial G theta N x.2)) := by
    simp [modeCreate_apply, mul_assoc]
  rw [hc, mode_create_adjoint, mode_create_adjoint]

/-- The factor is the original normalized pair factor together with the
ratio of the two standard finite-sector factorial normalizations. -/
def pairDiagonalFactor (N : ℕ) : ℂ :=
  (((Real.sqrt ((N + 2).factorial : ℝ))⁻¹ : ℝ) : ℂ) *
    (Real.sqrt 2 : ℂ) * (Real.sqrt (N.factorial : ℝ) : ℂ)

/-- Actual diagonal/removal identity for every N and every finite core input.
The left side is literal function restriction; no transport definition or
isometry/pair-sum assumption appears. -/
theorem coreFunction_diagonal_pair (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (x : ContactConfiguration N) :
    diagonalMap N (coreFunction G theta (N + 2) f) x =
      pairDiagonalFactor N *
        coreFunction G theta N (modePair (evaluationCoordinates G theta x.1) f) x.2 := by
  rw [coreFunction_diagonal_raw, coreFunction_eq_kernel_inner]
  simp only [pairDiagonalFactor, modePair, LinearMap.smul_apply, LinearMap.comp_apply,
    occupationInner_smul_right, Complex.ofReal_inv]
  have hnR : Real.sqrt (N.factorial : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos N)))
  have hnC : (Real.sqrt (N.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnR
  have htwoR : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have htwoC : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast htwoR
  have hnextR : Real.sqrt ((N + 2).factorial : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos (N + 2))))
  have hnextC : (Real.sqrt ((N + 2).factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnextR
  field_simp [hnC, htwoC, hnextC]
  <;> ring

theorem pairDiagonalFactor_normSq (N : ℕ) :
    Complex.normSq (pairDiagonalFactor N) =
      2 * (N.factorial : ℝ) / ((N + 2).factorial : ℝ) := by
  unfold pairDiagonalFactor
  simp only [Complex.ofReal_inv, Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (Nat.cast_nonneg _), Real.mul_self_sqrt (by norm_num),
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  ring

end TorusLean.Shared.PhysicalBosonPolarization
