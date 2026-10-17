import torus.shared.ThermalCoherentJacobiFourRotation
import TwoBodyLift

/-! A genuine finite Parseval identity on each complete two-mode degree
sector. This is proved in the original factorial occupation form and then
transported by the actual second-quantized spectator unitary. The final
identity holds after arbitrary finite linear functionals, so it does not
assume that the physical W4 insertion is isometric or injective. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourParseval
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl
open TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.ThermalCoherentJacobiFourRotation
open scoped BigOperators ComplexConjugate

abbrev DegreeIndex (t : ℕ) := {n : Fin 2 →₀ ℕ // n.degree=t}

noncomputable instance degreeIndexFintype (t : ℕ) : Fintype (DegreeIndex t) := by
  classical
  have h : Set.Finite {n : Fin 2 →₀ ℕ | n.degree=t} := by
    simpa only [Finsupp.degree_eq_weight_one] using
      Finsupp.finite_of_nat_weight_eq (fun _ : Fin 2 => 1) (by simp) t
  exact h.fintype

private def frameRoot (n : Fin 2 →₀ ℕ) : ℂ :=
  (Real.sqrt (occupationMetricWeight (fun _ : Fin 2=>1) n : ℝ):ℂ)

private theorem frameRoot_ne_zero (n : Fin 2 →₀ ℕ) : frameRoot n≠0 := by
  have h := occupationMetricWeight_pos (fun _ : Fin 2=>1) (by simp) n
  unfold frameRoot
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast h)))

private theorem frameRoot_sq (n : Fin 2 →₀ ℕ) :
    (frameRoot n)^2=(occupationMetricWeight (fun _ : Fin 2=>1) n : ℂ) := by
  unfold frameRoot
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (occupationMetricWeight (fun _ : Fin 2=>1) n))

/-- Normalized canonical monomial, with the actual factorial occupation weight. -/
def degreeFrame (t : ℕ) (n : DegreeIndex t) : Core (Fin 2) ℂ :=
  MvPolynomial.monomial n.val (frameRoot n.val)⁻¹

theorem degreeFrame_homogeneous (t : ℕ) (n : DegreeIndex t) :
    (degreeFrame t n).IsHomogeneous t :=
  MvPolynomial.isHomogeneous_monomial _ n.property

theorem degreeFrame_inner_coeff (t : ℕ) (n : DegreeIndex t) (f : Core (Fin 2) ℂ) :
    ip (degreeFrame t n) f = frameRoot n.val * f.coeff n.val := by
  rw [ip, degreeFrame, occupationInner_monomial_left]
  have hc : star (frameRoot n.val)=(frameRoot n.val) := by simp [frameRoot,Complex.star_def]
  rw [star_inv₀, hc, ← frameRoot_sq]
  field_simp [frameRoot_ne_zero] <;> ring

theorem degreeFrame_orthonormal (t : ℕ) (n m : DegreeIndex t) :
    ip (degreeFrame t n) (degreeFrame t m) = if n=m then 1 else 0 := by
  classical
  rw [degreeFrame_inner_coeff]
  by_cases h:n=m
  · subst m
    simp [degreeFrame, MvPolynomial.coeff_monomial, frameRoot_ne_zero]
  · have hv : n.val≠m.val := fun he => h (Subtype.ext he)
    simp [degreeFrame, MvPolynomial.coeff_monomial, hv, Ne.symm hv,h]

/-- Complete finite-sector reconstruction; no proper occupation block is used. -/
theorem degreeFrame_expansion (t : ℕ) (f : Core (Fin 2) ℂ) (hf : f.IsHomogeneous t) :
    f = ∑ n : DegreeIndex t, ip (degreeFrame t n) f • degreeFrame t n := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.coeff_sum]
  by_cases hm:m.degree=t
  · let m' : DegreeIndex t := ⟨m,hm⟩
    rw [Finset.sum_eq_single m']
    · rw [MvPolynomial.coeff_smul, degreeFrame_inner_coeff]
      simp only [degreeFrame, MvPolynomial.coeff_monomial, m', ↓reduceIte, smul_eq_mul]
      field_simp [frameRoot_ne_zero] <;> ring
    · intro n hn hne
      have hv : n.val≠m := fun he => hne (Subtype.ext he)
      simp [degreeFrame,MvPolynomial.coeff_monomial,hv,Ne.symm hv]
    · simp
  · rw [hf.coeff_eq_zero hm]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hv : n.val≠m := fun he => hm (he ▸ n.property)
    simp [degreeFrame,MvPolynomial.coeff_monomial,hv,Ne.symm hv]

/-- Finite Riesz vector for a fixed linear functional on the whole core,
restricted to one genuine degree sector. -/
def finiteDualVector (t : ℕ) (F : Core (Fin 2) ℂ →ₗ[ℂ] ℂ) : Core (Fin 2) ℂ :=
  ∑ n : DegreeIndex t, star (F (degreeFrame t n)) • degreeFrame t n

theorem finiteDualVector_homogeneous (t : ℕ) (F : Core (Fin 2) ℂ →ₗ[ℂ] ℂ) :
    (finiteDualVector t F).IsHomogeneous t := by
  apply (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ t).sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (degreeFrame_homogeneous t n)

theorem finiteDualVector_reproduces (t : ℕ) (F : Core (Fin 2) ℂ →ₗ[ℂ] ℂ)
    (f : Core (Fin 2) ℂ) (hf : f.IsHomogeneous t) : ip (finiteDualVector t F) f=F f := by
  rw [finiteDualVector, inner_sum_left]
  simp only [TwoBodyLift.inner_smul_left, star_star]
  conv_rhs => rw [degreeFrame_expansion t f hf, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem degreeFrame_cross (t : ℕ) (f g : Core (Fin 2) ℂ) (hf : f.IsHomogeneous t) :
    ∑ n : DegreeIndex t, star (ip f (degreeFrame t n))*ip g (degreeFrame t n) = ip g f := by
  conv_rhs => rw [degreeFrame_expansion t f hf, inner_sum_right]
  simp only [TwoBodyLift.inner_smul_right]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show star (ip f (degreeFrame t n))=ip (degreeFrame t n) f from
    occupationInner_conj_symm (fun _=>1) f (degreeFrame t n)]

/-- Exact finite cross-form trace invariance after arbitrary linear maps.
The input sector is the full degree sector, and U is an actual orbital unitary. -/
theorem secondQuantization_finite_dual_cross (U : Unitary (Fin 2)) (t : ℕ)
    (F G : Core (Fin 2) ℂ →ₗ[ℂ] ℂ) :
    ∑ n : DegreeIndex t, star (F (secondQuantization U (degreeFrame t n))) *
      G (secondQuantization U (degreeFrame t n)) =
    ∑ n : DegreeIndex t, star (F (degreeFrame t n))*G (degreeFrame t n) := by
  let f := finiteDualVector t F
  let g := finiteDualVector t G
  have hf := finiteDualVector_homogeneous t F
  have hg := finiteDualVector_homogeneous t G
  have hF (n : DegreeIndex t) : F (secondQuantization U (degreeFrame t n))=
      ip (secondQuantization U.symm f) (degreeFrame t n) := by
    rw [← finiteDualVector_reproduces t F _ (secondQuantization_sector U t _ (degreeFrame_homogeneous t n))]
    have h := secondQuantization_inner U (secondQuantization U.symm f) (degreeFrame t n)
    rw [secondQuantization_inverse] at h
    exact h
  have hG (n : DegreeIndex t) : G (secondQuantization U (degreeFrame t n))=
      ip (secondQuantization U.symm g) (degreeFrame t n) := by
    rw [← finiteDualVector_reproduces t G _ (secondQuantization_sector U t _ (degreeFrame_homogeneous t n))]
    have h := secondQuantization_inner U (secondQuantization U.symm g) (degreeFrame t n)
    rw [secondQuantization_inverse] at h
    exact h
  simp_rw [hF,hG]
  rw [degreeFrame_cross t _ _ (secondQuantization_sector U.symm t f hf)]
  have hunit : ip (secondQuantization U.symm g) (secondQuantization U.symm f)=ip g f :=
    secondQuantization_inner U.symm g f
  rw [hunit]
  symm
  have he := degreeFrame_cross t f g hf
  simpa only [f,g,finiteDualVector_reproduces t F _ (degreeFrame_homogeneous t _),
    finiteDualVector_reproduces t G _ (degreeFrame_homogeneous t _)] using he

theorem spectatorRotation_finite_dual_cross (t : ℕ)
    (F G : Core (Fin 2) ℂ →ₗ[ℂ] ℂ) :
    ∑ n : DegreeIndex t, star (F (rotateSpectatorPolynomial (degreeFrame t n))) *
      G (rotateSpectatorPolynomial (degreeFrame t n)) =
    ∑ n : DegreeIndex t, star (F (degreeFrame t n))*G (degreeFrame t n) :=
  secondQuantization_finite_dual_cross spectatorRotation t F G


/-- The complete degree index has the original ordered spectator labels
(j,t-j); equal labels are retained. -/
def degreeIndexEquiv (t : ℕ) : DegreeIndex t ≃ Fin (t+1) where
  toFun n := ⟨n.val 0, by
    have h : n.val 0+n.val 1=t := by
      simpa only [Finsupp.degree_eq_sum,Fin.sum_univ_two] using n.property
    omega⟩
  invFun j := ⟨Finsupp.single 0 j.val + Finsupp.single 1 (t-j.val), by
    simp only [map_add,Finsupp.degree_single]
    omega⟩
  left_inv n := by
    apply Subtype.ext
    ext i
    have h : n.val 0+n.val 1=t := by
      simpa only [Finsupp.degree_eq_sum,Fin.sum_univ_two] using n.property
    fin_cases i <;> simp only [Finsupp.add_apply,Finsupp.single_apply] <;> norm_num <;> omega
  right_inv j := by
    apply Fin.ext
    simp

/-- Literal normalized canonical spectator monomial. -/
def normalizedSpectatorWord (j m : ℕ) : Core (Fin 2) ℂ :=
  (TorusLean.BosonFiniteCertificate.factorialRootNat j *
    TorusLean.BosonFiniteCertificate.factorialRootNat m)⁻¹ •
      ((MvPolynomial.X 0)^j * (MvPolynomial.X 1)^m)

theorem degreeFrame_eq_spectatorWord (t : ℕ) (n : DegreeIndex t) :
    degreeFrame t n = normalizedSpectatorWord (n.val 0) (n.val 1) := by
  have hn : n.val=Finsupp.single 0 (n.val 0)+Finsupp.single 1 (n.val 1) := by
    ext i
    fin_cases i <;> simp
  have hr : frameRoot n.val =
      TorusLean.BosonFiniteCertificate.factorialRootNat (n.val 0) *
        TorusLean.BosonFiniteCertificate.factorialRootNat (n.val 1) := by
    simp only [frameRoot,occupationMetricWeight,Fin.prod_univ_two,one_pow,mul_one,
      Nat.cast_mul,TorusLean.BosonFiniteCertificate.factorialRootNat]
    rw [Real.sqrt_mul (by positivity),Complex.ofReal_mul]
  simp only [degreeFrame,normalizedSpectatorWord,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial,mul_one,MvPolynomial.smul_monomial,
    smul_eq_mul,hr]
  exact congrArg (fun k : Fin 2 →₀ ℕ => MvPolynomial.monomial k
    (TorusLean.BosonFiniteCertificate.factorialRootNat (n.val 0) *
      TorusLean.BosonFiniteCertificate.factorialRootNat (n.val 1))⁻¹) hn

/-- The actual spectator rotation preserves the complete original finite
ordered degree-t cross sum. No matrix of guessed binomial coefficients is used. -/
theorem spectatorRotation_ordered_cross (t : ℕ)
    (F G : Core (Fin 2) ℂ →ₗ[ℂ] ℂ) :
    ∑ j : Fin (t+1), star (F (rotateSpectatorPolynomial
      (normalizedSpectatorWord j.val (t-j.val)))) *
      G (rotateSpectatorPolynomial (normalizedSpectatorWord j.val (t-j.val))) =
    ∑ j : Fin (t+1), star (F (normalizedSpectatorWord j.val (t-j.val))) *
      G (normalizedSpectatorWord j.val (t-j.val)) := by
  classical
  have h := spectatorRotation_finite_dual_cross t F G
  simp_rw [degreeFrame_eq_spectatorWord] at h
  have hsum (H : ℕ → ℕ → ℂ) :
      (∑ j : Fin (t+1), H j.val (t-j.val)) =
        ∑ n : DegreeIndex t, H (n.val 0) (n.val 1) := by
    simpa [degreeIndexEquiv] using
      (Equiv.sum_comp (degreeIndexEquiv t).symm
        (fun n : DegreeIndex t => H (n.val 0) (n.val 1)))
  rw [hsum (fun j m => star (F (rotateSpectatorPolynomial (normalizedSpectatorWord j m))) *
    G (rotateSpectatorPolynomial (normalizedSpectatorWord j m))),
    hsum (fun j m => star (F (normalizedSpectatorWord j m))*G (normalizedSpectatorWord j m))]
  exact h

end TorusLean.Shared.ThermalCoherentJacobiFourParseval
