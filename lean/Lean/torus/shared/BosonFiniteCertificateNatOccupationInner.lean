import torus.boson.PolynomialInnerAdjoint
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Genuine occupation inner product on arbitrary natural orbital labels

The polynomial domain has finite support in both its occupation monomials and
in the orbital labels of each monomial. No global `Fintype ℕ` or orbital cutoff
is introduced. The actual multiplicity factorial weight makes multiplication
by `X j` adjoint to formal differentiation at every natural orbital label.
Injective renaming from any finite orbital set preserves the canonical
occupation inner product. This is an algebraic common-domain result, not a
construction of a completed infinite Fock space or an operator closure.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open scoped BigOperators ComplexConjugate
open TorusLean.Boson

/-- Product of the actual occupation multiplicity factorials, over finite support. -/
def natOccupationWeight (n : ℕ →₀ ℕ) : ℕ :=
  n.prod fun _ a => a.factorial

theorem natOccupationWeight_pos (n : ℕ →₀ ℕ) : 0 < natOccupationWeight n := by
  unfold natOccupationWeight Finsupp.prod
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

theorem natOccupationWeight_add_single (n : ℕ →₀ ℕ) (i : ℕ) :
    natOccupationWeight (n + Finsupp.single i 1) =
      (n i + 1) * natOccupationWeight n := by
  classical
  have he : Finsupp.erase i (n + Finsupp.single i 1) = Finsupp.erase i n := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  have hprod (m : ℕ →₀ ℕ) :
      (m i).factorial * (m.erase i).prod (fun (_ : ℕ) (a : ℕ) => a.factorial) =
        natOccupationWeight m :=
    Finsupp.mul_prod_erase' m i (fun (_ : ℕ) (a : ℕ) => a.factorial) (fun _ => rfl)
  rw [← hprod (n + Finsupp.single i 1), ← hprod n, he]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, mul_assoc]

/-- The genuine finite-support occupation form, conjugate-linear in the first input. -/
def natOccupationInner (f g : Core ℕ ℂ) : ℂ :=
  f.coeff.sum fun n c => (natOccupationWeight n : ℂ) * star c * g.coeff n

theorem natOccupationInner_monomial_left (n : ℕ →₀ ℕ) (c : ℂ) (g : Core ℕ ℂ) :
    natOccupationInner (MvPolynomial.monomial n c) g =
      (natOccupationWeight n : ℂ) * star c * g.coeff n := by
  simp [natOccupationInner]

theorem natOccupationInner_zero_left (g : Core ℕ ℂ) : natOccupationInner 0 g = 0 := by
  simp [natOccupationInner]

theorem natOccupationInner_zero_right (f : Core ℕ ℂ) : natOccupationInner f 0 = 0 := by
  simp [natOccupationInner]

theorem natOccupationInner_add_left (f g h : Core ℕ ℂ) :
    natOccupationInner (f + g) h = natOccupationInner f h + natOccupationInner g h := by
  unfold natOccupationInner
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index'
  · intro n
    simp
  · intro n c d
    simp [star_add, mul_add, add_mul]

theorem natOccupationInner_add_right (f g h : Core ℕ ℂ) :
    natOccupationInner f (g + h) = natOccupationInner f g + natOccupationInner f h := by
  simp [natOccupationInner, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]

theorem natOccupationInner_smul_left (c : ℂ) (f g : Core ℕ ℂ) :
    natOccupationInner (c • f) g = star c * natOccupationInner f g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial n d =>
    simp [MvPolynomial.smul_monomial, natOccupationInner_monomial_left,
      smul_eq_mul, star_mul, mul_assoc, mul_comm, mul_left_comm]
  | add f h hf hh =>
    simp [smul_add, natOccupationInner_add_left, hf, hh, mul_add]

theorem natOccupationInner_smul_right (c : ℂ) (f g : Core ℕ ℂ) :
    natOccupationInner f (c • g) = c * natOccupationInner f g := by
  unfold natOccupationInner
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem natOccupationInner_sum_left {α : Type*} (s : Finset α)
    (f : α → Core ℕ ℂ) (g : Core ℕ ℂ) :
    natOccupationInner (∑ a ∈ s, f a) g = ∑ a ∈ s, natOccupationInner (f a) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [natOccupationInner_zero_left]
  | @insert a s ha ih => simp [ha, natOccupationInner_add_left, ih]

theorem natOccupationInner_sum_right {α : Type*} (s : Finset α)
    (f : Core ℕ ℂ) (g : α → Core ℕ ℂ) :
    natOccupationInner f (∑ a ∈ s, g a) = ∑ a ∈ s, natOccupationInner f (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [natOccupationInner_zero_right]
  | @insert a s ha ih => simp [ha, natOccupationInner_add_right, ih]

theorem natOccupationInner_list_sum_left {α : Type*} (s : List α)
    (f : α → Core ℕ ℂ) (g : Core ℕ ℂ) :
    natOccupationInner ((s.map f).sum) g =
      (s.map fun a => natOccupationInner (f a) g).sum := by
  induction s with
  | nil => simp [natOccupationInner_zero_left]
  | cons a s ih => simp [natOccupationInner_add_left, ih]

theorem natOccupationInner_list_sum_right {α : Type*} (s : List α)
    (f : Core ℕ ℂ) (g : α → Core ℕ ℂ) :
    natOccupationInner f ((s.map g).sum) =
      (s.map fun a => natOccupationInner f (g a)).sum := by
  induction s with
  | nil => simp [natOccupationInner_zero_right]
  | cons a s ih => simp [natOccupationInner_add_right, ih]

theorem natOccupationInner_conj_symm (f g : Core ℕ ℂ) :
    star (natOccupationInner f g) = natOccupationInner g f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f h hf hh =>
    simp [natOccupationInner_add_left, natOccupationInner_add_right, star_add, hf, hh]
  | monomial n c =>
    induction g using MvPolynomial.induction_on' with
    | add g h hg hh =>
      simp [natOccupationInner_add_left, natOccupationInner_add_right, star_add, hg, hh]
    | monomial m d =>
      by_cases h : n = m
      · subst m
        simp [natOccupationInner_monomial_left, MvPolynomial.coeff_monomial,
          star_mul, mul_assoc, mul_comm, mul_left_comm]
      · simp [natOccupationInner_monomial_left, MvPolynomial.coeff_monomial, h, Ne.symm h]

def natOccupationNormSq (f : Core ℕ ℂ) : ℝ :=
  ∑ n ∈ f.support, (natOccupationWeight n : ℝ) * Complex.normSq (f.coeff n)

theorem natOccupationNormSq_nonneg (f : Core ℕ ℂ) : 0 ≤ natOccupationNormSq f := by
  unfold natOccupationNormSq
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem natOccupationInner_self (f : Core ℕ ℂ) :
    natOccupationInner f f = (natOccupationNormSq f : ℂ) := by
  classical
  unfold natOccupationInner natOccupationNormSq
  simp only [Finsupp.sum, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_assoc,
    MvPolynomial.finsupp_support_eq_support]

theorem natOccupationInner_self_re (f : Core ℕ ℂ) :
    (natOccupationInner f f).re = natOccupationNormSq f := by
  rw [natOccupationInner_self]
  simp

theorem natOccupationInner_self_nonneg (f : Core ℕ ℂ) :
    0 ≤ (natOccupationInner f f).re := by
  rw [natOccupationInner_self_re]
  exact natOccupationNormSq_nonneg f

theorem natOccupationNormSq_pos (f : Core ℕ ℂ) (hf : f ≠ 0) :
    0 < natOccupationNormSq f := by
  classical
  unfold natOccupationNormSq
  apply Finset.sum_pos
  · intro n hn
    exact mul_pos (Nat.cast_pos.mpr (natOccupationWeight_pos n))
      (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hn))
  · exact MvPolynomial.support_nonempty.mpr hf

theorem natOccupationInner_self_eq_zero_iff (f : Core ℕ ℂ) :
    natOccupationInner f f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    have hz : natOccupationNormSq f = 0 := by
      have hr := congrArg Complex.re h
      simpa only [natOccupationInner_self_re, Complex.zero_re] using hr
    exact (ne_of_gt (natOccupationNormSq_pos f hf)) hz
  · intro h
    subst f
    exact natOccupationInner_zero_left 0

/-- Actual creation and annihilation are adjoint at every natural label. -/
theorem nat_create_adjoint (i : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner (create i f) g = natOccupationInner f (annihilate i g) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f h hf hh =>
    simp [map_add, natOccupationInner_add_left, hf, hh]
  | monomial n c =>
    have hc : create i (MvPolynomial.monomial n c) =
        MvPolynomial.monomial (n + Finsupp.single i 1) c := by
      simp [create, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, add_comm]
    rw [hc, natOccupationInner_monomial_left, natOccupationInner_monomial_left]
    have hcoef : (annihilate i g).coeff n =
        g.coeff (n + Finsupp.single i 1) * ((n i : ℂ) + 1) := by
      simpa [annihilate, Nat.cast_add, Nat.cast_one] using (MvPolynomial.coeff_pderiv g n)
    rw [hcoef, natOccupationWeight_add_single]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem nat_annihilate_adjoint (i : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner (annihilate i f) g = natOccupationInner f (create i g) := by
  have h := congrArg star (nat_create_adjoint i g f)
  simpa only [natOccupationInner_conj_symm] using h.symm

/-- Injective finite-mode relabeling preserves the actual occupation weight. -/
theorem natOccupationWeight_mapDomain {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (he : Function.Injective e) (n : ι →₀ ℕ) :
    natOccupationWeight (n.mapDomain e) = occupationMetricWeight (fun _ => 1) n := by
  unfold natOccupationWeight occupationMetricWeight
  rw [Finsupp.prod_mapDomain_index_inj he, Finsupp.prod_fintype]
  · simp
  · intro i
    rfl

/-- Equality with the existing scale-one finite-mode form under genuine injective rename. -/
theorem natOccupationInner_rename {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (he : Function.Injective e) (f g : Core ι ℂ) :
    natOccupationInner (MvPolynomial.rename e f) (MvPolynomial.rename e g) =
      occupationInner (fun _ => 1) f g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f h hf hh =>
    simp only [map_add, natOccupationInner_add_left, occupationInner_add_left, hf, hh]
  | monomial n c =>
    rw [MvPolynomial.rename_monomial, natOccupationInner_monomial_left,
      occupationInner_monomial_left, natOccupationWeight_mapDomain e he,
      MvPolynomial.coeff_rename_mapDomain e he]

theorem natOccupationInner_rename_fin9 (f g : Core (Fin 9) ℂ) :
    natOccupationInner (MvPolynomial.rename Fin.val f) (MvPolynomial.rename Fin.val g) =
      occupationInner (fun _ => 1) f g :=
  natOccupationInner_rename Fin.val Fin.val_injective f g

#print axioms natOccupationWeight_pos
#print axioms natOccupationWeight_add_single
#print axioms natOccupationInner_conj_symm
#print axioms natOccupationInner_self_eq_zero_iff
#print axioms nat_create_adjoint
#print axioms nat_annihilate_adjoint
#print axioms natOccupationInner_rename
#print axioms natOccupationInner_rename_fin9
end TorusLean.BosonFiniteCertificate
