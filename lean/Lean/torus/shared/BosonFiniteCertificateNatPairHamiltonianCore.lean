import torus.shared.BosonFiniteCertificateNatCOM
import torus.shared.BosonFiniteCertificateRescaleCCR

/-! The original planar pair operator on arbitrary natural orbital labels.
Pair annihilators and creators are actual differential/multiplication sums.
The global Hamiltonian is their locally finite sum, defined on each occupation
monomial through its true orbital degree and extended linearly. No Fin9
Hamiltonian, compression matrix, or target restriction is used to define it. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateRescaleCCR
open scoped BigOperators

def pairCoefficientNat (p a : ℕ) : ℂ :=
  (factorialRootNat a * factorialRootNat (p-a))⁻¹

theorem pairCoefficientNat_real (p a : ℕ) : star (pairCoefficientNat p a)=pairCoefficientNat p a := by
  simp [pairCoefficientNat,factorialRootNat,Complex.star_def]

def canonicalPairNat (p : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ((List.range (p+1)).map fun a =>
    pairCoefficientNat p a • (annihilate (p-a)).comp (annihilate a)).sum

def canonicalPairCreatorNat (p : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ((List.range (p+1)).map fun a =>
    pairCoefficientNat p a • (create a).comp (create (p-a))).sum

theorem nat_linear_list_sum_apply {J : Type*} (l : List J)
    (A : J → Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ) (f : Core ℕ ℂ) :
    (l.map A).sum f = (l.map fun a => A a f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem canonicalPairNat_eq_conjugate (p : ℕ) :
    canonicalPairNat p = conjugateOperator factorialRootNat factorialRootNat_ne_zero
      (paperColumnWordOperator p none) := by
  unfold canonicalPairNat
  symm
  rw [paperColumnWordOperator,conjugateOperator_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [normalWord_pair_remove,conjugateOperator_comp,conjugateOperator_annihilate,
    LinearMap.smul_comp,LinearMap.comp_smul,smul_smul]
  simp only [pairCoefficientNat,mul_inv,mul_comm]

/-- A pair cannot remove more orbital degree than a homogeneous input has.
This proof reads the actual two-derivative coefficient, without a source table
or particle-number restriction. -/
theorem nat_pair_annihilate_above_weight (a b d : ℕ) (f : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) (hab : d<a+b) :
    annihilate b (annihilate a f)=0 := by
  ext n
  have hz : f.coeff ((n+Finsupp.single b 1)+Finsupp.single a 1)=0 := by
    by_contra hc
    have hh := hd hc
    simp only [map_add,Finsupp.weight_single,one_smul,id_eq] at hh
    omega
  change (MvPolynomial.pderiv b (MvPolynomial.pderiv a f)).coeff n=0
  simp only [MvPolynomial.coeff_pderiv,hz,mul_zero,zero_mul]

theorem canonicalPairNat_high_degree_zero (p d : ℕ) (f : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) (hp : d<p) : canonicalPairNat p f=0 := by
  rw [canonicalPairNat,nat_linear_list_sum_apply]
  have hh : ((List.range (p+1)).map fun a =>
      (pairCoefficientNat p a • (annihilate (p-a)).comp (annihilate a)) f) =
      (List.range (p+1)).map (fun _ => (0 : Core ℕ ℂ)) := by
    apply List.map_congr_left
    intro a ha
    have ha' := Nat.le_of_lt_succ (List.mem_range.mp ha)
    simp only [LinearMap.smul_apply,LinearMap.comp_apply,
      nat_pair_annihilate_above_weight a (p-a) d f hd (by omega),smul_zero]
  rw [hh]
  simp

def canonicalPairHamiltonianNatCutoff (D : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ((List.range (D+1)).map fun p =>
    ((p.factorial:ℂ)/(2:ℂ)^(p+1)) •
      (canonicalPairCreatorNat p).comp (canonicalPairNat p)).sum

theorem canonicalPairHamiltonianNatCutoff_succ (D : ℕ) :
    canonicalPairHamiltonianNatCutoff (D+1) = canonicalPairHamiltonianNatCutoff D +
      (((D+1).factorial:ℂ)/(2:ℂ)^((D+1)+1)) •
        (canonicalPairCreatorNat (D+1)).comp (canonicalPairNat (D+1)) :=
  List.sum_range_succ _ (D+1)

theorem canonicalPairHamiltonianNatCutoff_stable (d D : ℕ) (hD : d≤D)
    (f : Core ℕ ℂ) (hd : f.IsWeightedHomogeneous id d) :
    canonicalPairHamiltonianNatCutoff D f=canonicalPairHamiltonianNatCutoff d f := by
  induction D,hD using Nat.le_induction with
  | base => rfl
  | succ D hD ih =>
    rw [canonicalPairHamiltonianNatCutoff_succ,LinearMap.add_apply,ih,
      LinearMap.smul_apply,LinearMap.comp_apply,
      canonicalPairNat_high_degree_zero (D+1) d f hd (by omega),map_zero,smul_zero,add_zero]

/-- Genuine locally finite all-core planar pair Hamiltonian. The coefficient
linear equivalence is just the polynomial's finite monomial expansion. -/
def canonicalPairHamiltonianNat : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (Finsupp.lsum ℂ (fun n : ℕ →₀ ℕ =>
    (canonicalPairHamiltonianNatCutoff (Finsupp.weight id n)).comp (MvPolynomial.monomial n))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem canonicalPairHamiltonianNat_monomial (n : ℕ →₀ ℕ) (c : ℂ) :
    canonicalPairHamiltonianNat (MvPolynomial.monomial n c) =
      canonicalPairHamiltonianNatCutoff (Finsupp.weight id n) (MvPolynomial.monomial n c) := by
  change (Finsupp.lsum ℂ (fun m : ℕ →₀ ℕ =>
    (canonicalPairHamiltonianNatCutoff (Finsupp.weight id m)).comp (MvPolynomial.monomial m)))
      (Finsupp.single n c) = _
  rw [Finsupp.lsum_single]
  rfl

theorem canonicalPairHamiltonianNat_eq_cutoff_weighted (d : ℕ) (f : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) :
    canonicalPairHamiltonianNat f=canonicalPairHamiltonianNatCutoff d f := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [canonicalPairHamiltonianNat_monomial,hd (MvPolynomial.mem_support_iff.mp hn)]

/-- Any finite bound on the actual input support gives the same Hamiltonian;
the choice used in its definition therefore does not truncate the operator. -/
theorem canonicalPairHamiltonianNat_eq_cutoff_support (D : ℕ) (f : Core ℕ ℂ)
    (hD : ∀ n ∈ f.support, Finsupp.weight id n≤D) :
    canonicalPairHamiltonianNat f=canonicalPairHamiltonianNatCutoff D f := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [canonicalPairHamiltonianNat_monomial]
  exact (canonicalPairHamiltonianNatCutoff_stable (Finsupp.weight id n) D (hD n hn) _
    (MvPolynomial.isWeightedHomogeneous_monomial id n _ rfl)).symm

#print axioms canonicalPairNat_eq_conjugate
#print axioms canonicalPairNat_high_degree_zero
#print axioms canonicalPairHamiltonianNat_eq_cutoff_weighted
#print axioms canonicalPairHamiltonianNat_eq_cutoff_support
end TorusLean.BosonFiniteCertificate
