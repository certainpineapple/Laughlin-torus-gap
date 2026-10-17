import torus.shared.BosonFiniteCertificateNatPairHamiltonianCore
import torus.shared.BosonFiniteCertificateNatCOMCompatibility
import torus.shared.BosonFiniteCertificateCanonicalPairAdjoint

/-! True operator restriction of the locally finite Nat planar Hamiltonian.
The finite H8 is not its definition. Injective rename is used only after the
pair labels are explicitly bounded, and the full sum is reduced by proved
annihilator support. The restriction holds for every particle number at
orbital degree at most eight. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

theorem pairCoefficientNat_eq_nine (p a : ℕ) (hp : p<9) (ha : a≤p) :
    pairCoefficientNat p a=pairCoefficient9 p a := by
  simp only [pairCoefficientNat,pairCoefficient9,factorialRootNat,pairFactorialRoot9,
    fin9,Nat.mod_eq_of_lt (show a<9 by omega),Nat.mod_eq_of_lt (show p-a<9 by omega)]

theorem nat_create_rename_fin9 (a : ℕ) (ha : a<9) (f : Core (Fin 9) ℂ) :
    create a (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (create (fin9 a) f) := by
  change MvPolynomial.X a * MvPolynomial.rename Fin.val f =
    MvPolynomial.rename Fin.val (MvPolynomial.X (fin9 a)*f)
  rw [map_mul,MvPolynomial.rename_X]
  simp only [fin9,Nat.mod_eq_of_lt ha]

theorem nat_annihilate_rename_fin9 (a : ℕ) (ha : a<9) (f : Core (Fin 9) ℂ) :
    annihilate a (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (annihilate (fin9 a) f) := by
  have h := annihilateWord_rename Fin.val Fin.val_injective [fin9 a] f
  simpa only [List.map_cons,List.map_nil,annihilateWord,
    LinearMap.comp_apply,LinearMap.id_apply,fin9,Nat.mod_eq_of_lt ha] using h

theorem canonicalPairNat_rename (p : ℕ) (hp : p<9) (f : Core (Fin 9) ℂ) :
    canonicalPairNat p (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (canonicalPair9 p f) := by
  rw [canonicalPairNat,nat_linear_list_sum_apply,canonicalPair9_eq_differential,
    linear_list_sum_apply,map_list_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have ha' := Nat.le_of_lt_succ (List.mem_range.mp ha)
  simp only [Function.comp_def,LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
  rw [nat_annihilate_rename_fin9 a (by omega),
    nat_annihilate_rename_fin9 (p-a) (by omega),pairCoefficientNat_eq_nine p a hp ha']

theorem canonicalPairCreatorNat_rename (p : ℕ) (hp : p<9) (f : Core (Fin 9) ℂ) :
    canonicalPairCreatorNat p (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (canonicalPairCreator9 p f) := by
  rw [canonicalPairCreatorNat,nat_linear_list_sum_apply,canonicalPairCreator9,
    linear_list_sum_apply,map_list_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have ha' := Nat.le_of_lt_succ (List.mem_range.mp ha)
  simp only [Function.comp_def,LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
  rw [nat_create_rename_fin9 (p-a) (by omega),
    nat_create_rename_fin9 a (by omega),pairCoefficientNat_eq_nine p a hp ha']

theorem canonicalPairHamiltonianNatCutoff_rename (D : ℕ) (hD : D<9)
    (f : Core (Fin 9) ℂ) :
    canonicalPairHamiltonianNatCutoff D (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 D f) := by
  rw [canonicalPairHamiltonianNatCutoff,nat_linear_list_sum_apply,canonicalPairHamiltonian9,
    linear_list_sum_apply,map_list_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hp' := Nat.le_of_lt_succ (List.mem_range.mp hp)
  simp only [Function.comp_def,LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
  rw [canonicalPairNat_rename p (by omega),canonicalPairCreatorNat_rename p (by omega)]

theorem rename_weighted_homogeneous_fin9 (d : ℕ) (f : Core (Fin 9) ℂ)
    (hd : f.IsWeightedHomogeneous Fin.val d) :
    (MvPolynomial.rename Fin.val f).IsWeightedHomogeneous id d := by
  change MvPolynomial.rename Fin.val f ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ id d
  rw [← MvPolynomial.support_sum_monomial_coeff f,map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [MvPolynomial.rename_monomial]
  exact MvPolynomial.isWeightedHomogeneous_monomial id _ _
    ((nat_weight_mapDomain_fin9 n).trans (hd (MvPolynomial.mem_support_iff.mp hn)))

/-- The full locally finite Nat Hamiltonian really restricts to the genuine
finite H8. Only the input's true orbital degree is bounded. -/
theorem canonicalPairHamiltonianNat_rename_low_degree (d : ℕ) (hd8 : d≤8)
    (f : Core (Fin 9) ℂ) (hd : f.IsWeightedHomogeneous Fin.val d) :
    canonicalPairHamiltonianNat (MvPolynomial.rename Fin.val f)=
      MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 f) := by
  have hh := rename_weighted_homogeneous_fin9 d f hd
  calc
    canonicalPairHamiltonianNat (MvPolynomial.rename Fin.val f) =
        canonicalPairHamiltonianNatCutoff d (MvPolynomial.rename Fin.val f) :=
      canonicalPairHamiltonianNat_eq_cutoff_weighted d _ hh
    _ = canonicalPairHamiltonianNatCutoff 8 (MvPolynomial.rename Fin.val f) :=
      (canonicalPairHamiltonianNatCutoff_stable d 8 hd8 _ hh).symm
    _ = MvPolynomial.rename Fin.val (canonicalPairHamiltonian9 8 f) :=
      canonicalPairHamiltonianNatCutoff_rename 8 (by decide) f

#print axioms canonicalPairNat_rename
#print axioms canonicalPairCreatorNat_rename
#print axioms canonicalPairHamiltonianNat_rename_low_degree
end TorusLean.BosonFiniteCertificate
