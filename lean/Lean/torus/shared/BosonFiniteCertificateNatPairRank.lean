import torus.shared.BosonFiniteCertificateNatPairHamiltonianAdjoint
import torus.shared.BosonFiniteCertificateNatCOMTail
import torus.shared.BosonFiniteCertificateConjugationPair

/-! Actual rank-one resolution of the pair Hamiltonian on each N3 orbital
homogeneous sector. The one-particle output is proved from the original
pair derivative on every three-word generator, then extended over its true
span. There is no finite orbital bound or assumed invariant matrix block. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem natOccupationInner_X_left (j : ℕ) (f : Core ℕ ℂ) :
    natOccupationInner (MvPolynomial.X j) f=f.coeff (Finsupp.single j 1) := by
  simp [MvPolynomial.X,natOccupationInner_monomial_left,natOccupationWeight]

theorem natOccupationInner_X_self (j : ℕ) :
    natOccupationInner (MvPolynomial.X j : Core ℕ ℂ) (MvPolynomial.X j)=1 := by
  rw [natOccupationInner_X_left]
  simp [MvPolynomial.X]

theorem canonicalPairNat_word_action (p d : ℕ) (s : List ℕ)
    (hlen : s.length=3) (hsum : s.sum=d) :
    canonicalPairNat p (scaledWord factorialRootNat s)=
      (pairRemoval s p : ℂ) • scaledWord factorialRootNat [d-p] := by
  rw [canonicalPairNat_eq_conjugate,←rescaleEquiv_word factorialRootNat factorialRootNat_ne_zero,
    conjugateOperator_apply_rescale,
    paperColumnWordOperator_apply p d s none (pairColumnOutputOK_of_length_sum p d s hlen hsum),map_smul]
  have hx : (MvPolynomial.X (d-p) : Core ℕ ℂ)=wordPolynomial [d-p] := by
    simp [wordPolynomial]
  rw [hx,rescaleEquiv_word]
  simp only [columnRemoval]

/-- Genuine one-particle Parseval reduction for every N3 polynomial of degree d. -/
theorem canonicalPairNat_span_singleton_output (p d : ℕ) (f : Core ℕ ℂ)
    (hf : f ∈ threeWordDegreeSpanNat d) :
    canonicalPairNat p f =
      natOccupationInner (MvPolynomial.X (d-p)) (canonicalPairNat p f) • MvPolynomial.X (d-p) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s,hlen,hsum,rfl⟩ := hf
    rw [canonicalPairNat_word_action p d s hlen hsum]
    simp only [scaledWord,wordScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      wordPolynomial,List.prod_nil,mul_one,List.prod_cons,
      natOccupationInner_smul_right,natOccupationInner_X_self,mul_one,smul_smul]
  | zero => simp only [map_zero,natOccupationInner_zero_right,zero_smul]
  | add f g hf hg ihf ihg =>
    simpa only [map_add,natOccupationInner_add_right,add_smul] using congrArg₂ (·+·) ihf ihg
  | smul c f hf ih =>
    simpa only [map_smul,natOccupationInner_smul_right,smul_smul] using
      congrArg (fun z => c • z) ih

theorem canonicalPairNat_singleton_output (p d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    canonicalPairNat p f =
      natOccupationInner (MvPolynomial.X (d-p)) (canonicalPairNat p f) • MvPolynomial.X (d-p) :=
  canonicalPairNat_span_singleton_output p d f
    (homogeneous_mem_threeWordDegreeSpanNat d f hN hd)

def canonicalNatPairRankSeed (p j : ℕ) : Core ℕ ℂ :=
  canonicalPairCreatorNat p (MvPolynomial.X j)

theorem canonicalPairNat_rank_action (p d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    canonicalPairCreatorNat p (canonicalPairNat p f) =
      natOccupationInner (canonicalNatPairRankSeed p (d-p)) f •
        canonicalNatPairRankSeed p (d-p) := by
  rw [canonicalPairNat_singleton_output p d f hN hd,map_smul]
  simp only [canonicalNatPairRankSeed,canonicalPairCreatorNat_adjoint]

/-- The genuine locally finite Hamiltonian is a sum of actual source ranks,
not a separately defined comparison operator. -/
theorem canonicalPairHamiltonianNat_rank_action (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    canonicalPairHamiltonianNat f =
      ((List.range (d+1)).map fun p => ((p.factorial:ℂ)/(2:ℂ)^(p+1)) •
        (natOccupationInner (canonicalNatPairRankSeed p (d-p)) f •
          canonicalNatPairRankSeed p (d-p))).sum := by
  rw [canonicalPairHamiltonianNat_eq_cutoff_weighted d f hd,
    canonicalPairHamiltonianNatCutoff,nat_linear_list_sum_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,
    canonicalPairNat_rank_action p d f hN hd]

theorem canonicalPairHamiltonianNat_rank_form (d : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 3) (hd : g.IsWeightedHomogeneous id d) :
    natOccupationInner f (canonicalPairHamiltonianNat g) =
      ((List.range (d+1)).map fun p => ((p.factorial:ℂ)/(2:ℂ)^(p+1)) *
        star (natOccupationInner (canonicalNatPairRankSeed p (d-p)) f) *
          natOccupationInner (canonicalNatPairRankSeed p (d-p)) g).sum := by
  rw [canonicalPairHamiltonianNat_rank_action d g hN hd,natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [natOccupationInner_smul_right,natOccupationInner_conj_symm]
  ring

#print axioms canonicalPairNat_singleton_output
#print axioms canonicalPairHamiltonianNat_rank_action
#print axioms canonicalPairHamiltonianNat_rank_form
end TorusLean.BosonFiniteCertificate
