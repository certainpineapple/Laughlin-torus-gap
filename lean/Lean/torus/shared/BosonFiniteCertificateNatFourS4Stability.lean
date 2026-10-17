import torus.shared.BosonFiniteCertificateNatFourS4Words
import torus.shared.BosonFiniteCertificateNatFourCOMDegree
import torus.shared.BosonFiniteCertificateNatFourDegreeSparse

/-! On the full true four-particle sector the independent double-pair source
is a locally finite sum: every off-degree complete annihilation is zero.
Consequently its monomial construction agrees with every sufficiently large
genuine pair cutoff. No finite certificate table is used here. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem natFourDoublePairRemoval_wrong_degree (p q : ℕ) (s : List ℕ)
    (hs : s.length=4) (hd : p+q ≠ s.sum) :
    natFourDoublePairRemoval p q s=0 := by
  unfold natFourDoublePairRemoval
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
  have hpa : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  have hqb : b ≤ q := Nat.le_of_lt_succ (List.mem_range.mp hb)
  apply natFour_removal_degree_zero s [a,p-a,b,q-b] hs rfl
  simpa only [List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc] using
    (show a+(p-a)+(b+(q-b)) ≠ s.sum by omega)

theorem canonicalNatFourDoublePair_wrong_degree (p q d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hf : f.IsWeightedHomogeneous id d) (hd : p+q ≠ d) :
    canonicalNatFourDoublePair p q f=0 := by
  have hspan : natFourDegreeWordSpan d ≤ (canonicalNatFourDoublePair p q).ker := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hs,hsd,rfl⟩
    change canonicalNatFourDoublePair p q (scaledWord factorialRootNat s)=0
    rw [canonicalNatFourDoublePair_word p q s hs,
      natFourDoublePairRemoval_wrong_degree p q s hs (by rwa [hsd])]
    simp
  exact hspan (homogeneous_mem_natFourDegreeWordSpan d f hN hf)

def canonicalNatFourS4Shell (d : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ((List.range (d+1)).map fun p => (natFourPairWeight p (d-p) : ℂ) •
    (canonicalNatFourDoubleCreator p (d-p)).comp
      (canonicalNatFourDoublePair p (d-p))).sum

theorem canonicalNatFourS4Cutoff_succ (D : ℕ) :
    canonicalNatFourS4Cutoff (D+1)=
      canonicalNatFourS4Cutoff D+canonicalNatFourS4Shell (D+1) := by
  unfold canonicalNatFourS4Cutoff natFourPairSlots
  rw [List.range_succ,List.flatMap_append,List.map_append,List.sum_append]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map,
    Function.comp_def,canonicalNatFourS4Shell]

theorem canonicalNatFourS4Shell_wrong_degree (d e : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hf : f.IsWeightedHomogeneous id d) (he : e ≠ d) :
    canonicalNatFourS4Shell e f=0 := by
  rw [canonicalNatFourS4Shell,nat_linear_list_sum_apply]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
  have hpe : p ≤ e := Nat.le_of_lt_succ (List.mem_range.mp hp)
  simp only [LinearMap.smul_apply,LinearMap.comp_apply]
  rw [canonicalNatFourDoublePair_wrong_degree p (e-p) d f hN hf (by omega)]
  simp

theorem canonicalNatFourS4Cutoff_stable_four (d D : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hf : f.IsWeightedHomogeneous id d) (hD : d ≤ D) :
    canonicalNatFourS4Cutoff D f=canonicalNatFourS4Cutoff d f := by
  induction D,hD using Nat.le_induction with
  | base => rfl
  | succ D hD ih =>
    rw [canonicalNatFourS4Cutoff_succ,LinearMap.add_apply,ih,
      canonicalNatFourS4Shell_wrong_degree d (D+1) f hN hf (by omega),add_zero]

theorem canonicalNatFourS4_eq_any_cutoff_four (d D : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hf : f.IsWeightedHomogeneous id d) (hD : d ≤ D) :
    canonicalNatFourS4 f=canonicalNatFourS4Cutoff D f := by
  rw [canonicalNatFourS4_eq_cutoff_weighted d f hf,
    canonicalNatFourS4Cutoff_stable_four d D f hN hf hD]

theorem canonicalNatFourS4Cutoff_below_degree (D d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hf : f.IsWeightedHomogeneous id d) (hD : D<d) :
    canonicalNatFourS4Cutoff D f=0 := by
  rw [canonicalNatFourS4Cutoff,nat_linear_list_sum_apply]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨pq,hpq,rfl⟩ := List.mem_map.mp hz
  obtain ⟨e,he,hpq⟩ := List.mem_flatMap.mp hpq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hpq
  have heD : e ≤ D := Nat.le_of_lt_succ (List.mem_range.mp he)
  have hpe : p ≤ e := Nat.le_of_lt_succ (List.mem_range.mp hp)
  simp only [LinearMap.smul_apply,LinearMap.comp_apply]
  rw [canonicalNatFourDoublePair_wrong_degree p (e-p) d f hN hf (by omega)]
  simp

theorem canonicalNatFourS4_eq_shell_four (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hf : f.IsWeightedHomogeneous id d) :
    canonicalNatFourS4 f=canonicalNatFourS4Shell d f := by
  rw [canonicalNatFourS4_eq_cutoff_weighted d f hf]
  cases d with
  | zero => rfl
  | succ d =>
    rw [canonicalNatFourS4Cutoff_succ,LinearMap.add_apply,
      canonicalNatFourS4Cutoff_below_degree d (d+1) f hN hf (by omega),zero_add]

theorem canonicalNatFourS4Shell_form (d : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner f (canonicalNatFourS4Shell d g)=
      ((List.range (d+1)).map fun p => (natFourPairWeight p (d-p) : ℂ)*
        natOccupationInner (canonicalNatFourDoublePair p (d-p) f)
          (canonicalNatFourDoublePair p (d-p) g)).sum := by
  simp only [canonicalNatFourS4Shell,nat_linear_list_sum_apply,
    natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,natOccupationInner_smul_right,
    canonicalNatFourDoubleCreator_right_adjoint]

#print axioms natFourDoublePairRemoval_wrong_degree
#print axioms canonicalNatFourDoublePair_wrong_degree
#print axioms canonicalNatFourS4Cutoff_succ
#print axioms canonicalNatFourS4Shell_wrong_degree
#print axioms canonicalNatFourS4Cutoff_stable_four
#print axioms canonicalNatFourS4_eq_any_cutoff_four
#print axioms canonicalNatFourS4Cutoff_below_degree
#print axioms canonicalNatFourS4_eq_shell_four
#print axioms canonicalNatFourS4Shell_form
end TorusLean.BosonFiniteCertificate
