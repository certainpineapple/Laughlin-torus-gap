import torus.shared.BosonFiniteCertificateNatFourDualPrefixSparse

/-! Exact complete-word factorization of the original normal coefficient.
The physical left factorial metric cancels the original adjoint denominator;
the original integer-row denominator remains exactly ten to the twenty-four.
No numerical target matrix occurs in these identities. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem natFour_removal_success_perm (s labels : List ℕ)
    (h : wordRemovalWeight s labels ≠ 0) : s.Perm (labels++eraseWord s labels) := by
  induction labels generalizing s with
  | nil => simp [eraseWord]
  | cons j labels ih =>
    have hh : s.count j≠0 ∧ wordRemovalWeight (s.erase j) labels≠0 := mul_ne_zero_iff.mp h
    have hm : j ∈ s := List.count_pos_iff.mp (Nat.pos_of_ne_zero hh.1)
    exact (List.perm_cons_erase hm).trans ((ih (s.erase j) hh.2).cons j)

theorem natFour_removal_zero_of_not_perm (s labels : List ℕ)
    (hlen : s.length=labels.length) (hp : ¬ s.Perm labels) :
    wordRemovalWeight s labels=0 := by
  by_contra hz
  have he : eraseWord s labels=[] := List.eq_nil_of_length_eq_zero (by
    have hh := eraseWord_length_add s labels hz
    omega)
  exact hp (by simpa only [he,List.append_nil] using natFour_removal_success_perm s labels hz)

theorem natFourComputableMetric_perm (s u : List ℕ) (h : s.Perm u) :
    natFourComputableMetric s=natFourComputableMetric u := by
  have ho := natFourOccupation_eq_iff_perm s u |>.mpr h
  have hp := (h.map Nat.factorial).prod_eq
  simp only [natFourComputableMetric,natFourMultiplicity_eq_weight,ho,hp]

theorem natFourComputableNormalForm_complete (s u creators annihilators : List ℕ)
    (hs : s.length=creators.length) (hu : u.length=annihilators.length) :
    natFourComputableNormalForm s u creators annihilators=
      (wordRemovalWeight s creators : ℚ)*(wordRemovalWeight u annihilators : ℚ)*
        ((creators.map Nat.factorial).prod : ℚ) := by
  by_cases hz : wordRemovalWeight u annihilators=0
  · simp [natFourComputableNormalForm,hz]
  · have he : eraseWord u annihilators=[] := List.eq_nil_of_length_eq_zero (by
      have hh := eraseWord_length_add u annihilators hz
      omega)
    simp only [natFourComputableNormalForm,he,List.append_nil]
    by_cases hp : s.Perm creators
    · rw [if_pos hp,natFourComputableMetric_perm s creators hp,
        natFour_removal_input_perm s creators creators hp,natFour_removal_self]
      simp only [natFourComputableMetric,Nat.cast_mul]
      ring
    · rw [if_neg hp,natFour_removal_zero_of_not_perm s creators hs hp]
      simp

theorem natFour_original_term_complete_factor (t p j p' j' a b : ℕ) (s u : List ℕ)
    (hs : s.length=4) (hu : u.length=4) :
    natFourOriginalCoefficient t p j a 1 1 *
      natFourNormalWordForm s u [a,p-a,j,p'+j'-t] [p+j-t,j',b,p'-b] =
    ((p+j-t).factorial : ℚ)*((p'+j'-t).factorial : ℚ)*
      (wordRemovalWeight s [a,p-a,j,p'+j'-t] : ℚ)*
      (wordRemovalWeight u [p+j-t,j',b,p'-b] : ℚ)/1000000000000000000000000 := by
  rw [← natFourComputableNormalForm_eq,natFourComputableNormalForm_complete s u [a,p-a,j,p'+j'-t] [p+j-t,j',b,p'-b] hs hu]
  simp only [natFourOriginalCoefficient,natFourDecodedRowEntry,Int.cast_one,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Nat.cast_mul,mul_one]
  have ha : (a.factorial : ℚ)≠0 := by positivity
  have hp : ((p-a).factorial : ℚ)≠0 := by positivity
  have hj : (j.factorial : ℚ)≠0 := by positivity
  field_simp [ha,hp,hj]
  <;> ring

#print axioms natFour_removal_success_perm
#print axioms natFour_removal_zero_of_not_perm
#print axioms natFourComputableMetric_perm
#print axioms natFourComputableNormalForm_complete
#print axioms natFour_original_term_complete_factor
end TorusLean.BosonFiniteCertificate
