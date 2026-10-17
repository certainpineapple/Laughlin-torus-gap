import torus.shared.BosonFiniteCertificateNatFourHWords

/-! Source-derived sparse evaluation of the genuine single-pair form.
Only actual zero annihilation amplitudes are discarded. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords

def natFourPairWordFormSparse (p : ℕ) (s u : List ℕ) : ℚ :=
  ((List.range (p+1)).map fun a =>
    if wordRemovalWeight s [a,p-a]=0 then 0 else
    ((List.range (p+1)).map fun b =>
      if wordRemovalWeight u [b,p-b]=0 then 0 else
      if (eraseWord s [a,p-a]).Perm (eraseWord u [b,p-b]) then
        (wordRemovalWeight s [a,p-a] : ℚ)*(natFourComputableMetric (eraseWord s [a,p-a]) : ℚ)*
          (wordRemovalWeight u [b,p-b] : ℚ) else 0).sum).sum

theorem natFourPairWordFormSparse_eq (p : ℕ) (s u : List ℕ) :
    natFourPairWordFormSparse p s u=natFourPairWordForm p s u := by
  unfold natFourPairWordFormSparse natFourPairWordForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  by_cases hsa : wordRemovalWeight s [a,p-a]=0
  · simp [hsa]
  · rw [if_neg hsa]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    by_cases hbu : wordRemovalWeight u [b,p-b]=0
    · simp [hbu]
    · rw [if_neg hbu]

def natFourHWordFormSparse (D : ℕ) (s u : List ℕ) : ℚ :=
  ((List.range (D+1)).map fun p =>
    ((p.factorial : ℚ)/2^(p+1))*natFourPairWordFormSparse p s u).sum

theorem natFourHWordFormSparse_eq (D : ℕ) (s u : List ℕ) :
    natFourHWordFormSparse D s u=natFourHWordForm D s u := by
  simp only [natFourHWordFormSparse,natFourHWordForm,natFourPairWordFormSparse_eq]

#print axioms natFourPairWordFormSparse_eq
#print axioms natFourHWordFormSparse_eq
end TorusLean.BosonFiniteCertificate
