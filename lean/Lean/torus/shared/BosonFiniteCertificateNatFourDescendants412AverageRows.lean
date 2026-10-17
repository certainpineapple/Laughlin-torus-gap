import torus.shared.BosonFiniteCertificateNatFourDescendants412AverageData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412_bounded_average (a : Fin 7) (b : Fin 7) :
    (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) a b=(b412average) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b412average) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b412average) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b412average) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b412average) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b412average) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b412average) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 5, natFourOriginalCOMWeight k • f412descForms k) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b412average) 6 j) (by decide +kernel)
    exact h 0 b

#print axioms f412_bounded_average

end TorusLean.BosonFiniteCertificate
