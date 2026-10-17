import torus.shared.BosonFiniteCertificateNatFourDescendants414AverageData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_bounded_average (a : Fin 8) (b : Fin 8) :
    (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) a b=(b414average) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 0 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 1 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 2 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 3 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 4 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 5 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 6 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (∑ k ∈ Finset.range 3, natFourOriginalCOMWeight k • f414descForms k) 7 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414average) 7 j) (by decide +kernel)
    exact h 0 b

#print axioms f414_bounded_average

end TorusLean.BosonFiniteCertificate
