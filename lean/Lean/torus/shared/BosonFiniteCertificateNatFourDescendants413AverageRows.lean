import torus.shared.BosonFiniteCertificateNatFourDescendants413AverageData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_bounded_average (a : Fin 5) (b : Fin 5) :
    (∑ k ∈ Finset.range 4, natFourOriginalCOMWeight k • f413descForms k) a b=(b413average) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (∑ k ∈ Finset.range 4, natFourOriginalCOMWeight k • f413descForms k) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413average) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (∑ k ∈ Finset.range 4, natFourOriginalCOMWeight k • f413descForms k) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413average) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (∑ k ∈ Finset.range 4, natFourOriginalCOMWeight k • f413descForms k) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413average) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (∑ k ∈ Finset.range 4, natFourOriginalCOMWeight k • f413descForms k) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413average) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (∑ k ∈ Finset.range 4, natFourOriginalCOMWeight k • f413descForms k) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413average) 4 j) (by decide +kernel)
    exact h 0 b

#print axioms f413_bounded_average

end TorusLean.BosonFiniteCertificate
