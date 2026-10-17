import torus.shared.BosonFiniteCertificateNatFourDescendants415AverageData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_bounded_average (a : Fin 7) (b : Fin 7) :
    (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) a b=(b415average) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415average) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415average) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415average) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415average) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415average) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415average) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (∑ k ∈ Finset.range 2, natFourOriginalCOMWeight k • f415descForms k) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415average) 6 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_bounded_average

end TorusLean.BosonFiniteCertificate
