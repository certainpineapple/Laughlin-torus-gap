import torus.shared.BosonFiniteCertificateNatFourDescendants411AverageData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411_bounded_average (a : Fin 4) (b : Fin 4) :
    (∑ k ∈ Finset.range 6, natFourOriginalCOMWeight k • f411descForms k) a b=(b411average) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (∑ k ∈ Finset.range 6, natFourOriginalCOMWeight k • f411descForms k) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (b411average) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (∑ k ∈ Finset.range 6, natFourOriginalCOMWeight k • f411descForms k) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (b411average) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (∑ k ∈ Finset.range 6, natFourOriginalCOMWeight k • f411descForms k) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (b411average) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (∑ k ∈ Finset.range 6, natFourOriginalCOMWeight k • f411descForms k) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (b411average) 3 j) (by decide +kernel)
    exact h 0 b

#print axioms f411_bounded_average

end TorusLean.BosonFiniteCertificate
