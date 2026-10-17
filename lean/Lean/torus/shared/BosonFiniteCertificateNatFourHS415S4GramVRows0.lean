import torus.shared.BosonFiniteCertificateNatFourHS415S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Gram_hV_rows_0 (a : Fin 16) (hlo : 0 ≤ a.val) (hhi : a.val < 16) (b : Fin 54) :
    (f415S4GramWInt*f415S4GramAInt ) a b=( f415S4GramVInt) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 0 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 1 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 2 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 3 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 4 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 5 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 6 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 7 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 7 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 8 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 8 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 9 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 9 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 10 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 10 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 11 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 11 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 12 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 12 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 13 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 13 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 14 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 14 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramWInt*f415S4GramAInt ) 15 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramVInt) 15 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f415_S4Gram_hV_rows_0
end TorusLean.BosonFiniteCertificate
