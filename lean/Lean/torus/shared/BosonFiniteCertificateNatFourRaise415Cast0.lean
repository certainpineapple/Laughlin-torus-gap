import torus.shared.BosonFiniteCertificateNatFourRaise415Data

/-! True Nat COM raising from degree 15 to degree 16.
The target rectangular matrix is checked on the actual rational word action
before the invertible factorial substitution transports it to the source. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open Matrix
open scoped BigOperators

theorem f415_raise_nat_cast_chunk0 (b : Fin 16) (a : Fin 54) :
    (f415raiseNat ⟨b.val + 0, by omega⟩ a : ℚ)=
      f415raise ⟨b.val + 0, by omega⟩ a := by
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 0 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 0 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 1 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 1 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 2 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 2 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 3 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 3 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 4 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 4 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 5 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 5 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 6 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 6 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 7 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 7 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 8 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 8 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 9 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 9 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 10 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 10 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 11 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 11 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 12 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 12 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 13 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 13 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 14 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 14 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 15 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 15 a)
      (by decide +kernel) 0 a

#print axioms f415_raise_nat_cast_chunk0
end TorusLean.BosonFiniteCertificate
