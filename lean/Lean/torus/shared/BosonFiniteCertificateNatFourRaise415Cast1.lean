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

theorem f415_raise_nat_cast_chunk1 (b : Fin 16) (a : Fin 54) :
    (f415raiseNat ⟨b.val + 16, by omega⟩ a : ℚ)=
      f415raise ⟨b.val + 16, by omega⟩ a := by
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 16 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 16 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 17 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 17 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 18 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 18 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 19 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 19 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 20 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 20 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 21 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 21 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 22 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 22 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 23 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 23 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 24 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 24 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 25 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 25 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 26 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 26 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 27 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 27 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 28 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 28 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 29 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 29 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 30 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 30 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 31 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 31 a)
      (by decide +kernel) 0 a

#print axioms f415_raise_nat_cast_chunk1
end TorusLean.BosonFiniteCertificate
