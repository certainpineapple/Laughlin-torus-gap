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

theorem f415_raise_nat_cast_chunk3 (b : Fin 16) (a : Fin 54) :
    (f415raiseNat ⟨b.val + 48, by omega⟩ a : ℚ)=
      f415raise ⟨b.val + 48, by omega⟩ a := by
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 48 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 48 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 49 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 49 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 50 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 50 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 51 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 51 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 52 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 52 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 53 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 53 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 54 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 54 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 55 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 55 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 56 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 56 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 57 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 57 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 58 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 58 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 59 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 59 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 60 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 60 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 61 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 61 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 62 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 62 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 63 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 63 a)
      (by decide +kernel) 0 a

#print axioms f415_raise_nat_cast_chunk3
end TorusLean.BosonFiniteCertificate
