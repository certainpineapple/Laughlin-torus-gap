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

theorem f415_raise_nat_cast_chunk2 (b : Fin 16) (a : Fin 54) :
    (f415raiseNat ⟨b.val + 32, by omega⟩ a : ℚ)=
      f415raise ⟨b.val + 32, by omega⟩ a := by
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 32 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 32 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 33 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 33 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 34 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 34 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 35 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 35 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 36 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 36 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 37 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 37 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 38 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 38 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 39 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 39 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 40 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 40 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 41 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 41 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 42 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 42 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 43 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 43 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 44 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 44 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 45 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 45 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 46 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 46 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 54) => (f415raiseNat 47 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 54) => f415raise 47 a)
      (by decide +kernel) 0 a

#print axioms f415_raise_nat_cast_chunk2
end TorusLean.BosonFiniteCertificate
