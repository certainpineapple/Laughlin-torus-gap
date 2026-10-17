import torus.shared.BosonFiniteCertificateNatFourHS415S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Gram_hW_rows_0 (a : Fin 16) (hlo : 0 ≤ a.val) (hhi : a.val < 16) (b : Fin 16) :
    (natFourIntegerMatrix (2^17) f415S4GramWInt ) a b=( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 0 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 1 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 2 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 3 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 4 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 5 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 6 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 7 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 8 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 9 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 10 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 11 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 12 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 13 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 14 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 16) => (natFourIntegerMatrix (2^17) f415S4GramWInt ) 15 j)
      (fun (_ : Fin 1) (j : Fin 16) => ( (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val)))) 15 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_S4Gram_hW_rows_0
end TorusLean.BosonFiniteCertificate
