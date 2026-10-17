import torus.shared.BosonFiniteCertificateCanonicalTransport

/-! Kernel-checked membership of every true pair-creator output occupation
in the existing complete three-particle degree blocks. Original source data
are read only; all repeated and ordered pair labels remain allowed. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem k300_pair_output_membership
    (p : Fin 1) (a : Fin (p.val+1)) :
    ∃ b : Fin 1, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (0-p.val)] = k300occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k300_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k301_pair_output_membership
    (p : Fin 2) (a : Fin (p.val+1)) :
    ∃ b : Fin 1, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (1-p.val)] = k301occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k301_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k301_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k301_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k302_pair_output_membership
    (p : Fin 3) (a : Fin (p.val+1)) :
    ∃ b : Fin 2, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (2-p.val)] = k302occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k302_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k302_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k302_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k302_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k302_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k302_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k303_pair_output_membership
    (p : Fin 4) (a : Fin (p.val+1)) :
    ∃ b : Fin 3, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (3-p.val)] = k303occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k303_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k304_pair_output_membership
    (p : Fin 5) (a : Fin (p.val+1)) :
    ∃ b : Fin 4, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (4-p.val)] = k304occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k304_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k305_pair_output_membership
    (p : Fin 6) (a : Fin (p.val+1)) :
    ∃ b : Fin 5, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (5-p.val)] = k305occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k305_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k306_pair_output_membership
    (p : Fin 7) (a : Fin (p.val+1)) :
    ∃ b : Fin 7, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (6-p.val)] = k306occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k306_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k307_pair_output_membership
    (p : Fin 8) (a : Fin (p.val+1)) :
    ∃ b : Fin 8, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (7-p.val)] = k307occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k307_occupation_source_word]
      fin_cases j <;> decide +kernel

theorem k308_pair_output_membership
    (p : Fin 9) (a : Fin (p.val+1)) :
    ∃ b : Fin 10, wordOccupation [fin9 a.val, fin9 (p.val-a.val), fin9 (8-p.val)] = k308occ b := by
  fin_cases p
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨8, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨9, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨9, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨8, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨9, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨8, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨7, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨6, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨5, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
  · fin_cases a
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨4, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨3, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨2, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨1, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel
    · refine ⟨0, ?_⟩
      ext j
      rw [wordOccupation_apply, k308_occupation_source_word]
      fin_cases j <;> decide +kernel

end TorusLean.BosonFiniteCertificate
