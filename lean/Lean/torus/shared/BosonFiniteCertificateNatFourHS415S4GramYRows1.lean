import torus.shared.BosonFiniteCertificateNatFourHS415S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Gram_hY_rows_1 (a : Fin 54) (hlo : 16 ≤ a.val) (hhi : a.val < 32) (b : Fin 54) :
    (f415S4GramAIntᵀ*f415S4GramVInt ) a b=( f415S4GramYInt) a b := by
  fin_cases a
  · change 16 ≤ (0 : ℕ) at hlo
    omega
  · change 16 ≤ (1 : ℕ) at hlo
    omega
  · change 16 ≤ (2 : ℕ) at hlo
    omega
  · change 16 ≤ (3 : ℕ) at hlo
    omega
  · change 16 ≤ (4 : ℕ) at hlo
    omega
  · change 16 ≤ (5 : ℕ) at hlo
    omega
  · change 16 ≤ (6 : ℕ) at hlo
    omega
  · change 16 ≤ (7 : ℕ) at hlo
    omega
  · change 16 ≤ (8 : ℕ) at hlo
    omega
  · change 16 ≤ (9 : ℕ) at hlo
    omega
  · change 16 ≤ (10 : ℕ) at hlo
    omega
  · change 16 ≤ (11 : ℕ) at hlo
    omega
  · change 16 ≤ (12 : ℕ) at hlo
    omega
  · change 16 ≤ (13 : ℕ) at hlo
    omega
  · change 16 ≤ (14 : ℕ) at hlo
    omega
  · change 16 ≤ (15 : ℕ) at hlo
    omega
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 16 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 16 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 17 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 17 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 18 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 18 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 19 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 19 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 20 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 20 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 21 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 21 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 22 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 22 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 23 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 23 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 24 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 24 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 25 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 25 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 26 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 26 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 27 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 27 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 28 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 28 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 29 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 29 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 30 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 30 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 31 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 31 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (32 : ℕ) < 32 at hhi
    omega
  · change (33 : ℕ) < 32 at hhi
    omega
  · change (34 : ℕ) < 32 at hhi
    omega
  · change (35 : ℕ) < 32 at hhi
    omega
  · change (36 : ℕ) < 32 at hhi
    omega
  · change (37 : ℕ) < 32 at hhi
    omega
  · change (38 : ℕ) < 32 at hhi
    omega
  · change (39 : ℕ) < 32 at hhi
    omega
  · change (40 : ℕ) < 32 at hhi
    omega
  · change (41 : ℕ) < 32 at hhi
    omega
  · change (42 : ℕ) < 32 at hhi
    omega
  · change (43 : ℕ) < 32 at hhi
    omega
  · change (44 : ℕ) < 32 at hhi
    omega
  · change (45 : ℕ) < 32 at hhi
    omega
  · change (46 : ℕ) < 32 at hhi
    omega
  · change (47 : ℕ) < 32 at hhi
    omega
  · change (48 : ℕ) < 32 at hhi
    omega
  · change (49 : ℕ) < 32 at hhi
    omega
  · change (50 : ℕ) < 32 at hhi
    omega
  · change (51 : ℕ) < 32 at hhi
    omega
  · change (52 : ℕ) < 32 at hhi
    omega
  · change (53 : ℕ) < 32 at hhi
    omega

#print axioms f415_S4Gram_hY_rows_1
end TorusLean.BosonFiniteCertificate
