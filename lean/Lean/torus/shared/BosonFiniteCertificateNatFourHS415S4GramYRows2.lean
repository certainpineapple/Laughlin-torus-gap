import torus.shared.BosonFiniteCertificateNatFourHS415S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Gram_hY_rows_2 (a : Fin 54) (hlo : 32 ≤ a.val) (hhi : a.val < 48) (b : Fin 54) :
    (f415S4GramAIntᵀ*f415S4GramVInt ) a b=( f415S4GramYInt) a b := by
  fin_cases a
  · change 32 ≤ (0 : ℕ) at hlo
    omega
  · change 32 ≤ (1 : ℕ) at hlo
    omega
  · change 32 ≤ (2 : ℕ) at hlo
    omega
  · change 32 ≤ (3 : ℕ) at hlo
    omega
  · change 32 ≤ (4 : ℕ) at hlo
    omega
  · change 32 ≤ (5 : ℕ) at hlo
    omega
  · change 32 ≤ (6 : ℕ) at hlo
    omega
  · change 32 ≤ (7 : ℕ) at hlo
    omega
  · change 32 ≤ (8 : ℕ) at hlo
    omega
  · change 32 ≤ (9 : ℕ) at hlo
    omega
  · change 32 ≤ (10 : ℕ) at hlo
    omega
  · change 32 ≤ (11 : ℕ) at hlo
    omega
  · change 32 ≤ (12 : ℕ) at hlo
    omega
  · change 32 ≤ (13 : ℕ) at hlo
    omega
  · change 32 ≤ (14 : ℕ) at hlo
    omega
  · change 32 ≤ (15 : ℕ) at hlo
    omega
  · change 32 ≤ (16 : ℕ) at hlo
    omega
  · change 32 ≤ (17 : ℕ) at hlo
    omega
  · change 32 ≤ (18 : ℕ) at hlo
    omega
  · change 32 ≤ (19 : ℕ) at hlo
    omega
  · change 32 ≤ (20 : ℕ) at hlo
    omega
  · change 32 ≤ (21 : ℕ) at hlo
    omega
  · change 32 ≤ (22 : ℕ) at hlo
    omega
  · change 32 ≤ (23 : ℕ) at hlo
    omega
  · change 32 ≤ (24 : ℕ) at hlo
    omega
  · change 32 ≤ (25 : ℕ) at hlo
    omega
  · change 32 ≤ (26 : ℕ) at hlo
    omega
  · change 32 ≤ (27 : ℕ) at hlo
    omega
  · change 32 ≤ (28 : ℕ) at hlo
    omega
  · change 32 ≤ (29 : ℕ) at hlo
    omega
  · change 32 ≤ (30 : ℕ) at hlo
    omega
  · change 32 ≤ (31 : ℕ) at hlo
    omega
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 32 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 32 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 33 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 33 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 34 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 34 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 35 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 35 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 36 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 36 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 37 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 37 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 38 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 38 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 39 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 39 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 40 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 40 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 41 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 41 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 42 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 42 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 43 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 43 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 44 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 44 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 45 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 45 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 46 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 46 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (f415S4GramAIntᵀ*f415S4GramVInt ) 47 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4GramYInt) 47 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (48 : ℕ) < 48 at hhi
    omega
  · change (49 : ℕ) < 48 at hhi
    omega
  · change (50 : ℕ) < 48 at hhi
    omega
  · change (51 : ℕ) < 48 at hhi
    omega
  · change (52 : ℕ) < 48 at hhi
    omega
  · change (53 : ℕ) < 48 at hhi
    omega

#print axioms f415_S4Gram_hY_rows_2
end TorusLean.BosonFiniteCertificate
