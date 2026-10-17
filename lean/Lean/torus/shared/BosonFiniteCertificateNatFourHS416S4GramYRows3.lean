import torus.shared.BosonFiniteCertificateNatFourHS416S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Gram_hY_rows_3 (a : Fin 64) (hlo : 48 ≤ a.val) (hhi : a.val < 64) (b : Fin 64) :
    (f416S4GramAIntᵀ*f416S4GramVInt ) a b=( f416S4GramYInt) a b := by
  fin_cases a
  · change 48 ≤ (0 : ℕ) at hlo
    omega
  · change 48 ≤ (1 : ℕ) at hlo
    omega
  · change 48 ≤ (2 : ℕ) at hlo
    omega
  · change 48 ≤ (3 : ℕ) at hlo
    omega
  · change 48 ≤ (4 : ℕ) at hlo
    omega
  · change 48 ≤ (5 : ℕ) at hlo
    omega
  · change 48 ≤ (6 : ℕ) at hlo
    omega
  · change 48 ≤ (7 : ℕ) at hlo
    omega
  · change 48 ≤ (8 : ℕ) at hlo
    omega
  · change 48 ≤ (9 : ℕ) at hlo
    omega
  · change 48 ≤ (10 : ℕ) at hlo
    omega
  · change 48 ≤ (11 : ℕ) at hlo
    omega
  · change 48 ≤ (12 : ℕ) at hlo
    omega
  · change 48 ≤ (13 : ℕ) at hlo
    omega
  · change 48 ≤ (14 : ℕ) at hlo
    omega
  · change 48 ≤ (15 : ℕ) at hlo
    omega
  · change 48 ≤ (16 : ℕ) at hlo
    omega
  · change 48 ≤ (17 : ℕ) at hlo
    omega
  · change 48 ≤ (18 : ℕ) at hlo
    omega
  · change 48 ≤ (19 : ℕ) at hlo
    omega
  · change 48 ≤ (20 : ℕ) at hlo
    omega
  · change 48 ≤ (21 : ℕ) at hlo
    omega
  · change 48 ≤ (22 : ℕ) at hlo
    omega
  · change 48 ≤ (23 : ℕ) at hlo
    omega
  · change 48 ≤ (24 : ℕ) at hlo
    omega
  · change 48 ≤ (25 : ℕ) at hlo
    omega
  · change 48 ≤ (26 : ℕ) at hlo
    omega
  · change 48 ≤ (27 : ℕ) at hlo
    omega
  · change 48 ≤ (28 : ℕ) at hlo
    omega
  · change 48 ≤ (29 : ℕ) at hlo
    omega
  · change 48 ≤ (30 : ℕ) at hlo
    omega
  · change 48 ≤ (31 : ℕ) at hlo
    omega
  · change 48 ≤ (32 : ℕ) at hlo
    omega
  · change 48 ≤ (33 : ℕ) at hlo
    omega
  · change 48 ≤ (34 : ℕ) at hlo
    omega
  · change 48 ≤ (35 : ℕ) at hlo
    omega
  · change 48 ≤ (36 : ℕ) at hlo
    omega
  · change 48 ≤ (37 : ℕ) at hlo
    omega
  · change 48 ≤ (38 : ℕ) at hlo
    omega
  · change 48 ≤ (39 : ℕ) at hlo
    omega
  · change 48 ≤ (40 : ℕ) at hlo
    omega
  · change 48 ≤ (41 : ℕ) at hlo
    omega
  · change 48 ≤ (42 : ℕ) at hlo
    omega
  · change 48 ≤ (43 : ℕ) at hlo
    omega
  · change 48 ≤ (44 : ℕ) at hlo
    omega
  · change 48 ≤ (45 : ℕ) at hlo
    omega
  · change 48 ≤ (46 : ℕ) at hlo
    omega
  · change 48 ≤ (47 : ℕ) at hlo
    omega
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 48 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 48 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 49 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 49 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 50 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 50 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 51 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 51 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 52 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 52 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 53 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 53 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 54 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 54 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 55 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 55 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 56 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 56 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 57 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 57 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 58 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 58 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 59 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 59 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 60 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 60 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 61 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 61 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 62 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 62 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (f416S4GramAIntᵀ*f416S4GramVInt ) 63 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416S4GramYInt) 63 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f416_S4Gram_hY_rows_3
end TorusLean.BosonFiniteCertificate
