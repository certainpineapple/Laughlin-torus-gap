import torus.shared.BosonFiniteCertificateNatFourHS414S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_S4Gram_hY_rows_0 (a : Fin 47) (hlo : 0 ≤ a.val) (hhi : a.val < 16) (b : Fin 47) :
    (f414S4GramAIntᵀ*f414S4GramVInt ) a b=( f414S4GramYInt) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 0 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 1 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 2 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 3 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 4 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 5 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 6 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 7 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 7 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 8 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 8 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 9 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 9 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 10 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 10 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 11 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 11 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 12 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 12 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 13 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 13 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 14 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 14 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (f414S4GramAIntᵀ*f414S4GramVInt ) 15 j)
      (fun (_ : Fin 1) (j : Fin 47) => ( f414S4GramYInt) 15 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (16 : ℕ) < 16 at hhi
    omega
  · change (17 : ℕ) < 16 at hhi
    omega
  · change (18 : ℕ) < 16 at hhi
    omega
  · change (19 : ℕ) < 16 at hhi
    omega
  · change (20 : ℕ) < 16 at hhi
    omega
  · change (21 : ℕ) < 16 at hhi
    omega
  · change (22 : ℕ) < 16 at hhi
    omega
  · change (23 : ℕ) < 16 at hhi
    omega
  · change (24 : ℕ) < 16 at hhi
    omega
  · change (25 : ℕ) < 16 at hhi
    omega
  · change (26 : ℕ) < 16 at hhi
    omega
  · change (27 : ℕ) < 16 at hhi
    omega
  · change (28 : ℕ) < 16 at hhi
    omega
  · change (29 : ℕ) < 16 at hhi
    omega
  · change (30 : ℕ) < 16 at hhi
    omega
  · change (31 : ℕ) < 16 at hhi
    omega
  · change (32 : ℕ) < 16 at hhi
    omega
  · change (33 : ℕ) < 16 at hhi
    omega
  · change (34 : ℕ) < 16 at hhi
    omega
  · change (35 : ℕ) < 16 at hhi
    omega
  · change (36 : ℕ) < 16 at hhi
    omega
  · change (37 : ℕ) < 16 at hhi
    omega
  · change (38 : ℕ) < 16 at hhi
    omega
  · change (39 : ℕ) < 16 at hhi
    omega
  · change (40 : ℕ) < 16 at hhi
    omega
  · change (41 : ℕ) < 16 at hhi
    omega
  · change (42 : ℕ) < 16 at hhi
    omega
  · change (43 : ℕ) < 16 at hhi
    omega
  · change (44 : ℕ) < 16 at hhi
    omega
  · change (45 : ℕ) < 16 at hhi
    omega
  · change (46 : ℕ) < 16 at hhi
    omega

#print axioms f414_S4Gram_hY_rows_0
end TorusLean.BosonFiniteCertificate
