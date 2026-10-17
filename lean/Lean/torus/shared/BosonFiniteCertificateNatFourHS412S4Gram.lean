import torus.shared.BosonFiniteCertificateNatFourHS412S4Amplitudes

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f412hs_shape (a : Fin 34) :
    (f412basis a).length=4 ∧ (f412basis a).sum=12 := by
  apply natFourBasis_shape 12
  rw [← f412_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

private def f412S4GramAInt : Matrix (Fin 13) (Fin 34) ℤ :=
  fun i j => (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 12 else 4) else 4) else (if j.val < 6 then 4 else (if j.val < 7 then 4 else 0))) else 0) else 0) else (if i.val < 2 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 8) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 8))) else (if j.val < 12 then 4 else 0)) else 0) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 8 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 4))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 4 else 0) else 0) else (if j.val < 14 then (if j.val < 13 then 8 else 4) else (if j.val < 15 then 4 else (if j.val < 16 then 4 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 12 else 4)) else (if j.val < 23 then 4 else (if j.val < 24 then 4 else 0))) else 0)))) else (if i.val < 4 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 8)) else 0) else (if j.val < 12 then (if j.val < 10 then 4 else 0) else (if j.val < 14 then (if j.val < 13 then 0 else 4) else (if j.val < 15 then 0 else (if j.val < 16 then 0 else 8))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 4 else 0) else (if j.val < 20 then 0 else 8)) else (if j.val < 23 then 0 else (if j.val < 24 then 0 else 8))) else (if j.val < 29 then (if j.val < 27 then 4 else 0) else 0))) else (if i.val < 5 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 8 else 0) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 4) else (if j.val < 11 then 4 else 0)) else (if j.val < 14 then (if j.val < 13 then 4 else 0) else (if j.val < 15 then 4 else 0)))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 4 else 12) else 0) else (if j.val < 23 then (if j.val < 22 then 8 else 0) else (if j.val < 24 then 0 else 4))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 4 else 0) else (if j.val < 28 then 8 else 4)) else (if j.val < 31 then (if j.val < 30 then 12 else 4) else (if j.val < 32 then 4 else 0))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 8) else 0)) else (if j.val < 12 then (if j.val < 10 then 0 else 4) else (if j.val < 14 then (if j.val < 13 then 0 else 4) else (if j.val < 15 then 0 else (if j.val < 16 then 8 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 4 else 0) else 0) else (if j.val < 23 then (if j.val < 22 then 0 else 8) else 0)) else (if j.val < 29 then (if j.val < 27 then 4 else (if j.val < 28 then 0 else 8)) else (if j.val < 31 then (if j.val < 30 then 0 else 8) else (if j.val < 32 then 0 else (if j.val < 33 then 8 else 0))))))))) else (if i.val < 9 then (if i.val < 7 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 16 else 0))) else (if j.val < 12 then (if j.val < 10 then 0 else (if j.val < 11 then 0 else 8)) else (if j.val < 14 then 0 else (if j.val < 15 then 8 else (if j.val < 16 then 0 else 8))))) else (if j.val < 25 then (if j.val < 21 then 0 else (if j.val < 23 then 0 else (if j.val < 24 then 16 else 0))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 0 else 8) else (if j.val < 28 then 8 else 0)) else (if j.val < 31 then 0 else (if j.val < 32 then 16 else (if j.val < 33 then 8 else 24)))))) else (if i.val < 8 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 8) else 0)) else (if j.val < 12 then (if j.val < 10 then 0 else 4) else (if j.val < 14 then (if j.val < 13 then 0 else 4) else (if j.val < 15 then 0 else (if j.val < 16 then 8 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 4 else 0) else 0) else (if j.val < 23 then (if j.val < 22 then 0 else 8) else 0)) else (if j.val < 29 then (if j.val < 27 then 4 else (if j.val < 28 then 0 else 8)) else (if j.val < 31 then (if j.val < 30 then 0 else 8) else (if j.val < 32 then 0 else (if j.val < 33 then 8 else 0)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 8 else 0) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 4) else (if j.val < 11 then 4 else 0)) else (if j.val < 14 then (if j.val < 13 then 4 else 0) else (if j.val < 15 then 4 else 0)))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 4 else 12) else 0) else (if j.val < 23 then (if j.val < 22 then 8 else 0) else (if j.val < 24 then 0 else 4))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 4 else 0) else (if j.val < 28 then 8 else 4)) else (if j.val < 31 then (if j.val < 30 then 12 else 4) else (if j.val < 32 then 4 else 0))))))) else (if i.val < 11 then (if i.val < 10 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 8)) else 0) else (if j.val < 12 then (if j.val < 10 then 4 else 0) else (if j.val < 14 then (if j.val < 13 then 0 else 4) else (if j.val < 15 then 0 else (if j.val < 16 then 0 else 8))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 4 else 0) else (if j.val < 20 then 0 else 8)) else (if j.val < 23 then 0 else (if j.val < 24 then 0 else 8))) else (if j.val < 29 then (if j.val < 27 then 4 else 0) else 0))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 8 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 4))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 4 else 0) else 0) else (if j.val < 14 then (if j.val < 13 then 8 else 4) else (if j.val < 15 then 4 else (if j.val < 16 then 4 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 12 else 4)) else (if j.val < 23 then 4 else (if j.val < 24 then 4 else 0))) else 0))) else (if i.val < 12 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 8) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 8))) else (if j.val < 12 then 4 else 0)) else 0) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 12 else 4) else 4) else (if j.val < 6 then 4 else (if j.val < 7 then 4 else 0))) else 0) else 0)))))

private def f412S4GramWInt : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.diagonal (fun p : Fin 13 => ((p.val.factorial * (12-p.val).factorial : ℕ) : ℤ))

private def f412S4GramVInt : Matrix (Fin 13) (Fin 34) ℤ :=
  fun i j => (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5748019200 else 1916006400) else 1916006400) else (if j.val < 6 then 1916006400 else (if j.val < 7 then 1916006400 else 0))) else 0) else 0) else (if i.val < 2 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 319334400) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 319334400))) else (if j.val < 12 then 159667200 else 0)) else 0) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 58060800 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 29030400))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 29030400 else 0) else 0) else (if j.val < 14 then (if j.val < 13 then 58060800 else 29030400) else (if j.val < 15 then 29030400 else (if j.val < 16 then 29030400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 87091200 else 29030400)) else (if j.val < 23 then 29030400 else (if j.val < 24 then 29030400 else 0))) else 0)))) else (if i.val < 4 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 17418240)) else 0) else (if j.val < 12 then (if j.val < 10 then 8709120 else 0) else (if j.val < 14 then (if j.val < 13 then 0 else 8709120) else (if j.val < 15 then 0 else (if j.val < 16 then 0 else 17418240))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 8709120 else 0) else (if j.val < 20 then 0 else 17418240)) else (if j.val < 23 then 0 else (if j.val < 24 then 0 else 17418240))) else (if j.val < 29 then (if j.val < 27 then 8709120 else 0) else 0))) else (if i.val < 5 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 7741440 else 0) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 3870720) else (if j.val < 11 then 3870720 else 0)) else (if j.val < 14 then (if j.val < 13 then 3870720 else 0) else (if j.val < 15 then 3870720 else 0)))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 3870720 else 11612160) else 0) else (if j.val < 23 then (if j.val < 22 then 7741440 else 0) else (if j.val < 24 then 0 else 3870720))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 3870720 else 0) else (if j.val < 28 then 7741440 else 3870720)) else (if j.val < 31 then (if j.val < 30 then 11612160 else 3870720) else (if j.val < 32 then 3870720 else 0))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 4838400) else 0)) else (if j.val < 12 then (if j.val < 10 then 0 else 2419200) else (if j.val < 14 then (if j.val < 13 then 0 else 2419200) else (if j.val < 15 then 0 else (if j.val < 16 then 4838400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 2419200 else 0) else 0) else (if j.val < 23 then (if j.val < 22 then 0 else 4838400) else 0)) else (if j.val < 29 then (if j.val < 27 then 2419200 else (if j.val < 28 then 0 else 4838400)) else (if j.val < 31 then (if j.val < 30 then 0 else 4838400) else (if j.val < 32 then 0 else (if j.val < 33 then 4838400 else 0))))))))) else (if i.val < 9 then (if i.val < 7 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 8294400 else 0))) else (if j.val < 12 then (if j.val < 10 then 0 else (if j.val < 11 then 0 else 4147200)) else (if j.val < 14 then 0 else (if j.val < 15 then 4147200 else (if j.val < 16 then 0 else 4147200))))) else (if j.val < 25 then (if j.val < 21 then 0 else (if j.val < 23 then 0 else (if j.val < 24 then 8294400 else 0))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 0 else 4147200) else (if j.val < 28 then 4147200 else 0)) else (if j.val < 31 then 0 else (if j.val < 32 then 8294400 else (if j.val < 33 then 4147200 else 12441600)))))) else (if i.val < 8 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 4838400) else 0)) else (if j.val < 12 then (if j.val < 10 then 0 else 2419200) else (if j.val < 14 then (if j.val < 13 then 0 else 2419200) else (if j.val < 15 then 0 else (if j.val < 16 then 4838400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 2419200 else 0) else 0) else (if j.val < 23 then (if j.val < 22 then 0 else 4838400) else 0)) else (if j.val < 29 then (if j.val < 27 then 2419200 else (if j.val < 28 then 0 else 4838400)) else (if j.val < 31 then (if j.val < 30 then 0 else 4838400) else (if j.val < 32 then 0 else (if j.val < 33 then 4838400 else 0)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 7741440 else 0) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 3870720) else (if j.val < 11 then 3870720 else 0)) else (if j.val < 14 then (if j.val < 13 then 3870720 else 0) else (if j.val < 15 then 3870720 else 0)))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 3870720 else 11612160) else 0) else (if j.val < 23 then (if j.val < 22 then 7741440 else 0) else (if j.val < 24 then 0 else 3870720))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 3870720 else 0) else (if j.val < 28 then 7741440 else 3870720)) else (if j.val < 31 then (if j.val < 30 then 11612160 else 3870720) else (if j.val < 32 then 3870720 else 0))))))) else (if i.val < 11 then (if i.val < 10 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 17418240)) else 0) else (if j.val < 12 then (if j.val < 10 then 8709120 else 0) else (if j.val < 14 then (if j.val < 13 then 0 else 8709120) else (if j.val < 15 then 0 else (if j.val < 16 then 0 else 17418240))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 8709120 else 0) else (if j.val < 20 then 0 else 17418240)) else (if j.val < 23 then 0 else (if j.val < 24 then 0 else 17418240))) else (if j.val < 29 then (if j.val < 27 then 8709120 else 0) else 0))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 58060800 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 29030400))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 29030400 else 0) else 0) else (if j.val < 14 then (if j.val < 13 then 58060800 else 29030400) else (if j.val < 15 then 29030400 else (if j.val < 16 then 29030400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 87091200 else 29030400)) else (if j.val < 23 then 29030400 else (if j.val < 24 then 29030400 else 0))) else 0))) else (if i.val < 12 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 319334400) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 319334400))) else (if j.val < 12 then 159667200 else 0)) else 0) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 5748019200 else 1916006400) else 1916006400) else (if j.val < 6 then 1916006400 else (if j.val < 7 then 1916006400 else 0))) else 0) else 0)))))

private def f412S4GramYInt : Matrix (Fin 34) (Fin 34) ℤ :=
  fun i j => (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 137952460800 else 45984153600) else 45984153600) else (if j.val < 6 then 45984153600 else (if j.val < 7 then 45984153600 else 0))) else 0) else 0) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 45984153600 else 20437401600) else 15328051200) else (if j.val < 6 then 15328051200 else (if j.val < 7 then 15328051200 else 5109350400))) else (if j.val < 12 then 2554675200 else 0)) else 0)) else (if i.val < 3 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 45984153600 else 15328051200) else (if j.val < 3 then 16257024000 else 15328051200)) else (if j.val < 6 then 15328051200 else (if j.val < 7 then 15328051200 else 464486400))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 464486400 else 0) else 0) else (if j.val < 14 then (if j.val < 13 then 928972800 else 464486400) else (if j.val < 15 then 464486400 else (if j.val < 16 then 464486400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 1393459200 else 464486400)) else (if j.val < 23 then 464486400 else (if j.val < 24 then 464486400 else 0))) else 0)) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 45984153600 else 15328051200) else (if j.val < 3 then 15328051200 else 15606743040)) else (if j.val < 6 then 15328051200 else (if j.val < 7 then 15328051200 else 0))) else (if j.val < 12 then (if j.val < 10 then 139345920 else 0) else (if j.val < 14 then (if j.val < 13 then 0 else 139345920) else (if j.val < 15 then 0 else (if j.val < 16 then 0 else 278691840))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 139345920 else 0) else (if j.val < 20 then 0 else 278691840)) else (if j.val < 23 then 0 else (if j.val < 24 then 0 else 278691840))) else (if j.val < 29 then (if j.val < 27 then 139345920 else 0) else 0))))) else (if i.val < 6 then (if i.val < 5 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 45984153600 else 15328051200) else 15328051200) else (if j.val < 6 then (if j.val < 5 then 15451914240 else 15328051200) else (if j.val < 7 then 15328051200 else 0))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 61931520) else (if j.val < 11 then 61931520 else 0)) else (if j.val < 14 then (if j.val < 13 then 61931520 else 0) else (if j.val < 15 then 61931520 else 0)))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 61931520 else 185794560) else 0) else (if j.val < 23 then (if j.val < 22 then 123863040 else 0) else (if j.val < 24 then 0 else 61931520))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 61931520 else 0) else (if j.val < 28 then 123863040 else 61931520)) else (if j.val < 31 then (if j.val < 30 then 185794560 else 61931520) else (if j.val < 32 then 61931520 else 0))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 45984153600 else 15328051200) else 15328051200) else (if j.val < 6 then (if j.val < 5 then 15328051200 else 15405465600) else (if j.val < 7 then 15328051200 else 0))) else (if j.val < 12 then (if j.val < 10 then 0 else 38707200) else (if j.val < 14 then (if j.val < 13 then 0 else 38707200) else (if j.val < 15 then 0 else (if j.val < 16 then 77414400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 38707200 else 0) else 0) else (if j.val < 23 then (if j.val < 22 then 0 else 77414400) else 0)) else (if j.val < 29 then (if j.val < 27 then 38707200 else (if j.val < 28 then 0 else 77414400)) else (if j.val < 31 then (if j.val < 30 then 0 else 77414400) else (if j.val < 32 then 0 else (if j.val < 33 then 77414400 else 0))))))) else (if i.val < 7 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 45984153600 else 15328051200) else 15328051200) else (if j.val < 6 then 15328051200 else (if j.val < 7 then 15460761600 else 0))) else (if j.val < 12 then (if j.val < 10 then 0 else (if j.val < 11 then 0 else 66355200)) else (if j.val < 14 then 0 else (if j.val < 15 then 66355200 else (if j.val < 16 then 0 else 66355200))))) else (if j.val < 25 then (if j.val < 21 then 0 else (if j.val < 23 then 0 else (if j.val < 24 then 132710400 else 0))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 0 else 66355200) else (if j.val < 28 then 66355200 else 0)) else (if j.val < 31 then 0 else (if j.val < 32 then 132710400 else (if j.val < 33 then 66355200 else 199065600)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 5109350400) else (if j.val < 3 then 464486400 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 5341593600))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 2786918400 else 2554675200) else 2554675200) else (if j.val < 14 then (if j.val < 13 then 464486400 else 232243200) else (if j.val < 15 then 232243200 else (if j.val < 16 then 232243200 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 696729600 else 232243200)) else (if j.val < 23 then 232243200 else (if j.val < 24 then 232243200 else 0))) else 0))))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 2554675200) else (if j.val < 3 then 464486400 else 139345920)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 2786918400))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 1579253760 else 1347010560) else 1277337600) else (if j.val < 14 then (if j.val < 13 then 464486400 else 301916160) else (if j.val < 15 then 232243200 else (if j.val < 16 then 232243200 else 139345920))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 69672960 else 0) else (if j.val < 20 then 696729600 else 371589120)) else (if j.val < 23 then 232243200 else (if j.val < 24 then 232243200 else 139345920))) else (if j.val < 29 then (if j.val < 27 then 69672960 else 0) else 0))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 2554675200) else (if j.val < 3 then 0 else 139345920)) else (if j.val < 6 then (if j.val < 5 then 61931520 else 0) else (if j.val < 7 then 0 else 2554675200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 1347010560 else 1377976320) else (if j.val < 11 then 1308303360 else 1277337600)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 69672960) else (if j.val < 15 then 30965760 else (if j.val < 16 then 0 else 139345920))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 100638720 else 92897280) else (if j.val < 20 then 0 else 139345920)) else (if j.val < 23 then (if j.val < 22 then 61931520 else 0) else (if j.val < 24 then 0 else 170311680))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 100638720 else 69672960) else (if j.val < 28 then 61931520 else 30965760)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 30965760) else (if j.val < 32 then 30965760 else 0)))))) else (if i.val < 11 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 2554675200) else 0) else (if j.val < 6 then (if j.val < 5 then 61931520 else 38707200) else (if j.val < 7 then 0 else 2554675200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 1277337600 else 1308303360) else (if j.val < 11 then 1327656960 else 1296691200)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 19353600) else (if j.val < 15 then 30965760 else (if j.val < 16 then 38707200 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 50319360 else 92897280) else 0) else (if j.val < 23 then (if j.val < 22 then 61931520 else 38707200) else (if j.val < 24 then 0 else 30965760))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 50319360 else 19353600) else (if j.val < 28 then 61931520 else 69672960)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 69672960) else (if j.val < 32 then 30965760 else (if j.val < 33 then 38707200 else 0)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 2554675200) else 0) else (if j.val < 6 then (if j.val < 5 then 0 else 38707200) else (if j.val < 7 then 66355200 else 2554675200))) else (if j.val < 12 then (if j.val < 10 then 1277337600 else (if j.val < 11 then 1296691200 else 1329868800)) else (if j.val < 14 then (if j.val < 13 then 0 else 19353600) else (if j.val < 15 then 33177600 else (if j.val < 16 then 38707200 else 33177600))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 19353600 else 0) else 0) else (if j.val < 23 then (if j.val < 22 then 0 else 38707200) else (if j.val < 24 then 66355200 else 0))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 19353600 else 52531200) else (if j.val < 28 then 33177600 else 38707200)) else (if j.val < 31 then (if j.val < 30 then 0 else 38707200) else (if j.val < 32 then 66355200 else (if j.val < 33 then 71884800 else 99532800)))))))) else (if i.val < 14 then (if i.val < 13 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 928972800 else 0)) else (if j.val < 6 then (if j.val < 5 then 61931520 else 0) else (if j.val < 7 then 0 else 464486400))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 464486400 else 30965760) else (if j.val < 11 then 30965760 else 0)) else (if j.val < 14 then (if j.val < 13 then 959938560 else 464486400) else (if j.val < 15 then 495452160 else (if j.val < 16 then 464486400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 30965760 else 92897280) else (if j.val < 20 then 1393459200 else 464486400)) else (if j.val < 23 then (if j.val < 22 then 526417920 else 464486400) else (if j.val < 24 then 464486400 else 30965760))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 30965760 else 0) else (if j.val < 28 then 61931520 else 30965760)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 30965760) else (if j.val < 32 then 30965760 else 0))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 464486400 else 139345920)) else (if j.val < 6 then (if j.val < 5 then 0 else 38707200) else (if j.val < 7 then 0 else 232243200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 301916160 else 69672960) else 19353600) else (if j.val < 14 then (if j.val < 13 then 464486400 else 321269760) else (if j.val < 15 then 232243200 else (if j.val < 16 then 270950400 else 139345920))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 89026560 else 0) else (if j.val < 20 then 696729600 else 371589120)) else (if j.val < 23 then (if j.val < 22 then 232243200 else 270950400) else (if j.val < 24 then 232243200 else 139345920))) else (if j.val < 29 then (if j.val < 27 then 89026560 else (if j.val < 28 then 0 else 38707200)) else (if j.val < 31 then (if j.val < 30 then 0 else 38707200) else (if j.val < 32 then 0 else (if j.val < 33 then 38707200 else 0))))))) else (if i.val < 15 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 464486400 else 0)) else (if j.val < 6 then (if j.val < 5 then 61931520 else 0) else (if j.val < 7 then 66355200 else 232243200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 232243200 else 30965760) else (if j.val < 11 then 30965760 else 33177600)) else (if j.val < 14 then (if j.val < 13 then 495452160 else 232243200) else (if j.val < 15 then 296386560 else (if j.val < 16 then 232243200 else 33177600))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 30965760 else 92897280) else (if j.val < 20 then 696729600 else 232243200)) else (if j.val < 23 then (if j.val < 22 then 294174720 else 232243200) else (if j.val < 24 then 298598400 else 30965760))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 30965760 else 33177600) else (if j.val < 28 then 95109120 else 30965760)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 30965760) else (if j.val < 32 then 97320960 else (if j.val < 33 then 33177600 else 99532800)))))) else (if i.val < 16 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 464486400 else 0)) else (if j.val < 6 then (if j.val < 5 then 0 else 77414400) else (if j.val < 7 then 0 else 232243200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 232243200 else 0) else 38707200) else (if j.val < 14 then (if j.val < 13 then 464486400 else 270950400) else (if j.val < 15 then 232243200 else (if j.val < 16 then 309657600 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 38707200 else 0) else (if j.val < 20 then 696729600 else 232243200)) else (if j.val < 23 then (if j.val < 22 then 232243200 else 309657600) else (if j.val < 24 then 232243200 else 0))) else (if j.val < 29 then (if j.val < 27 then 38707200 else (if j.val < 28 then 0 else 77414400)) else (if j.val < 31 then (if j.val < 30 then 0 else 77414400) else (if j.val < 32 then 0 else (if j.val < 33 then 77414400 else 0)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 278691840)) else (if j.val < 6 then 0 else (if j.val < 7 then 66355200 else 0))) else (if j.val < 12 then (if j.val < 10 then 139345920 else (if j.val < 11 then 0 else 33177600)) else (if j.val < 14 then (if j.val < 13 then 0 else 139345920) else (if j.val < 15 then 33177600 else (if j.val < 16 then 0 else 311869440))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 139345920 else 0) else (if j.val < 20 then 0 else 278691840)) else (if j.val < 23 then 0 else (if j.val < 24 then 66355200 else 278691840))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 139345920 else 172523520) else (if j.val < 28 then 33177600 else 0)) else (if j.val < 31 then 0 else (if j.val < 32 then 66355200 else (if j.val < 33 then 33177600 else 99532800))))))))))) else (if i.val < 25 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 139345920)) else (if j.val < 6 then (if j.val < 5 then 61931520 else 38707200) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 69672960 else 100638720) else (if j.val < 11 then 50319360 else 19353600)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 89026560) else (if j.val < 15 then 30965760 else (if j.val < 16 then 38707200 else 139345920))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 119992320 else 92897280) else (if j.val < 20 then 0 else 139345920)) else (if j.val < 23 then (if j.val < 22 then 61931520 else 38707200) else (if j.val < 24 then 0 else 170311680))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 119992320 else 89026560) else (if j.val < 28 then 61931520 else 69672960)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 69672960) else (if j.val < 32 then 30965760 else (if j.val < 33 then 38707200 else 0)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 185794560 else 0) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 92897280) else (if j.val < 11 then 92897280 else 0)) else (if j.val < 14 then (if j.val < 13 then 92897280 else 0) else (if j.val < 15 then 92897280 else 0)))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 92897280 else 278691840) else 0) else (if j.val < 23 then (if j.val < 22 then 185794560 else 0) else (if j.val < 24 then 0 else 92897280))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 92897280 else 0) else (if j.val < 28 then 185794560 else 92897280)) else (if j.val < 31 then (if j.val < 30 then 278691840 else 92897280) else (if j.val < 32 then 92897280 else 0)))))) else (if i.val < 20 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 1393459200 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 696729600))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 696729600 else 0) else 0) else (if j.val < 14 then (if j.val < 13 then 1393459200 else 696729600) else (if j.val < 15 then 696729600 else (if j.val < 16 then 696729600 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 2090188800 else 696729600)) else (if j.val < 23 then 696729600 else (if j.val < 24 then 696729600 else 0))) else 0)) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 464486400 else 278691840)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 232243200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 371589120 else 139345920) else 0) else (if j.val < 14 then (if j.val < 13 then 464486400 else 371589120) else (if j.val < 15 then 232243200 else (if j.val < 16 then 232243200 else 278691840))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 139345920 else 0) else (if j.val < 20 then 696729600 else 510935040)) else (if j.val < 23 then 232243200 else (if j.val < 24 then 232243200 else 278691840))) else (if j.val < 29 then (if j.val < 27 then 139345920 else 0) else 0))))) else (if i.val < 23 then (if i.val < 22 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 464486400 else 0)) else (if j.val < 6 then (if j.val < 5 then 123863040 else 0) else (if j.val < 7 then 0 else 232243200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 232243200 else 61931520) else (if j.val < 11 then 61931520 else 0)) else (if j.val < 14 then (if j.val < 13 then 526417920 else 232243200) else (if j.val < 15 then 294174720 else (if j.val < 16 then 232243200 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 61931520 else 185794560) else (if j.val < 20 then 696729600 else 232243200)) else (if j.val < 23 then (if j.val < 22 then 356106240 else 232243200) else (if j.val < 24 then 232243200 else 61931520))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 61931520 else 0) else (if j.val < 28 then 123863040 else 61931520)) else (if j.val < 31 then (if j.val < 30 then 185794560 else 61931520) else (if j.val < 32 then 61931520 else 0))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 464486400 else 0)) else (if j.val < 6 then (if j.val < 5 then 0 else 77414400) else (if j.val < 7 then 0 else 232243200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 232243200 else 0) else 38707200) else (if j.val < 14 then (if j.val < 13 then 464486400 else 270950400) else (if j.val < 15 then 232243200 else (if j.val < 16 then 309657600 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 38707200 else 0) else (if j.val < 20 then 696729600 else 232243200)) else (if j.val < 23 then (if j.val < 22 then 232243200 else 309657600) else (if j.val < 24 then 232243200 else 0))) else (if j.val < 29 then (if j.val < 27 then 38707200 else (if j.val < 28 then 0 else 77414400)) else (if j.val < 31 then (if j.val < 30 then 0 else 77414400) else (if j.val < 32 then 0 else (if j.val < 33 then 77414400 else 0))))))) else (if i.val < 24 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 464486400 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 132710400 else 232243200))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 232243200 else 0) else (if j.val < 11 then 0 else 66355200)) else (if j.val < 14 then (if j.val < 13 then 464486400 else 232243200) else (if j.val < 15 then 298598400 else (if j.val < 16 then 232243200 else 66355200))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then 0 else (if j.val < 20 then 696729600 else 232243200)) else (if j.val < 23 then 232243200 else (if j.val < 24 then 364953600 else 0))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 0 else 66355200) else (if j.val < 28 then 66355200 else 0)) else (if j.val < 31 then 0 else (if j.val < 32 then 132710400 else (if j.val < 33 then 66355200 else 199065600)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 278691840)) else (if j.val < 6 then (if j.val < 5 then 61931520 else 0) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 139345920 else 170311680) else (if j.val < 11 then 30965760 else 0)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 139345920) else (if j.val < 15 then 30965760 else (if j.val < 16 then 0 else 278691840))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 170311680 else 92897280) else (if j.val < 20 then 0 else 278691840)) else (if j.val < 23 then (if j.val < 22 then 61931520 else 0) else (if j.val < 24 then 0 else 309657600))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 170311680 else 139345920) else (if j.val < 28 then 61931520 else 30965760)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 30965760) else (if j.val < 32 then 30965760 else 0)))))))) else (if i.val < 29 then (if i.val < 27 then (if i.val < 26 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 139345920)) else (if j.val < 6 then (if j.val < 5 then 61931520 else 38707200) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 69672960 else 100638720) else (if j.val < 11 then 50319360 else 19353600)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 89026560) else (if j.val < 15 then 30965760 else (if j.val < 16 then 38707200 else 139345920))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 119992320 else 92897280) else (if j.val < 20 then 0 else 139345920)) else (if j.val < 23 then (if j.val < 22 then 61931520 else 38707200) else (if j.val < 24 then 0 else 170311680))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 119992320 else 89026560) else (if j.val < 28 then 61931520 else 69672960)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 69672960) else (if j.val < 32 then 30965760 else (if j.val < 33 then 38707200 else 0)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 139345920)) else (if j.val < 6 then (if j.val < 5 then 0 else 38707200) else (if j.val < 7 then 66355200 else 0))) else (if j.val < 12 then (if j.val < 10 then 69672960 else (if j.val < 11 then 19353600 else 52531200)) else (if j.val < 14 then (if j.val < 13 then 0 else 89026560) else (if j.val < 15 then 33177600 else (if j.val < 16 then 38707200 else 172523520))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 89026560 else 0) else (if j.val < 20 then 0 else 139345920)) else (if j.val < 23 then (if j.val < 22 then 0 else 38707200) else (if j.val < 24 then 66355200 else 139345920))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 89026560 else 122204160) else (if j.val < 28 then 33177600 else 38707200)) else (if j.val < 31 then (if j.val < 30 then 0 else 38707200) else (if j.val < 32 then 66355200 else (if j.val < 33 then 71884800 else 99532800))))))) else (if i.val < 28 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 123863040 else 0) else (if j.val < 7 then 66355200 else 0))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 61931520) else (if j.val < 11 then 61931520 else 33177600)) else (if j.val < 14 then (if j.val < 13 then 61931520 else 0) else (if j.val < 15 then 95109120 else (if j.val < 16 then 0 else 33177600))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 61931520 else 185794560) else 0) else (if j.val < 23 then (if j.val < 22 then 123863040 else 0) else (if j.val < 24 then 66355200 else 61931520))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 61931520 else 33177600) else (if j.val < 28 then 157040640 else 61931520)) else (if j.val < 31 then (if j.val < 30 then 185794560 else 61931520) else (if j.val < 32 then 128286720 else (if j.val < 33 then 33177600 else 99532800)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 61931520 else 77414400) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 30965760) else (if j.val < 11 then 69672960 else 38707200)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 38707200) else (if j.val < 15 then 30965760 else (if j.val < 16 then 77414400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 69672960 else 92897280) else 0) else (if j.val < 23 then (if j.val < 22 then 61931520 else 77414400) else (if j.val < 24 then 0 else 30965760))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 69672960 else 38707200) else (if j.val < 28 then 61931520 else 108380160)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 108380160) else (if j.val < 32 then 30965760 else (if j.val < 33 then 77414400 else 0)))))))) else (if i.val < 31 then (if i.val < 30 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 185794560 else 0) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 92897280) else (if j.val < 11 then 92897280 else 0)) else (if j.val < 14 then (if j.val < 13 then 92897280 else 0) else (if j.val < 15 then 92897280 else 0)))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 92897280 else 278691840) else 0) else (if j.val < 23 then (if j.val < 22 then 185794560 else 0) else (if j.val < 24 then 0 else 92897280))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 92897280 else 0) else (if j.val < 28 then 185794560 else 92897280)) else (if j.val < 31 then (if j.val < 30 then 278691840 else 92897280) else (if j.val < 32 then 92897280 else 0))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 61931520 else 77414400) else 0)) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 30965760) else (if j.val < 11 then 69672960 else 38707200)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 38707200) else (if j.val < 15 then 30965760 else (if j.val < 16 then 77414400 else 0))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 69672960 else 92897280) else 0) else (if j.val < 23 then (if j.val < 22 then 61931520 else 77414400) else (if j.val < 24 then 0 else 30965760))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 69672960 else 38707200) else (if j.val < 28 then 61931520 else 108380160)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 108380160) else (if j.val < 32 then 30965760 else (if j.val < 33 then 77414400 else 0))))))) else (if i.val < 32 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 61931520 else 0) else (if j.val < 7 then 132710400 else 0))) else (if j.val < 12 then (if j.val < 10 then (if j.val < 9 then 0 else 30965760) else (if j.val < 11 then 30965760 else 66355200)) else (if j.val < 14 then (if j.val < 13 then 30965760 else 0) else (if j.val < 15 then 97320960 else (if j.val < 16 then 0 else 66355200))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 30965760 else 92897280) else 0) else (if j.val < 23 then (if j.val < 22 then 61931520 else 0) else (if j.val < 24 then 132710400 else 30965760))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 30965760 else 66355200) else (if j.val < 28 then 128286720 else 30965760)) else (if j.val < 31 then (if j.val < 30 then 92897280 else 30965760) else (if j.val < 32 then 163676160 else (if j.val < 33 then 66355200 else 199065600)))))) else (if i.val < 33 then (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 77414400) else (if j.val < 7 then 66355200 else 0))) else (if j.val < 12 then (if j.val < 10 then 0 else (if j.val < 11 then 38707200 else 71884800)) else (if j.val < 14 then (if j.val < 13 then 0 else 38707200) else (if j.val < 15 then 33177600 else (if j.val < 16 then 77414400 else 33177600))))) else (if j.val < 25 then (if j.val < 21 then (if j.val < 19 then (if j.val < 18 then 38707200 else 0) else 0) else (if j.val < 23 then (if j.val < 22 then 0 else 77414400) else (if j.val < 24 then 66355200 else 0))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 38707200 else 71884800) else (if j.val < 28 then 33177600 else 77414400)) else (if j.val < 31 then (if j.val < 30 then 0 else 77414400) else (if j.val < 32 then 66355200 else (if j.val < 33 then 110592000 else 99532800)))))) else (if j.val < 17 then (if j.val < 8 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 199065600 else 0))) else (if j.val < 12 then (if j.val < 10 then 0 else (if j.val < 11 then 0 else 99532800)) else (if j.val < 14 then 0 else (if j.val < 15 then 99532800 else (if j.val < 16 then 0 else 99532800))))) else (if j.val < 25 then (if j.val < 21 then 0 else (if j.val < 23 then 0 else (if j.val < 24 then 199065600 else 0))) else (if j.val < 29 then (if j.val < 27 then (if j.val < 26 then 0 else 99532800) else (if j.val < 28 then 99532800 else 0)) else (if j.val < 31 then 0 else (if j.val < 32 then 199065600 else (if j.val < 33 then 99532800 else 298598400))))))))))))

theorem f412_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 12 f412S4Amplitudes=f412rawS4Form := by
  have hA : natFourIntegerMatrix 1 f412S4GramAInt = f412S4Amplitudes := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix 1 f412S4GramAInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4Amplitudes) 12 j) (by decide +kernel)
      exact h 0 b
  have hW : natFourIntegerMatrix (2^14) f412S4GramWInt = (Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val))) := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 13) => (natFourIntegerMatrix (2^14) f412S4GramWInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 13) => ((Matrix.diagonal (fun p : Fin 13 => natFourPairWeight p.val (12-p.val)))) 12 j) (by decide +kernel)
      exact h 0 b
  have hV : f412S4GramWInt*f412S4GramAInt = f412S4GramVInt := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 7 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 8 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 9 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 10 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 11 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramWInt*f412S4GramAInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramVInt) 12 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f412S4GramAIntᵀ*f412S4GramVInt = f412S4GramYInt := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 7 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 8 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 9 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 10 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 11 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 12 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 13 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 14 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 14 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 15 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 15 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 16 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 16 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 17 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 17 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 18 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 18 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 19 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 19 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 20 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 20 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 21 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 21 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 22 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 22 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 23 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 23 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 24 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 24 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 25 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 25 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 26 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 26 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 27 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 27 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 28 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 28 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 29 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 29 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 30 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 30 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 31 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 31 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 32 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 32 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramAIntᵀ*f412S4GramVInt) 33 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412S4GramYInt) 33 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt = f412rawS4Form := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 13 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 14 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 14 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 15 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 15 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 16 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 16 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 17 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 17 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 18 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 18 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 19 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 19 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 20 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 20 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 21 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 21 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 22 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 22 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 23 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 23 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 24 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 24 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 25 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 25 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 26 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 26 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 27 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 27 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 28 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 28 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 29 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 29 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 30 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 30 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 31 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 31 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 32 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 32 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (natFourIntegerMatrix (1*((2^14)*1)) f412S4GramYInt) 33 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f412rawS4Form) 33 j) (by decide +kernel)
      exact h 0 b
  unfold natFourS4AmplitudeGram
  rw [← hA, ← hW, ← natFourIntegerMatrix_transpose,
    natFourIntegerMatrix_mul, natFourIntegerMatrix_mul, hV, hY]
  exact hF

theorem f412_actual_raw_S4_matrix (x y : Fin 34 → ℂ) :
    natOccupationInner (natFourWordBlock f412basis x)
      (canonicalNatFourS4 (natFourWordBlock f412basis y))=
      star x ⬝ᵥ (complexify f412rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 12 f412basis
    (fun a => (f412hs_shape a).1) (fun a => (f412hs_shape a).2)
    f412S4Amplitudes f412_S4_amplitudes_check f412rawS4Form f412_S4_amplitude_gram_check x y

#print axioms f412_S4_amplitude_gram_check
#print axioms f412_actual_raw_S4_matrix
end TorusLean.BosonFiniteCertificate
