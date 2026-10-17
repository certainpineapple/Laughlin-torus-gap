import torus.shared.BosonFiniteCertificateNatFourHS413S4Amplitudes

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f413hs_shape (a : Fin 39) :
    (f413basis a).length=4 ∧ (f413basis a).sum=13 := by
  apply natFourBasis_shape 13
  rw [← f413_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

private def f413S4GramAInt : Matrix (Fin 14) (Fin 39) ℤ :=
  fun i j => (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 12 else 4) else 4) else (if j.val < 6 then 4 else (if j.val < 7 then 4 else 0))) else 0) else 0) else (if i.val < 2 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 8) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 8 else 4)))) else (if j.val < 14 then (if j.val < 11 then 4 else (if j.val < 12 then 4 else (if j.val < 13 then 4 else 0))) else 0)) else 0) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 8 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 4))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 8))) else (if j.val < 16 then 4 else (if j.val < 17 then 4 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 12 else 4)) else (if j.val < 26 then 4 else 0)) else 0)))) else (if i.val < 5 then (if i.val < 4 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 8)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 0 else 4)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 4 else 0) else 0) else (if j.val < 16 then (if j.val < 15 then 4 else 0) else (if j.val < 17 then 0 else (if j.val < 18 then 8 else 4))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 4 else 0) else (if j.val < 22 then 0 else (if j.val < 23 then 8 else 0))) else (if j.val < 26 then 0 else (if j.val < 27 then 8 else 4))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 4 else 0) else 0) else 0))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 8 else 0) else 0)) else (if j.val < 14 then (if j.val < 11 then 4 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 4))) else (if j.val < 16 then (if j.val < 15 then 0 else 4) else (if j.val < 17 then 0 else (if j.val < 18 then 0 else 4))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 8) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 8))) else (if j.val < 26 then 0 else (if j.val < 27 then 4 else (if j.val < 28 then 4 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 8) else (if j.val < 32 then 4 else (if j.val < 33 then 0 else 12))) else (if j.val < 36 then 4 else 0))))) else (if i.val < 6 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 8) else 0)) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 4) else (if j.val < 12 then 4 else 0)) else (if j.val < 16 then (if j.val < 15 then 4 else 0) else (if j.val < 17 then 4 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 8 else 4) else 0) else (if j.val < 26 then (if j.val < 25 then 8 else 0) else (if j.val < 27 then 0 else 4))) else (if j.val < 34 then (if j.val < 31 then 0 else (if j.val < 32 then 4 else (if j.val < 33 then 12 else 0))) else (if j.val < 36 then (if j.val < 35 then 8 else 0) else (if j.val < 37 then 8 else (if j.val < 38 then 4 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 8 else 0))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 4 else (if j.val < 13 then 8 else 0))) else (if j.val < 16 then (if j.val < 15 then 0 else 4) else 4))) else (if j.val < 29 then (if j.val < 24 then 0 else (if j.val < 26 then (if j.val < 25 then 0 else 8) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 4)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 8 else 4) else (if j.val < 32 then 4 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 8) else (if j.val < 37 then 4 else (if j.val < 38 then 8 else 12))))))))) else (if i.val < 10 then (if i.val < 8 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 8 else 0))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 4 else (if j.val < 13 then 8 else 0))) else (if j.val < 16 then (if j.val < 15 then 0 else 4) else 4))) else (if j.val < 29 then (if j.val < 24 then 0 else (if j.val < 26 then (if j.val < 25 then 0 else 8) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 4)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 8 else 4) else (if j.val < 32 then 4 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 8) else (if j.val < 37 then 4 else (if j.val < 38 then 8 else 12)))))) else (if i.val < 9 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 8) else 0)) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 4) else (if j.val < 12 then 4 else 0)) else (if j.val < 16 then (if j.val < 15 then 4 else 0) else (if j.val < 17 then 4 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 8 else 4) else 0) else (if j.val < 26 then (if j.val < 25 then 8 else 0) else (if j.val < 27 then 0 else 4))) else (if j.val < 34 then (if j.val < 31 then 0 else (if j.val < 32 then 4 else (if j.val < 33 then 12 else 0))) else (if j.val < 36 then (if j.val < 35 then 8 else 0) else (if j.val < 37 then 8 else (if j.val < 38 then 4 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 8 else 0) else 0)) else (if j.val < 14 then (if j.val < 11 then 4 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 4))) else (if j.val < 16 then (if j.val < 15 then 0 else 4) else (if j.val < 17 then 0 else (if j.val < 18 then 0 else 4))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 8) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 8))) else (if j.val < 26 then 0 else (if j.val < 27 then 4 else (if j.val < 28 then 4 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 8) else (if j.val < 32 then 4 else (if j.val < 33 then 0 else 12))) else (if j.val < 36 then 4 else 0)))))) else (if i.val < 12 then (if i.val < 11 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 8)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 0 else 4)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 4 else 0) else 0) else (if j.val < 16 then (if j.val < 15 then 4 else 0) else (if j.val < 17 then 0 else (if j.val < 18 then 8 else 4))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 4 else 0) else (if j.val < 22 then 0 else (if j.val < 23 then 8 else 0))) else (if j.val < 26 then 0 else (if j.val < 27 then 8 else 4))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 4 else 0) else 0) else 0))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 8 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 4))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 8))) else (if j.val < 16 then 4 else (if j.val < 17 then 4 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 12 else 4)) else (if j.val < 26 then 4 else 0)) else 0))) else (if i.val < 13 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 8) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 8 else 4)))) else (if j.val < 14 then (if j.val < 11 then 4 else (if j.val < 12 then 4 else (if j.val < 13 then 4 else 0))) else 0)) else 0) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 12 else 4) else 4) else (if j.val < 6 then 4 else (if j.val < 7 then 4 else 0))) else 0) else 0)))))

private def f413S4GramWInt : Matrix (Fin 14) (Fin 14) ℤ :=
  Matrix.diagonal (fun p : Fin 14 => ((p.val.factorial * (13-p.val).factorial : ℕ) : ℤ))

private def f413S4GramVInt : Matrix (Fin 14) (Fin 39) ℤ :=
  fun i j => (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 74724249600 else 24908083200) else 24908083200) else (if j.val < 6 then 24908083200 else (if j.val < 7 then 24908083200 else 0))) else 0) else 0) else (if i.val < 2 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 3832012800) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 3832012800 else 1916006400)))) else (if j.val < 14 then (if j.val < 11 then 1916006400 else (if j.val < 12 then 1916006400 else (if j.val < 13 then 1916006400 else 0))) else 0)) else 0) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 638668800 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 319334400))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 638668800))) else (if j.val < 16 then 319334400 else (if j.val < 17 then 319334400 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 958003200 else 319334400)) else (if j.val < 26 then 319334400 else 0)) else 0)))) else (if i.val < 5 then (if i.val < 4 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 174182400)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 0 else 87091200)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 87091200 else 0) else 0) else (if j.val < 16 then (if j.val < 15 then 87091200 else 0) else (if j.val < 17 then 0 else (if j.val < 18 then 174182400 else 87091200))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 87091200 else 0) else (if j.val < 22 then 0 else (if j.val < 23 then 174182400 else 0))) else (if j.val < 26 then 0 else (if j.val < 27 then 174182400 else 87091200))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 87091200 else 0) else 0) else 0))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 69672960 else 0) else 0)) else (if j.val < 14 then (if j.val < 11 then 34836480 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 34836480))) else (if j.val < 16 then (if j.val < 15 then 0 else 34836480) else (if j.val < 17 then 0 else (if j.val < 18 then 0 else 34836480))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 69672960) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 69672960))) else (if j.val < 26 then 0 else (if j.val < 27 then 34836480 else (if j.val < 28 then 34836480 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 69672960) else (if j.val < 32 then 34836480 else (if j.val < 33 then 0 else 104509440))) else (if j.val < 36 then 34836480 else 0))))) else (if i.val < 6 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 38707200) else 0)) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 19353600) else (if j.val < 12 then 19353600 else 0)) else (if j.val < 16 then (if j.val < 15 then 19353600 else 0) else (if j.val < 17 then 19353600 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 38707200 else 19353600) else 0) else (if j.val < 26 then (if j.val < 25 then 38707200 else 0) else (if j.val < 27 then 0 else 19353600))) else (if j.val < 34 then (if j.val < 31 then 0 else (if j.val < 32 then 19353600 else (if j.val < 33 then 58060800 else 0))) else (if j.val < 36 then (if j.val < 35 then 38707200 else 0) else (if j.val < 37 then 38707200 else (if j.val < 38 then 19353600 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 29030400 else 0))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 14515200 else (if j.val < 13 then 29030400 else 0))) else (if j.val < 16 then (if j.val < 15 then 0 else 14515200) else 14515200))) else (if j.val < 29 then (if j.val < 24 then 0 else (if j.val < 26 then (if j.val < 25 then 0 else 29030400) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 14515200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 29030400 else 14515200) else (if j.val < 32 then 14515200 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 29030400) else (if j.val < 37 then 14515200 else (if j.val < 38 then 29030400 else 43545600))))))))) else (if i.val < 10 then (if i.val < 8 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 29030400 else 0))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 14515200 else (if j.val < 13 then 29030400 else 0))) else (if j.val < 16 then (if j.val < 15 then 0 else 14515200) else 14515200))) else (if j.val < 29 then (if j.val < 24 then 0 else (if j.val < 26 then (if j.val < 25 then 0 else 29030400) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 14515200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 29030400 else 14515200) else (if j.val < 32 then 14515200 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 29030400) else (if j.val < 37 then 14515200 else (if j.val < 38 then 29030400 else 43545600)))))) else (if i.val < 9 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 38707200) else 0)) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 19353600) else (if j.val < 12 then 19353600 else 0)) else (if j.val < 16 then (if j.val < 15 then 19353600 else 0) else (if j.val < 17 then 19353600 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 38707200 else 19353600) else 0) else (if j.val < 26 then (if j.val < 25 then 38707200 else 0) else (if j.val < 27 then 0 else 19353600))) else (if j.val < 34 then (if j.val < 31 then 0 else (if j.val < 32 then 19353600 else (if j.val < 33 then 58060800 else 0))) else (if j.val < 36 then (if j.val < 35 then 38707200 else 0) else (if j.val < 37 then 38707200 else (if j.val < 38 then 19353600 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 69672960 else 0) else 0)) else (if j.val < 14 then (if j.val < 11 then 34836480 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 34836480))) else (if j.val < 16 then (if j.val < 15 then 0 else 34836480) else (if j.val < 17 then 0 else (if j.val < 18 then 0 else 34836480))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 69672960) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 69672960))) else (if j.val < 26 then 0 else (if j.val < 27 then 34836480 else (if j.val < 28 then 34836480 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 69672960) else (if j.val < 32 then 34836480 else (if j.val < 33 then 0 else 104509440))) else (if j.val < 36 then 34836480 else 0)))))) else (if i.val < 12 then (if i.val < 11 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 174182400)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 0 else 87091200)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 87091200 else 0) else 0) else (if j.val < 16 then (if j.val < 15 then 87091200 else 0) else (if j.val < 17 then 0 else (if j.val < 18 then 174182400 else 87091200))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 87091200 else 0) else (if j.val < 22 then 0 else (if j.val < 23 then 174182400 else 0))) else (if j.val < 26 then 0 else (if j.val < 27 then 174182400 else 87091200))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 87091200 else 0) else 0) else 0))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 638668800 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 319334400))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 638668800))) else (if j.val < 16 then 319334400 else (if j.val < 17 then 319334400 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 958003200 else 319334400)) else (if j.val < 26 then 319334400 else 0)) else 0))) else (if i.val < 13 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 3832012800) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 3832012800 else 1916006400)))) else (if j.val < 14 then (if j.val < 11 then 1916006400 else (if j.val < 12 then 1916006400 else (if j.val < 13 then 1916006400 else 0))) else 0)) else 0) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 74724249600 else 24908083200) else 24908083200) else (if j.val < 6 then 24908083200 else (if j.val < 7 then 24908083200 else 0))) else 0) else 0)))))

private def f413S4GramYInt : Matrix (Fin 39) (Fin 39) ℤ :=
  fun i j => (if i.val < 19 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 1793381990400 else 597793996800) else 597793996800) else (if j.val < 6 then 597793996800 else (if j.val < 7 then 597793996800 else 0))) else 0) else 0) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 597793996800 else 260576870400) else 199264665600) else (if j.val < 6 then 199264665600 else (if j.val < 7 then 199264665600 else (if j.val < 8 then 61312204800 else 30656102400)))) else (if j.val < 14 then (if j.val < 11 then 30656102400 else (if j.val < 12 then 30656102400 else (if j.val < 13 then 30656102400 else 0))) else 0)) else 0)) else (if i.val < 3 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 597793996800 else 199264665600) else (if j.val < 3 then 209483366400 else 199264665600)) else (if j.val < 6 then 199264665600 else (if j.val < 7 then 199264665600 else 5109350400))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 10218700800))) else (if j.val < 16 then 5109350400 else (if j.val < 17 then 5109350400 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 15328051200 else 5109350400)) else (if j.val < 26 then 5109350400 else 0)) else 0)) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 597793996800 else 199264665600) else (if j.val < 3 then 199264665600 else 202051584000)) else (if j.val < 6 then 199264665600 else (if j.val < 7 then 199264665600 else (if j.val < 8 then 0 else 1393459200)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 1393459200 else 0) else 0) else (if j.val < 16 then (if j.val < 15 then 1393459200 else 0) else (if j.val < 17 then 0 else (if j.val < 18 then 2786918400 else 1393459200))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1393459200 else 0) else (if j.val < 22 then 0 else (if j.val < 23 then 2786918400 else 0))) else (if j.val < 26 then 0 else (if j.val < 27 then 2786918400 else 1393459200))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 1393459200 else 0) else 0) else 0))))) else (if i.val < 6 then (if i.val < 5 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 597793996800 else 199264665600) else 199264665600) else (if j.val < 6 then (if j.val < 5 then 200379432960 else 199264665600) else (if j.val < 7 then 199264665600 else 0))) else (if j.val < 14 then (if j.val < 11 then 557383680 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 557383680))) else (if j.val < 16 then (if j.val < 15 then 0 else 557383680) else (if j.val < 17 then 0 else (if j.val < 18 then 0 else 557383680))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 1114767360) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 1114767360))) else (if j.val < 26 then 0 else (if j.val < 27 then 557383680 else (if j.val < 28 then 557383680 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 1114767360) else (if j.val < 32 then 557383680 else (if j.val < 33 then 0 else 1672151040))) else (if j.val < 36 then 557383680 else 0)))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 597793996800 else 199264665600) else 199264665600) else (if j.val < 6 then (if j.val < 5 then 199264665600 else 199883980800) else (if j.val < 7 then 199264665600 else 0))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 309657600) else (if j.val < 12 then 309657600 else 0)) else (if j.val < 16 then (if j.val < 15 then 309657600 else 0) else (if j.val < 17 then 309657600 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 619315200 else 309657600) else 0) else (if j.val < 26 then (if j.val < 25 then 619315200 else 0) else (if j.val < 27 then 0 else 309657600))) else (if j.val < 34 then (if j.val < 31 then 0 else (if j.val < 32 then 309657600 else (if j.val < 33 then 928972800 else 0))) else (if j.val < 36 then (if j.val < 35 then 619315200 else 0) else (if j.val < 37 then 619315200 else (if j.val < 38 then 309657600 else 0))))))) else (if i.val < 7 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 597793996800 else 199264665600) else 199264665600) else (if j.val < 6 then 199264665600 else (if j.val < 7 then 199729152000 else 0))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 232243200 else (if j.val < 13 then 464486400 else 0))) else (if j.val < 16 then (if j.val < 15 then 0 else 232243200) else 232243200))) else (if j.val < 29 then (if j.val < 24 then 0 else (if j.val < 26 then (if j.val < 25 then 0 else 464486400) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 232243200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 464486400 else 232243200) else (if j.val < 32 then 232243200 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 464486400) else (if j.val < 37 then 232243200 else (if j.val < 38 then 464486400 else 696729600)))))) else (if i.val < 8 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 61312204800) else (if j.val < 3 then 5109350400 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 63866880000 else 33210777600)))) else (if j.val < 14 then (if j.val < 11 then 30656102400 else (if j.val < 12 then 30656102400 else (if j.val < 13 then 30656102400 else 5109350400))) else (if j.val < 16 then 2554675200 else (if j.val < 17 then 2554675200 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 7664025600 else 2554675200)) else (if j.val < 26 then 2554675200 else 0)) else 0)) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 30656102400) else (if j.val < 3 then 5109350400 else 1393459200)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 33210777600 else 18579456000)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 16024780800 else 15328051200) else (if j.val < 12 then 15328051200 else (if j.val < 13 then 15328051200 else 5109350400))) else (if j.val < 16 then (if j.val < 15 then 3251404800 else 2554675200) else (if j.val < 17 then 2554675200 else (if j.val < 18 then 1393459200 else 696729600))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 696729600 else 0) else (if j.val < 22 then 7664025600 else (if j.val < 23 then 3948134400 else 2554675200))) else (if j.val < 26 then 2554675200 else (if j.val < 27 then 1393459200 else 696729600))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 696729600 else 0) else 0) else 0))))))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 30656102400) else (if j.val < 3 then 0 else 1393459200)) else (if j.val < 6 then (if j.val < 5 then 557383680 else 0) else (if j.val < 7 then 0 else (if j.val < 8 then 30656102400 else 16024780800)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 16303472640 else 15606743040) else (if j.val < 12 then 15328051200 else (if j.val < 13 then 15328051200 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 696729600 else 278691840) else (if j.val < 17 then 0 else (if j.val < 18 then 1393459200 else 975421440))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 696729600 else 557383680) else (if j.val < 22 then 0 else (if j.val < 23 then 1393459200 else 557383680))) else (if j.val < 26 then 0 else (if j.val < 27 then 1672151040 else (if j.val < 28 then 975421440 else 696729600)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 696729600 else 557383680) else (if j.val < 32 then 278691840 else (if j.val < 33 then 0 else 836075520))) else (if j.val < 36 then 278691840 else 0)))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 30656102400) else 0) else (if j.val < 6 then (if j.val < 5 then 557383680 else 309657600) else (if j.val < 7 then 0 else (if j.val < 8 then 30656102400 else 15328051200)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 15606743040 else 15761571840) else (if j.val < 12 then 15482880000 else (if j.val < 13 then 15328051200 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 154828800 else 278691840) else (if j.val < 17 then 154828800 else (if j.val < 18 then 0 else 278691840))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 309657600 else 712212480) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 557383680))) else (if j.val < 26 then (if j.val < 25 then 309657600 else 0) else (if j.val < 27 then 278691840 else (if j.val < 28 then 433520640 else 154828800)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 557383680) else (if j.val < 32 then 433520640 else (if j.val < 33 then 464486400 else 836075520))) else (if j.val < 36 then (if j.val < 35 then 588349440 else 278691840) else (if j.val < 37 then 309657600 else (if j.val < 38 then 154828800 else 0))))))) else (if i.val < 12 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 30656102400) else 0) else (if j.val < 6 then (if j.val < 5 then 0 else 309657600) else (if j.val < 7 then 232243200 else (if j.val < 8 then 30656102400 else 15328051200)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 15328051200 else 15482880000) else (if j.val < 12 then 15599001600 else (if j.val < 13 then 15560294400 else 0))) else (if j.val < 16 then (if j.val < 15 then 154828800 else 116121600) else (if j.val < 17 then 270950400 else 116121600)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 309657600 else 154828800) else 0) else (if j.val < 26 then (if j.val < 25 then 309657600 else 232243200) else (if j.val < 27 then 0 else (if j.val < 28 then 154828800 else 270950400)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 232243200 else 116121600) else (if j.val < 32 then 270950400 else (if j.val < 33 then 464486400 else 0))) else (if j.val < 36 then (if j.val < 35 then 309657600 else 232243200) else (if j.val < 37 then 425779200 else (if j.val < 38 then 387072000 else 348364800)))))) else (if i.val < 13 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 0 else 30656102400) else 0) else (if j.val < 6 then 0 else (if j.val < 7 then 464486400 else (if j.val < 8 then 30656102400 else 15328051200)))) else (if j.val < 14 then (if j.val < 11 then 15328051200 else (if j.val < 12 then 15560294400 else (if j.val < 13 then 15792537600 else 0))) else (if j.val < 16 then (if j.val < 15 then 0 else 232243200) else 232243200))) else (if j.val < 29 then (if j.val < 24 then 0 else (if j.val < 26 then (if j.val < 25 then 0 else 464486400) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 232243200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 464486400 else 232243200) else (if j.val < 32 then 232243200 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 464486400) else (if j.val < 37 then 232243200 else (if j.val < 38 then 464486400 else 696729600)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 10218700800 else 0)) else (if j.val < 6 then (if j.val < 5 then 557383680 else 0) else (if j.val < 7 then 0 else 5109350400))) else (if j.val < 14 then (if j.val < 11 then 278691840 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 10497392640))) else (if j.val < 16 then (if j.val < 15 then 5109350400 else 5388042240) else (if j.val < 17 then 5109350400 else (if j.val < 18 then 0 else 278691840))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 557383680) else (if j.val < 22 then 15328051200 else (if j.val < 23 then 5109350400 else 5666734080))) else (if j.val < 26 then 5109350400 else (if j.val < 27 then 278691840 else (if j.val < 28 then 278691840 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 557383680) else (if j.val < 32 then 278691840 else (if j.val < 33 then 0 else 836075520))) else (if j.val < 36 then 278691840 else 0))))))) else (if i.val < 16 then (if i.val < 15 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 5109350400 else 1393459200)) else (if j.val < 6 then (if j.val < 5 then 0 else 309657600) else (if j.val < 7 then 0 else (if j.val < 8 then 2554675200 else 3251404800)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 696729600 else 154828800) else (if j.val < 12 then 154828800 else (if j.val < 13 then 0 else 5109350400))) else (if j.val < 16 then (if j.val < 15 then 3406233600 else 2554675200) else (if j.val < 17 then 2709504000 else (if j.val < 18 then 1393459200 else 696729600))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1006387200 else 154828800) else (if j.val < 22 then 7664025600 else (if j.val < 23 then 3948134400 else 2554675200))) else (if j.val < 26 then (if j.val < 25 then 2864332800 else 2554675200) else (if j.val < 27 then 1393459200 else 851558400))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 696729600 else 0) else (if j.val < 32 then 154828800 else (if j.val < 33 then 464486400 else 0))) else (if j.val < 36 then (if j.val < 35 then 309657600 else 0) else (if j.val < 37 then 309657600 else (if j.val < 38 then 154828800 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 5109350400 else 0)) else (if j.val < 6 then (if j.val < 5 then 557383680 else 0) else (if j.val < 7 then 232243200 else 2554675200))) else (if j.val < 14 then (if j.val < 11 then 278691840 else (if j.val < 12 then 116121600 else (if j.val < 13 then 232243200 else 5388042240))) else (if j.val < 16 then (if j.val < 15 then 2554675200 else 2949488640) else (if j.val < 17 then 2670796800 else (if j.val < 18 then 116121600 else 394813440))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 557383680) else (if j.val < 22 then 7664025600 else (if j.val < 23 then 2554675200 else 3112058880))) else (if j.val < 26 then (if j.val < 25 then 2554675200 else 2786918400) else (if j.val < 27 then 278691840 else (if j.val < 28 then 278691840 else 116121600)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 232243200 else 673505280) else (if j.val < 32 then 394813440 else (if j.val < 33 then 0 else 836075520))) else (if j.val < 36 then (if j.val < 35 then 278691840 else 510935040) else (if j.val < 37 then 116121600 else (if j.val < 38 then 232243200 else 348364800))))))) else (if i.val < 17 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 5109350400 else 0)) else (if j.val < 6 then (if j.val < 5 then 0 else 309657600) else (if j.val < 7 then 232243200 else 2554675200))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 154828800) else (if j.val < 12 then 270950400 else (if j.val < 13 then 232243200 else 5109350400))) else (if j.val < 16 then (if j.val < 15 then 2709504000 else 2670796800) else (if j.val < 17 then 2825625600 else 116121600)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 309657600 else 154828800) else (if j.val < 22 then 7664025600 else 2554675200)) else (if j.val < 26 then (if j.val < 25 then 2864332800 else 2786918400) else (if j.val < 27 then 0 else (if j.val < 28 then 154828800 else 270950400)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 232243200 else 116121600) else (if j.val < 32 then 270950400 else (if j.val < 33 then 464486400 else 0))) else (if j.val < 36 then (if j.val < 35 then 309657600 else 232243200) else (if j.val < 37 then 425779200 else (if j.val < 38 then 387072000 else 348364800)))))) else (if i.val < 18 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 2786918400)) else (if j.val < 6 then 0 else (if j.val < 7 then 232243200 else (if j.val < 8 then 0 else 1393459200)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 1393459200 else 0) else (if j.val < 12 then 116121600 else (if j.val < 13 then 232243200 else 0))) else (if j.val < 16 then (if j.val < 15 then 1393459200 else 116121600) else (if j.val < 17 then 116121600 else (if j.val < 18 then 2903040000 else 1509580800))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1393459200 else 0) else (if j.val < 22 then 0 else (if j.val < 23 then 2786918400 else 0))) else (if j.val < 26 then (if j.val < 25 then 0 else 232243200) else (if j.val < 27 then 2786918400 else (if j.val < 28 then 1393459200 else 1509580800)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 1625702400 else 116121600) else (if j.val < 32 then 116121600 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 232243200) else (if j.val < 37 then 116121600 else (if j.val < 38 then 232243200 else 348364800)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 1393459200)) else (if j.val < 6 then (if j.val < 5 then 557383680 else 0) else (if j.val < 7 then 232243200 else (if j.val < 8 then 0 else 696729600)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 975421440 else 278691840) else (if j.val < 12 then 116121600 else (if j.val < 13 then 232243200 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 696729600 else 394813440) else (if j.val < 17 then 116121600 else (if j.val < 18 then 1509580800 else 1091543040))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 696729600 else 557383680) else (if j.val < 22 then 0 else (if j.val < 23 then 1393459200 else 557383680))) else (if j.val < 26 then (if j.val < 25 then 0 else 232243200) else (if j.val < 27 then 1672151040 else (if j.val < 28 then 975421440 else 812851200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 928972800 else 673505280) else (if j.val < 32 then 394813440 else (if j.val < 33 then 0 else 836075520))) else (if j.val < 36 then (if j.val < 35 then 278691840 else 510935040) else (if j.val < 37 then 116121600 else (if j.val < 38 then 232243200 else 348364800))))))))))) else (if i.val < 29 then (if i.val < 24 then (if i.val < 21 then (if i.val < 20 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 1393459200)) else (if j.val < 6 then (if j.val < 5 then 0 else 619315200) else (if j.val < 7 then 0 else (if j.val < 8 then 0 else 696729600)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 696729600 else 309657600) else (if j.val < 12 then 309657600 else 0)) else (if j.val < 16 then (if j.val < 15 then 1006387200 else 0) else (if j.val < 17 then 309657600 else (if j.val < 18 then 1393459200 else 696729600))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1316044800 else 309657600) else (if j.val < 22 then 0 else (if j.val < 23 then 1393459200 else 0))) else (if j.val < 26 then (if j.val < 25 then 619315200 else 0) else (if j.val < 27 then 1393459200 else 1006387200))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 696729600 else 0) else (if j.val < 32 then 309657600 else (if j.val < 33 then 928972800 else 0))) else (if j.val < 36 then (if j.val < 35 then 619315200 else 0) else (if j.val < 37 then 619315200 else (if j.val < 38 then 309657600 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 1114767360 else 309657600) else 0)) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 557383680 else 712212480) else (if j.val < 12 then 154828800 else (if j.val < 13 then 0 else 557383680))) else (if j.val < 16 then (if j.val < 15 then 154828800 else 557383680) else (if j.val < 17 then 154828800 else (if j.val < 18 then 0 else 557383680))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 309657600 else 1269596160) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 1114767360))) else (if j.val < 26 then (if j.val < 25 then 309657600 else 0) else (if j.val < 27 then 557383680 else (if j.val < 28 then 712212480 else 154828800)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 1114767360) else (if j.val < 32 then 712212480 else (if j.val < 33 then 464486400 else 1672151040))) else (if j.val < 36 then (if j.val < 35 then 867041280 else 557383680) else (if j.val < 37 then 309657600 else (if j.val < 38 then 154828800 else 0))))))) else (if i.val < 22 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 15328051200 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else 7664025600))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 15328051200))) else (if j.val < 16 then 7664025600 else (if j.val < 17 then 7664025600 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 22992076800 else 7664025600)) else (if j.val < 26 then 7664025600 else 0)) else 0)) else (if i.val < 23 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 5109350400 else 2786918400)) else (if j.val < 6 then 0 else (if j.val < 7 then 0 else (if j.val < 8 then 2554675200 else 3948134400)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 1393459200 else 0) else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 5109350400))) else (if j.val < 16 then (if j.val < 15 then 3948134400 else 2554675200) else (if j.val < 17 then 2554675200 else (if j.val < 18 then 2786918400 else 1393459200))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1393459200 else 0) else (if j.val < 22 then 7664025600 else (if j.val < 23 then 5341593600 else 2554675200))) else (if j.val < 26 then 2554675200 else (if j.val < 27 then 2786918400 else 1393459200))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 1393459200 else 0) else 0) else 0))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 5109350400 else 0)) else (if j.val < 6 then (if j.val < 5 then 1114767360 else 0) else (if j.val < 7 then 0 else 2554675200))) else (if j.val < 14 then (if j.val < 11 then 557383680 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 5666734080))) else (if j.val < 16 then (if j.val < 15 then 2554675200 else 3112058880) else (if j.val < 17 then 2554675200 else (if j.val < 18 then 0 else 557383680))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 1114767360) else (if j.val < 22 then 7664025600 else (if j.val < 23 then 2554675200 else 3669442560))) else (if j.val < 26 then 2554675200 else (if j.val < 27 then 557383680 else (if j.val < 28 then 557383680 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 1114767360) else (if j.val < 32 then 557383680 else (if j.val < 33 then 0 else 1672151040))) else (if j.val < 36 then 557383680 else 0))))))) else (if i.val < 26 then (if i.val < 25 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 5109350400 else 0)) else (if j.val < 6 then (if j.val < 5 then 0 else 619315200) else (if j.val < 7 then 0 else 2554675200))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 309657600) else (if j.val < 12 then 309657600 else (if j.val < 13 then 0 else 5109350400))) else (if j.val < 16 then (if j.val < 15 then 2864332800 else 2554675200) else (if j.val < 17 then 2864332800 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 619315200 else 309657600) else (if j.val < 22 then 7664025600 else 2554675200)) else (if j.val < 26 then (if j.val < 25 then 3173990400 else 2554675200) else (if j.val < 27 then 0 else 309657600))) else (if j.val < 34 then (if j.val < 31 then 0 else (if j.val < 32 then 309657600 else (if j.val < 33 then 928972800 else 0))) else (if j.val < 36 then (if j.val < 35 then 619315200 else 0) else (if j.val < 37 then 619315200 else (if j.val < 38 then 309657600 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 5109350400 else 0)) else (if j.val < 6 then 0 else (if j.val < 7 then 464486400 else 2554675200))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 232243200 else (if j.val < 13 then 464486400 else 5109350400))) else (if j.val < 16 then (if j.val < 15 then 2554675200 else 2786918400) else (if j.val < 17 then 2786918400 else 232243200)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then 0 else (if j.val < 22 then 7664025600 else 2554675200)) else (if j.val < 26 then (if j.val < 25 then 2554675200 else 3019161600) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 232243200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 464486400 else 232243200) else (if j.val < 32 then 232243200 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 464486400) else (if j.val < 37 then 232243200 else (if j.val < 38 then 464486400 else 696729600))))))) else (if i.val < 27 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 2786918400)) else (if j.val < 6 then (if j.val < 5 then 557383680 else 0) else (if j.val < 7 then 0 else (if j.val < 8 then 0 else 1393459200)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 1672151040 else 278691840) else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 1393459200 else 278691840) else (if j.val < 17 then 0 else (if j.val < 18 then 2786918400 else 1672151040))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1393459200 else 557383680) else (if j.val < 22 then 0 else (if j.val < 23 then 2786918400 else 557383680))) else (if j.val < 26 then 0 else (if j.val < 27 then 3065610240 else (if j.val < 28 then 1672151040 else 1393459200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 1393459200 else 557383680) else (if j.val < 32 then 278691840 else (if j.val < 33 then 0 else 836075520))) else (if j.val < 36 then 278691840 else 0)))) else (if i.val < 28 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 1393459200)) else (if j.val < 6 then (if j.val < 5 then 557383680 else 309657600) else (if j.val < 7 then 0 else (if j.val < 8 then 0 else 696729600)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 975421440 else 433520640) else (if j.val < 12 then 154828800 else (if j.val < 13 then 0 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 851558400 else 278691840) else (if j.val < 17 then 154828800 else (if j.val < 18 then 1393459200 else 975421440))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1006387200 else 712212480) else (if j.val < 22 then 0 else (if j.val < 23 then 1393459200 else 557383680))) else (if j.val < 26 then (if j.val < 25 then 309657600 else 0) else (if j.val < 27 then 1672151040 else (if j.val < 28 then 1130250240 else 851558400)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 696729600 else 557383680) else (if j.val < 32 then 433520640 else (if j.val < 33 then 464486400 else 836075520))) else (if j.val < 36 then (if j.val < 35 then 588349440 else 278691840) else (if j.val < 37 then 309657600 else (if j.val < 38 then 154828800 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 1393459200)) else (if j.val < 6 then (if j.val < 5 then 0 else 309657600) else (if j.val < 7 then 232243200 else (if j.val < 8 then 0 else 696729600)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 696729600 else 154828800) else (if j.val < 12 then 270950400 else (if j.val < 13 then 232243200 else 0))) else (if j.val < 16 then (if j.val < 15 then 851558400 else 116121600) else (if j.val < 17 then 270950400 else (if j.val < 18 then 1509580800 else 812851200))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 1006387200 else 154828800) else (if j.val < 22 then 0 else (if j.val < 23 then 1393459200 else 0))) else (if j.val < 26 then (if j.val < 25 then 309657600 else 232243200) else (if j.val < 27 then 1393459200 else (if j.val < 28 then 851558400 else 967680000)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 928972800 else 116121600) else (if j.val < 32 then 270950400 else (if j.val < 33 then 464486400 else 0))) else (if j.val < 36 then (if j.val < 35 then 309657600 else 232243200) else (if j.val < 37 then 425779200 else (if j.val < 38 then 387072000 else 348364800)))))))))) else (if i.val < 34 then (if i.val < 31 then (if i.val < 30 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then 0 else (if j.val < 3 then 0 else 1393459200)) else (if j.val < 6 then 0 else (if j.val < 7 then 464486400 else (if j.val < 8 then 0 else 696729600)))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 696729600 else 0) else (if j.val < 12 then 232243200 else (if j.val < 13 then 464486400 else 0))) else (if j.val < 16 then (if j.val < 15 then 696729600 else 232243200) else (if j.val < 17 then 232243200 else (if j.val < 18 then 1625702400 else 928972800))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 696729600 else 0) else (if j.val < 22 then 0 else (if j.val < 23 then 1393459200 else 0))) else (if j.val < 26 then (if j.val < 25 then 0 else 464486400) else (if j.val < 27 then 1393459200 else (if j.val < 28 then 696729600 else 928972800)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 1161216000 else 232243200) else (if j.val < 32 then 232243200 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 464486400) else (if j.val < 37 then 232243200 else (if j.val < 38 then 464486400 else 696729600)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 1114767360 else 0) else (if j.val < 7 then 232243200 else 0))) else (if j.val < 14 then (if j.val < 11 then 557383680 else (if j.val < 12 then 116121600 else (if j.val < 13 then 232243200 else 557383680))) else (if j.val < 16 then (if j.val < 15 then 0 else 673505280) else (if j.val < 17 then 116121600 else (if j.val < 18 then 116121600 else 673505280))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 1114767360) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 1114767360))) else (if j.val < 26 then (if j.val < 25 then 0 else 232243200) else (if j.val < 27 then 557383680 else (if j.val < 28 then 557383680 else 116121600)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 232243200 else 1230888960) else (if j.val < 32 then 673505280 else (if j.val < 33 then 0 else 1672151040))) else (if j.val < 36 then (if j.val < 35 then 557383680 else 789626880) else (if j.val < 37 then 116121600 else (if j.val < 38 then 232243200 else 348364800))))))) else (if i.val < 32 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 557383680 else 309657600) else (if j.val < 7 then 232243200 else 0))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 278691840 else 433520640) else (if j.val < 12 then 270950400 else (if j.val < 13 then 232243200 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 154828800 else 394813440) else (if j.val < 17 then 270950400 else (if j.val < 18 then 116121600 else 394813440))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 309657600 else 712212480) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 557383680))) else (if j.val < 26 then (if j.val < 25 then 309657600 else 232243200) else (if j.val < 27 then 278691840 else (if j.val < 28 then 433520640 else 270950400)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 232243200 else 673505280) else (if j.val < 32 then 549642240 else (if j.val < 33 then 464486400 else 836075520))) else (if j.val < 36 then (if j.val < 35 then 588349440 else 510935040) else (if j.val < 37 then 425779200 else (if j.val < 38 then 387072000 else 348364800)))))) else (if i.val < 33 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 928972800) else 0)) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 464486400) else (if j.val < 12 then 464486400 else 0)) else (if j.val < 16 then (if j.val < 15 then 464486400 else 0) else (if j.val < 17 then 464486400 else 0)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 928972800 else 464486400) else 0) else (if j.val < 26 then (if j.val < 25 then 928972800 else 0) else (if j.val < 27 then 0 else 464486400))) else (if j.val < 34 then (if j.val < 31 then 0 else (if j.val < 32 then 464486400 else (if j.val < 33 then 1393459200 else 0))) else (if j.val < 36 then (if j.val < 35 then 928972800 else 0) else (if j.val < 37 then 928972800 else (if j.val < 38 then 464486400 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 1672151040 else 0) else 0)) else (if j.val < 14 then (if j.val < 11 then 836075520 else (if j.val < 12 then 0 else (if j.val < 13 then 0 else 836075520))) else (if j.val < 16 then (if j.val < 15 then 0 else 836075520) else (if j.val < 17 then 0 else (if j.val < 18 then 0 else 836075520))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 1672151040) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 1672151040))) else (if j.val < 26 then 0 else (if j.val < 27 then 836075520 else (if j.val < 28 then 836075520 else 0)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 1672151040) else (if j.val < 32 then 836075520 else (if j.val < 33 then 0 else 2508226560))) else (if j.val < 36 then 836075520 else 0))))))) else (if i.val < 36 then (if i.val < 35 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 557383680 else 619315200) else 0)) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 278691840 else 588349440) else (if j.val < 12 then 309657600 else (if j.val < 13 then 0 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 309657600 else 278691840) else (if j.val < 17 then 309657600 else (if j.val < 18 then 0 else 278691840))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 619315200 else 867041280) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 557383680))) else (if j.val < 26 then (if j.val < 25 then 619315200 else 0) else (if j.val < 27 then 278691840 else (if j.val < 28 then 588349440 else 309657600)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 0 else 557383680) else (if j.val < 32 then 588349440 else (if j.val < 33 then 928972800 else 836075520))) else (if j.val < 36 then (if j.val < 35 then 898007040 else 278691840) else (if j.val < 37 then 619315200 else (if j.val < 38 then 309657600 else 0)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 557383680 else 0) else (if j.val < 7 then 464486400 else 0))) else (if j.val < 14 then (if j.val < 11 then 278691840 else (if j.val < 12 then 232243200 else (if j.val < 13 then 464486400 else 278691840))) else (if j.val < 16 then (if j.val < 15 then 0 else 510935040) else (if j.val < 17 then 232243200 else (if j.val < 18 then 232243200 else 510935040))))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 0 else 557383680) else (if j.val < 22 then 0 else (if j.val < 23 then 0 else 557383680))) else (if j.val < 26 then (if j.val < 25 then 0 else 464486400) else (if j.val < 27 then 278691840 else (if j.val < 28 then 278691840 else 232243200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 464486400 else 789626880) else (if j.val < 32 then 510935040 else (if j.val < 33 then 0 else 836075520))) else (if j.val < 36 then (if j.val < 35 then 278691840 else 743178240) else (if j.val < 37 then 232243200 else (if j.val < 38 then 464486400 else 696729600))))))) else (if i.val < 37 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 619315200) else (if j.val < 7 then 232243200 else 0))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 309657600) else (if j.val < 12 then 425779200 else (if j.val < 13 then 232243200 else 0))) else (if j.val < 16 then (if j.val < 15 then 309657600 else 116121600) else (if j.val < 17 then 425779200 else 116121600)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 619315200 else 309657600) else 0) else (if j.val < 26 then (if j.val < 25 then 619315200 else 232243200) else (if j.val < 27 then 0 else (if j.val < 28 then 309657600 else 425779200)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 232243200 else 116121600) else (if j.val < 32 then 425779200 else (if j.val < 33 then 928972800 else 0))) else (if j.val < 36 then (if j.val < 35 then 619315200 else 232243200) else (if j.val < 37 then 735436800 else (if j.val < 38 then 541900800 else 348364800)))))) else (if i.val < 38 then (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then (if j.val < 5 then 0 else 309657600) else (if j.val < 7 then 464486400 else 0))) else (if j.val < 14 then (if j.val < 11 then (if j.val < 10 then 0 else 154828800) else (if j.val < 12 then 387072000 else (if j.val < 13 then 464486400 else 0))) else (if j.val < 16 then (if j.val < 15 then 154828800 else 232243200) else (if j.val < 17 then 387072000 else 232243200)))) else (if j.val < 29 then (if j.val < 24 then (if j.val < 21 then (if j.val < 20 then 309657600 else 154828800) else 0) else (if j.val < 26 then (if j.val < 25 then 309657600 else 464486400) else (if j.val < 27 then 0 else (if j.val < 28 then 154828800 else 387072000)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 464486400 else 232243200) else (if j.val < 32 then 387072000 else (if j.val < 33 then 464486400 else 0))) else (if j.val < 36 then (if j.val < 35 then 309657600 else 464486400) else (if j.val < 37 then 541900800 else (if j.val < 38 then 619315200 else 696729600)))))) else (if j.val < 19 then (if j.val < 9 then (if j.val < 4 then 0 else (if j.val < 6 then 0 else (if j.val < 7 then 696729600 else 0))) else (if j.val < 14 then (if j.val < 11 then 0 else (if j.val < 12 then 348364800 else (if j.val < 13 then 696729600 else 0))) else (if j.val < 16 then (if j.val < 15 then 0 else 348364800) else 348364800))) else (if j.val < 29 then (if j.val < 24 then 0 else (if j.val < 26 then (if j.val < 25 then 0 else 696729600) else (if j.val < 27 then 0 else (if j.val < 28 then 0 else 348364800)))) else (if j.val < 34 then (if j.val < 31 then (if j.val < 30 then 696729600 else 348364800) else (if j.val < 32 then 348364800 else 0)) else (if j.val < 36 then (if j.val < 35 then 0 else 696729600) else (if j.val < 37 then 348364800 else (if j.val < 38 then 696729600 else 1045094400))))))))))))

theorem f413_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 13 f413S4Amplitudes=f413rawS4Form := by
  have hA : natFourIntegerMatrix 1 f413S4GramAInt = f413S4Amplitudes := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 1 f413S4GramAInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4Amplitudes) 13 j) (by decide +kernel)
      exact h 0 b
  have hW : natFourIntegerMatrix (2^15) f413S4GramWInt = (Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val))) := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 14) => (natFourIntegerMatrix (2^15) f413S4GramWInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 14) => ((Matrix.diagonal (fun p : Fin 14 => natFourPairWeight p.val (13-p.val)))) 13 j) (by decide +kernel)
      exact h 0 b
  have hV : f413S4GramWInt*f413S4GramAInt = f413S4GramVInt := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 7 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 8 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 9 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 10 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 11 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 12 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramWInt*f413S4GramAInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramVInt) 13 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f413S4GramAIntᵀ*f413S4GramVInt = f413S4GramYInt := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 7 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 8 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 9 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 10 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 11 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 12 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 13 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 14 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 14 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 15 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 15 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 16 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 16 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 17 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 17 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 18 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 18 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 19 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 19 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 20 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 20 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 21 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 21 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 22 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 22 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 23 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 23 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 24 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 24 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 25 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 25 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 26 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 26 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 27 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 27 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 28 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 28 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 29 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 29 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 30 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 30 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 31 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 31 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 32 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 32 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 33 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 33 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 34 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 34 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 35 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 35 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 36 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 36 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 37 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 37 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramAIntᵀ*f413S4GramVInt) 38 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413S4GramYInt) 38 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt = f413rawS4Form := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 13 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 14 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 14 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 15 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 15 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 16 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 16 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 17 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 17 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 18 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 18 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 19 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 19 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 20 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 20 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 21 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 21 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 22 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 22 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 23 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 23 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 24 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 24 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 25 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 25 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 26 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 26 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 27 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 27 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 28 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 28 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 29 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 29 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 30 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 30 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 31 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 31 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 32 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 32 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 33 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 33 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 34 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 34 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 35 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 35 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 36 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 36 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 37 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 37 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix (1*((2^15)*1)) f413S4GramYInt) 38 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 38 j) (by decide +kernel)
      exact h 0 b
  unfold natFourS4AmplitudeGram
  rw [← hA, ← hW, ← natFourIntegerMatrix_transpose,
    natFourIntegerMatrix_mul, natFourIntegerMatrix_mul, hV, hY]
  exact hF

theorem f413_actual_raw_S4_matrix (x y : Fin 39 → ℂ) :
    natOccupationInner (natFourWordBlock f413basis x)
      (canonicalNatFourS4 (natFourWordBlock f413basis y))=
      star x ⬝ᵥ (complexify f413rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 13 f413basis
    (fun a => (f413hs_shape a).1) (fun a => (f413hs_shape a).2)
    f413S4Amplitudes f413_S4_amplitudes_check f413rawS4Form f413_S4_amplitude_gram_check x y

#print axioms f413_S4_amplitude_gram_check
#print axioms f413_actual_raw_S4_matrix
end TorusLean.BosonFiniteCertificate
