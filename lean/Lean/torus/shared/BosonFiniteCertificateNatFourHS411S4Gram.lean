import torus.shared.BosonFiniteCertificateNatFourHS411S4Amplitudes

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f411hs_shape (a : Fin 27) :
    (f411basis a).length=4 ∧ (f411basis a).sum=11 := by
  apply natFourBasis_shape 11
  rw [← f411_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

private def f411S4GramAInt : Matrix (Fin 12) (Fin 27) ℤ :=
  fun i j => (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 12 else 4) else 4) else 0) else 0) else (if i.val < 2 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 8 else 0)) else 0) else (if j.val < 9 then (if j.val < 7 then 8 else 4) else (if j.val < 11 then 4 else 0))) else 0) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 8)) else 0) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 4 else 0)) else (if j.val < 11 then 0 else (if j.val < 12 then 8 else 4)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 4 else 0) else (if j.val < 18 then (if j.val < 17 then 12 else 4) else 4)) else 0)))) else (if i.val < 4 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 8 else 0)) else (if j.val < 9 then (if j.val < 7 then 0 else 4) else (if j.val < 11 then 0 else (if j.val < 12 then 0 else 4)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 0 else (if j.val < 15 then 8 else 4)) else (if j.val < 18 then (if j.val < 17 then 0 else 8) else 0)) else (if j.val < 23 then (if j.val < 21 then 8 else 4) else 0))) else (if i.val < 5 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 8 else 0))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 4)) else (if j.val < 11 then (if j.val < 10 then 4 else 0) else (if j.val < 12 then 4 else 0)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 4 else (if j.val < 15 then 0 else 8)) else (if j.val < 18 then 0 else (if j.val < 19 then 8 else 0))) else (if j.val < 23 then (if j.val < 21 then 4 else (if j.val < 22 then 4 else 0)) else (if j.val < 25 then (if j.val < 24 then 8 else 12) else (if j.val < 26 then 4 else 0))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 0 else 8))) else (if j.val < 9 then 0 else (if j.val < 11 then (if j.val < 10 then 4 else 8) else (if j.val < 12 then 0 else 4)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 4 else (if j.val < 15 then 4 else 0)) else (if j.val < 18 then 0 else (if j.val < 19 then 0 else 8))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 4 else 8)) else (if j.val < 25 then (if j.val < 24 then 4 else 0) else (if j.val < 26 then 8 else 12)))))))) else (if i.val < 9 then (if i.val < 7 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 0 else 8))) else (if j.val < 9 then 0 else (if j.val < 11 then (if j.val < 10 then 4 else 8) else (if j.val < 12 then 0 else 4)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 4 else (if j.val < 15 then 4 else 0)) else (if j.val < 18 then 0 else (if j.val < 19 then 0 else 8))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 4 else 8)) else (if j.val < 25 then (if j.val < 24 then 4 else 0) else (if j.val < 26 then 8 else 12))))) else (if i.val < 8 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 8 else 0))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 4)) else (if j.val < 11 then (if j.val < 10 then 4 else 0) else (if j.val < 12 then 4 else 0)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 4 else (if j.val < 15 then 0 else 8)) else (if j.val < 18 then 0 else (if j.val < 19 then 8 else 0))) else (if j.val < 23 then (if j.val < 21 then 4 else (if j.val < 22 then 4 else 0)) else (if j.val < 25 then (if j.val < 24 then 8 else 12) else (if j.val < 26 then 4 else 0))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 8 else 0)) else (if j.val < 9 then (if j.val < 7 then 0 else 4) else (if j.val < 11 then 0 else (if j.val < 12 then 0 else 4)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 0 else (if j.val < 15 then 8 else 4)) else (if j.val < 18 then (if j.val < 17 then 0 else 8) else 0)) else (if j.val < 23 then (if j.val < 21 then 8 else 4) else 0))))) else (if i.val < 10 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 8)) else 0) else (if j.val < 9 then (if j.val < 7 then 4 else (if j.val < 8 then 4 else 0)) else (if j.val < 11 then 0 else (if j.val < 12 then 8 else 4)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 4 else 0) else (if j.val < 18 then (if j.val < 17 then 12 else 4) else 4)) else 0)) else (if i.val < 11 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 8 else 0)) else 0) else (if j.val < 9 then (if j.val < 7 then 8 else 4) else (if j.val < 11 then 4 else 0))) else 0) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 12 else 4) else 4) else 0) else 0)))))

private def f411S4GramWInt : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.diagonal (fun p : Fin 12 => ((p.val.factorial * (11-p.val).factorial : ℕ) : ℤ))

private def f411S4GramVInt : Matrix (Fin 12) (Fin 27) ℤ :=
  fun i j => (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 479001600 else 159667200) else 159667200) else 0) else 0) else (if i.val < 2 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 29030400 else 0)) else 0) else (if j.val < 9 then (if j.val < 7 then 29030400 else 14515200) else (if j.val < 11 then 14515200 else 0))) else 0) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 5806080)) else 0) else (if j.val < 9 then (if j.val < 7 then 2903040 else (if j.val < 8 then 2903040 else 0)) else (if j.val < 11 then 0 else (if j.val < 12 then 5806080 else 2903040)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 2903040 else 0) else (if j.val < 18 then (if j.val < 17 then 8709120 else 2903040) else 2903040)) else 0)))) else (if i.val < 4 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 1935360 else 0)) else (if j.val < 9 then (if j.val < 7 then 0 else 967680) else (if j.val < 11 then 0 else (if j.val < 12 then 0 else 967680)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 0 else (if j.val < 15 then 1935360 else 967680)) else (if j.val < 18 then (if j.val < 17 then 0 else 1935360) else 0)) else (if j.val < 23 then (if j.val < 21 then 1935360 else 967680) else 0))) else (if i.val < 5 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 967680 else 0))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 483840)) else (if j.val < 11 then (if j.val < 10 then 483840 else 0) else (if j.val < 12 then 483840 else 0)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 483840 else (if j.val < 15 then 0 else 967680)) else (if j.val < 18 then 0 else (if j.val < 19 then 967680 else 0))) else (if j.val < 23 then (if j.val < 21 then 483840 else (if j.val < 22 then 483840 else 0)) else (if j.val < 25 then (if j.val < 24 then 967680 else 1451520) else (if j.val < 26 then 483840 else 0))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 0 else 691200))) else (if j.val < 9 then 0 else (if j.val < 11 then (if j.val < 10 then 345600 else 691200) else (if j.val < 12 then 0 else 345600)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 345600 else (if j.val < 15 then 345600 else 0)) else (if j.val < 18 then 0 else (if j.val < 19 then 0 else 691200))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 345600 else 691200)) else (if j.val < 25 then (if j.val < 24 then 345600 else 0) else (if j.val < 26 then 691200 else 1036800)))))))) else (if i.val < 9 then (if i.val < 7 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 0 else 691200))) else (if j.val < 9 then 0 else (if j.val < 11 then (if j.val < 10 then 345600 else 691200) else (if j.val < 12 then 0 else 345600)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 345600 else (if j.val < 15 then 345600 else 0)) else (if j.val < 18 then 0 else (if j.val < 19 then 0 else 691200))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 345600 else 691200)) else (if j.val < 25 then (if j.val < 24 then 345600 else 0) else (if j.val < 26 then 691200 else 1036800))))) else (if i.val < 8 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 967680 else 0))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 483840)) else (if j.val < 11 then (if j.val < 10 then 483840 else 0) else (if j.val < 12 then 483840 else 0)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 483840 else (if j.val < 15 then 0 else 967680)) else (if j.val < 18 then 0 else (if j.val < 19 then 967680 else 0))) else (if j.val < 23 then (if j.val < 21 then 483840 else (if j.val < 22 then 483840 else 0)) else (if j.val < 25 then (if j.val < 24 then 967680 else 1451520) else (if j.val < 26 then 483840 else 0))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 1935360 else 0)) else (if j.val < 9 then (if j.val < 7 then 0 else 967680) else (if j.val < 11 then 0 else (if j.val < 12 then 0 else 967680)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 0 else (if j.val < 15 then 1935360 else 967680)) else (if j.val < 18 then (if j.val < 17 then 0 else 1935360) else 0)) else (if j.val < 23 then (if j.val < 21 then 1935360 else 967680) else 0))))) else (if i.val < 10 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 5806080)) else 0) else (if j.val < 9 then (if j.val < 7 then 2903040 else (if j.val < 8 then 2903040 else 0)) else (if j.val < 11 then 0 else (if j.val < 12 then 5806080 else 2903040)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 2903040 else 0) else (if j.val < 18 then (if j.val < 17 then 8709120 else 2903040) else 2903040)) else 0)) else (if i.val < 11 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 29030400 else 0)) else 0) else (if j.val < 9 then (if j.val < 7 then 29030400 else 14515200) else (if j.val < 11 then 14515200 else 0))) else 0) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 479001600 else 159667200) else 159667200) else 0) else 0)))))

private def f411S4GramYInt : Matrix (Fin 27) (Fin 27) ℤ :=
  fun i j => (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 11496038400 else 3832012800) else 3832012800) else 0) else 0) else (if i.val < 2 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3832012800 else (if j.val < 2 then 1741824000 else 1277337600)) else 1277337600) else (if j.val < 9 then (if j.val < 7 then 464486400 else 232243200) else (if j.val < 11 then 232243200 else 0))) else 0) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3832012800 else (if j.val < 2 then 1277337600 else 1370234880)) else 1277337600) else (if j.val < 9 then (if j.val < 7 then 46448640 else (if j.val < 8 then 46448640 else 0)) else (if j.val < 11 then 0 else (if j.val < 12 then 92897280 else 46448640)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 46448640 else 0) else (if j.val < 18 then (if j.val < 17 then 139345920 else 46448640) else 46448640)) else 0)))) else (if i.val < 4 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3832012800 else 1277337600) else (if j.val < 4 then 1308303360 else 1277337600)) else (if j.val < 9 then (if j.val < 7 then 0 else 15482880) else (if j.val < 11 then 0 else (if j.val < 12 then 0 else 15482880)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 0 else (if j.val < 15 then 30965760 else 15482880)) else (if j.val < 18 then (if j.val < 17 then 0 else 30965760) else 0)) else (if j.val < 23 then (if j.val < 21 then 30965760 else 15482880) else 0))) else (if i.val < 5 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3832012800 else 1277337600) else (if j.val < 4 then 1277337600 else (if j.val < 5 then 1292820480 else 1277337600))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 7741440)) else (if j.val < 11 then (if j.val < 10 then 7741440 else 0) else (if j.val < 12 then 7741440 else 0)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 7741440 else (if j.val < 15 then 0 else 15482880)) else (if j.val < 18 then 0 else (if j.val < 19 then 15482880 else 0))) else (if j.val < 23 then (if j.val < 21 then 7741440 else (if j.val < 22 then 7741440 else 0)) else (if j.val < 25 then (if j.val < 24 then 15482880 else 23224320) else (if j.val < 26 then 7741440 else 0))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 3832012800 else 1277337600) else (if j.val < 4 then 1277337600 else (if j.val < 5 then 1277337600 else 1288396800))) else (if j.val < 9 then 0 else (if j.val < 11 then (if j.val < 10 then 5529600 else 11059200) else (if j.val < 12 then 0 else 5529600)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 5529600 else (if j.val < 15 then 5529600 else 0)) else (if j.val < 18 then 0 else (if j.val < 19 then 0 else 11059200))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 5529600 else 11059200)) else (if j.val < 25 then (if j.val < 24 then 5529600 else 0) else (if j.val < 26 then 11059200 else 16588800)))))))) else (if i.val < 9 then (if i.val < 7 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 464486400 else 46448640)) else 0) else (if j.val < 9 then (if j.val < 7 then 487710720 else (if j.val < 8 then 255467520 else 232243200)) else (if j.val < 11 then 232243200 else (if j.val < 12 then 46448640 else 23224320)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 23224320 else 0) else (if j.val < 18 then (if j.val < 17 then 69672960 else 23224320) else 23224320)) else 0)) else (if i.val < 8 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 232243200 else 46448640)) else (if j.val < 4 then 15482880 else 0)) else (if j.val < 9 then (if j.val < 7 then 255467520 else (if j.val < 8 then 147087360 else 123863040)) else (if j.val < 11 then 116121600 else (if j.val < 12 then 46448640 else 30965760)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 23224320 else (if j.val < 15 then 15482880 else 7741440)) else (if j.val < 18 then (if j.val < 17 then 69672960 else 38707200) else 23224320)) else (if j.val < 23 then (if j.val < 21 then 15482880 else 7741440) else 0))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 232243200 else 0)) else (if j.val < 4 then 15482880 else (if j.val < 5 then 7741440 else 0))) else (if j.val < 9 then (if j.val < 7 then 232243200 else (if j.val < 8 then 123863040 else 127733760)) else (if j.val < 11 then (if j.val < 10 then 119992320 else 116121600) else (if j.val < 12 then 3870720 else 7741440)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 3870720 else 15482880) else (if j.val < 18 then (if j.val < 17 then 0 else 15482880) else (if j.val < 19 then 7741440 else 0))) else (if j.val < 23 then (if j.val < 21 then 19353600 else (if j.val < 22 then 11612160 else 7741440)) else (if j.val < 25 then (if j.val < 24 then 7741440 else 11612160) else (if j.val < 26 then 3870720 else 0))))))) else (if i.val < 11 then (if i.val < 10 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 232243200 else 0)) else (if j.val < 4 then 0 else (if j.val < 5 then 7741440 else 5529600))) else (if j.val < 9 then (if j.val < 7 then 232243200 else (if j.val < 8 then 116121600 else 119992320)) else (if j.val < 11 then (if j.val < 10 then 122757120 else 121651200) else (if j.val < 12 then 3870720 else 2764800)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 6635520 else (if j.val < 15 then 2764800 else 7741440)) else (if j.val < 18 then 0 else (if j.val < 19 then 7741440 else 5529600))) else (if j.val < 23 then (if j.val < 21 then 3870720 else (if j.val < 22 then 6635520 else 5529600)) else (if j.val < 25 then (if j.val < 24 then 10506240 else 11612160) else (if j.val < 26 then 9400320 else 8294400))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 232243200 else 0)) else (if j.val < 4 then 0 else (if j.val < 5 then 0 else 11059200))) else (if j.val < 9 then (if j.val < 7 then 232243200 else 116121600) else (if j.val < 11 then (if j.val < 10 then 121651200 else 127180800) else (if j.val < 12 then 0 else 5529600)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 5529600 else (if j.val < 15 then 5529600 else 0)) else (if j.val < 18 then 0 else (if j.val < 19 then 0 else 11059200))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 5529600 else 11059200)) else (if j.val < 25 then (if j.val < 24 then 5529600 else 0) else (if j.val < 26 then 11059200 else 16588800)))))) else (if i.val < 12 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 92897280)) else (if j.val < 4 then 0 else (if j.val < 5 then 7741440 else 0))) else (if j.val < 9 then (if j.val < 7 then 46448640 else (if j.val < 8 then 46448640 else 3870720)) else (if j.val < 11 then (if j.val < 10 then 3870720 else 0) else (if j.val < 12 then 96768000 else 46448640)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 50319360 else (if j.val < 15 then 0 else 7741440)) else (if j.val < 18 then (if j.val < 17 then 139345920 else 46448640) else (if j.val < 19 then 54190080 else 46448640))) else (if j.val < 23 then (if j.val < 21 then 3870720 else (if j.val < 22 then 3870720 else 0)) else (if j.val < 25 then (if j.val < 24 then 7741440 else 11612160) else (if j.val < 26 then 3870720 else 0))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 46448640)) else (if j.val < 4 then 15482880 else (if j.val < 5 then 0 else 5529600))) else (if j.val < 9 then (if j.val < 7 then 23224320 else (if j.val < 8 then 30965760 else 7741440)) else (if j.val < 11 then (if j.val < 10 then 2764800 else 5529600) else (if j.val < 12 then 46448640 else 33730560)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 25989120 else (if j.val < 15 then 18247680 else 7741440)) else (if j.val < 18 then (if j.val < 17 then 69672960 else 38707200) else (if j.val < 19 then 23224320 else 28753920))) else (if j.val < 23 then (if j.val < 21 then 15482880 else (if j.val < 22 then 10506240 else 13271040)) else (if j.val < 25 then (if j.val < 24 then 2764800 else 0) else (if j.val < 26 then 5529600 else 8294400))))))))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 46448640)) else (if j.val < 4 then 0 else (if j.val < 5 then 7741440 else 5529600))) else (if j.val < 9 then (if j.val < 7 then 23224320 else (if j.val < 8 then 23224320 else 3870720)) else (if j.val < 11 then (if j.val < 10 then 6635520 else 5529600) else (if j.val < 12 then 50319360 else 25989120)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 29859840 else (if j.val < 15 then 2764800 else 7741440)) else (if j.val < 18 then (if j.val < 17 then 69672960 else 23224320) else (if j.val < 19 then 30965760 else 28753920))) else (if j.val < 23 then (if j.val < 21 then 3870720 else (if j.val < 22 then 6635520 else 5529600)) else (if j.val < 25 then (if j.val < 24 then 10506240 else 11612160) else (if j.val < 26 then 9400320 else 8294400))))) else (if i.val < 15 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 30965760 else (if j.val < 5 then 0 else 5529600))) else (if j.val < 9 then (if j.val < 7 then 0 else 15482880) else (if j.val < 11 then (if j.val < 10 then 2764800 else 5529600) else (if j.val < 12 then 0 else 18247680)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 2764800 else (if j.val < 15 then 33730560 else 15482880)) else (if j.val < 18 then (if j.val < 17 then 0 else 30965760) else (if j.val < 19 then 0 else 5529600))) else (if j.val < 23 then (if j.val < 21 then 30965760 else (if j.val < 22 then 18247680 else 21012480)) else (if j.val < 25 then (if j.val < 24 then 2764800 else 0) else (if j.val < 26 then 5529600 else 8294400))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 15482880 else (if j.val < 5 then 15482880 else 0))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 7741440 else 15482880)) else (if j.val < 11 then (if j.val < 10 then 7741440 else 0) else 7741440))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 7741440 else (if j.val < 15 then 15482880 else 23224320)) else (if j.val < 18 then (if j.val < 17 then 0 else 15482880) else (if j.val < 19 then 15482880 else 0))) else (if j.val < 23 then (if j.val < 21 then 23224320 else (if j.val < 22 then 15482880 else 7741440)) else (if j.val < 25 then (if j.val < 24 then 15482880 else 23224320) else (if j.val < 26 then 7741440 else 0))))))) else (if i.val < 18 then (if i.val < 17 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 139345920)) else 0) else (if j.val < 9 then (if j.val < 7 then 69672960 else (if j.val < 8 then 69672960 else 0)) else (if j.val < 11 then 0 else (if j.val < 12 then 139345920 else 69672960)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 69672960 else 0) else (if j.val < 18 then (if j.val < 17 then 209018880 else 69672960) else 69672960)) else 0)) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 46448640)) else (if j.val < 4 then 30965760 else 0)) else (if j.val < 9 then (if j.val < 7 then 23224320 else (if j.val < 8 then 38707200 else 15482880)) else (if j.val < 11 then 0 else (if j.val < 12 then 46448640 else 38707200)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 23224320 else (if j.val < 15 then 30965760 else 15482880)) else (if j.val < 18 then (if j.val < 17 then 69672960 else 54190080) else 23224320)) else (if j.val < 23 then (if j.val < 21 then 30965760 else 15482880) else 0)))) else (if i.val < 19 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 46448640)) else (if j.val < 4 then 0 else (if j.val < 5 then 15482880 else 0))) else (if j.val < 9 then (if j.val < 7 then 23224320 else (if j.val < 8 then 23224320 else 7741440)) else (if j.val < 11 then (if j.val < 10 then 7741440 else 0) else (if j.val < 12 then 54190080 else 23224320)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 30965760 else (if j.val < 15 then 0 else 15482880)) else (if j.val < 18 then (if j.val < 17 then 69672960 else 23224320) else (if j.val < 19 then 38707200 else 23224320))) else (if j.val < 23 then (if j.val < 21 then 7741440 else (if j.val < 22 then 7741440 else 0)) else (if j.val < 25 then (if j.val < 24 then 15482880 else 23224320) else (if j.val < 26 then 7741440 else 0))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then (if j.val < 1 then 0 else (if j.val < 2 then 0 else 46448640)) else (if j.val < 4 then 0 else (if j.val < 5 then 0 else 11059200))) else (if j.val < 9 then (if j.val < 7 then 23224320 else (if j.val < 8 then 23224320 else 0)) else (if j.val < 11 then (if j.val < 10 then 5529600 else 11059200) else (if j.val < 12 then 46448640 else 28753920)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 28753920 else (if j.val < 15 then 5529600 else 0)) else (if j.val < 18 then (if j.val < 17 then 69672960 else 23224320) else (if j.val < 19 then 23224320 else 34283520))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 5529600 else 11059200)) else (if j.val < 25 then (if j.val < 24 then 5529600 else 0) else (if j.val < 26 then 11059200 else 16588800)))))))) else (if i.val < 23 then (if i.val < 21 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 30965760 else (if j.val < 5 then 7741440 else 0))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 15482880 else 19353600)) else (if j.val < 11 then (if j.val < 10 then 3870720 else 0) else (if j.val < 12 then 3870720 else 15482880)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 3870720 else (if j.val < 15 then 30965760 else 23224320)) else (if j.val < 18 then (if j.val < 17 then 0 else 30965760) else (if j.val < 19 then 7741440 else 0))) else (if j.val < 23 then (if j.val < 21 then 34836480 else (if j.val < 22 then 19353600 else 15482880)) else (if j.val < 25 then (if j.val < 24 then 7741440 else 11612160) else (if j.val < 26 then 3870720 else 0))))) else (if i.val < 22 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 15482880 else (if j.val < 5 then 7741440 else 5529600))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 7741440 else 11612160)) else (if j.val < 11 then (if j.val < 10 then 6635520 else 5529600) else (if j.val < 12 then 3870720 else 10506240)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 6635520 else (if j.val < 15 then 18247680 else 15482880)) else (if j.val < 18 then (if j.val < 17 then 0 else 15482880) else (if j.val < 19 then 7741440 else 5529600))) else (if j.val < 23 then (if j.val < 21 then 19353600 else (if j.val < 22 then 14376960 else 13271040)) else (if j.val < 25 then (if j.val < 24 then 10506240 else 11612160) else (if j.val < 26 then 9400320 else 8294400))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 15482880 else (if j.val < 5 then 0 else 11059200))) else (if j.val < 9 then (if j.val < 7 then 0 else 7741440) else (if j.val < 11 then (if j.val < 10 then 5529600 else 11059200) else (if j.val < 12 then 0 else 13271040)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 5529600 else (if j.val < 15 then 21012480 else 7741440)) else (if j.val < 18 then (if j.val < 17 then 0 else 15482880) else (if j.val < 19 then 0 else 11059200))) else (if j.val < 23 then (if j.val < 21 then 15482880 else (if j.val < 22 then 13271040 else 18800640)) else (if j.val < 25 then (if j.val < 24 then 5529600 else 0) else (if j.val < 26 then 11059200 else 16588800))))))) else (if i.val < 25 then (if i.val < 24 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 15482880 else 5529600))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 7741440)) else (if j.val < 11 then (if j.val < 10 then 10506240 else 5529600) else (if j.val < 12 then 7741440 else 2764800)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 10506240 else (if j.val < 15 then 2764800 else 15482880)) else (if j.val < 18 then 0 else (if j.val < 19 then 15482880 else 5529600))) else (if j.val < 23 then (if j.val < 21 then 7741440 else (if j.val < 22 then 10506240 else 5529600)) else (if j.val < 25 then (if j.val < 24 then 18247680 else 23224320) else (if j.val < 26 then 13271040 else 8294400))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 23224320 else 0))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 11612160)) else (if j.val < 11 then (if j.val < 10 then 11612160 else 0) else (if j.val < 12 then 11612160 else 0)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 11612160 else (if j.val < 15 then 0 else 23224320)) else (if j.val < 18 then 0 else (if j.val < 19 then 23224320 else 0))) else (if j.val < 23 then (if j.val < 21 then 11612160 else (if j.val < 22 then 11612160 else 0)) else (if j.val < 25 then (if j.val < 24 then 23224320 else 34836480) else (if j.val < 26 then 11612160 else 0)))))) else (if i.val < 26 then (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 7741440 else 11059200))) else (if j.val < 9 then (if j.val < 7 then 0 else (if j.val < 8 then 0 else 3870720)) else (if j.val < 11 then (if j.val < 10 then 9400320 else 11059200) else (if j.val < 12 then 3870720 else 5529600)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 9400320 else (if j.val < 15 then 5529600 else 7741440)) else (if j.val < 18 then 0 else (if j.val < 19 then 7741440 else 11059200))) else (if j.val < 23 then (if j.val < 21 then 3870720 else (if j.val < 22 then 9400320 else 11059200)) else (if j.val < 25 then (if j.val < 24 then 13271040 else 11612160) else (if j.val < 26 then 14929920 else 16588800))))) else (if j.val < 13 then (if j.val < 6 then (if j.val < 3 then 0 else (if j.val < 4 then 0 else (if j.val < 5 then 0 else 16588800))) else (if j.val < 9 then 0 else (if j.val < 11 then (if j.val < 10 then 8294400 else 16588800) else (if j.val < 12 then 0 else 8294400)))) else (if j.val < 20 then (if j.val < 16 then (if j.val < 14 then 8294400 else (if j.val < 15 then 8294400 else 0)) else (if j.val < 18 then 0 else (if j.val < 19 then 0 else 16588800))) else (if j.val < 23 then (if j.val < 21 then 0 else (if j.val < 22 then 8294400 else 16588800)) else (if j.val < 25 then (if j.val < 24 then 8294400 else 0) else (if j.val < 26 then 16588800 else 24883200))))))))))

theorem f411_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 11 f411S4Amplitudes=f411rawS4Form := by
  have hA : natFourIntegerMatrix 1 f411S4GramAInt = f411S4Amplitudes := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix 1 f411S4GramAInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4Amplitudes) 11 j) (by decide +kernel)
      exact h 0 b
  have hW : natFourIntegerMatrix (2^13) f411S4GramWInt = (Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val))) := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 12) => (natFourIntegerMatrix (2^13) f411S4GramWInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 12) => ((Matrix.diagonal (fun p : Fin 12 => natFourPairWeight p.val (11-p.val)))) 11 j) (by decide +kernel)
      exact h 0 b
  have hV : f411S4GramWInt*f411S4GramAInt = f411S4GramVInt := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 7 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 8 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 9 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 10 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramWInt*f411S4GramAInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramVInt) 11 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f411S4GramAIntᵀ*f411S4GramVInt = f411S4GramYInt := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 5 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 6 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 7 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 8 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 9 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 10 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 11 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 12 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 13 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 14 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 14 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 15 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 15 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 16 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 16 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 17 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 17 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 18 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 18 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 19 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 19 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 20 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 20 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 21 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 21 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 22 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 22 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 23 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 23 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 24 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 24 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 25 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 25 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramAIntᵀ*f411S4GramVInt) 26 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411S4GramYInt) 26 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt = f411rawS4Form := by
    ext a b
    fin_cases a
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 0 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 1 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 2 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 3 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 3 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 4 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 4 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 5 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 5 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 6 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 6 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 7 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 7 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 8 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 8 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 9 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 9 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 10 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 10 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 11 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 11 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 12 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 12 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 13 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 13 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 14 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 14 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 15 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 15 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 16 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 16 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 17 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 17 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 18 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 18 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 19 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 19 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 20 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 20 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 21 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 21 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 22 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 22 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 23 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 23 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 24 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 24 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 25 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 25 j) (by decide +kernel)
      exact h 0 b
    · have h := natFourRationalEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (natFourIntegerMatrix (1*((2^13)*1)) f411S4GramYInt) 26 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f411rawS4Form) 26 j) (by decide +kernel)
      exact h 0 b
  unfold natFourS4AmplitudeGram
  rw [← hA, ← hW, ← natFourIntegerMatrix_transpose,
    natFourIntegerMatrix_mul, natFourIntegerMatrix_mul, hV, hY]
  exact hF

theorem f411_actual_raw_S4_matrix (x y : Fin 27 → ℂ) :
    natOccupationInner (natFourWordBlock f411basis x)
      (canonicalNatFourS4 (natFourWordBlock f411basis y))=
      star x ⬝ᵥ (complexify f411rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 11 f411basis
    (fun a => (f411hs_shape a).1) (fun a => (f411hs_shape a).2)
    f411S4Amplitudes f411_S4_amplitudes_check f411rawS4Form f411_S4_amplitude_gram_check x y

#print axioms f411_S4_amplitude_gram_check
#print axioms f411_actual_raw_S4_matrix
end TorusLean.BosonFiniteCertificate
