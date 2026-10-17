import torus.shared.BosonFiniteCertificateNatFourCOMOriginalIndexTransport

/-! All seventeen separately checked original M4 form matrices enter the
whole-N4, all-COM-level rank expansion. This is an identity of the original
normal-ordered source, not a definition of a candidate matrix operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFourFinSeventeen_cases (P : Fin 17 → Prop)
    (h00 : P (0 : Fin 17))
    (h01 : P (1 : Fin 17))
    (h02 : P (2 : Fin 17))
    (h03 : P (3 : Fin 17))
    (h04 : P (4 : Fin 17))
    (h05 : P (5 : Fin 17))
    (h06 : P (6 : Fin 17))
    (h07 : P (7 : Fin 17))
    (h08 : P (8 : Fin 17))
    (h09 : P (9 : Fin 17))
    (h10 : P (10 : Fin 17))
    (h11 : P (11 : Fin 17))
    (h12 : P (12 : Fin 17))
    (h13 : P (13 : Fin 17))
    (h14 : P (14 : Fin 17))
    (h15 : P (15 : Fin 17))
    (h16 : P (16 : Fin 17))
    (D : Fin 17) : P D := by
  fin_cases D <;> assumption

#print axioms natFourFinSeventeen_cases
end TorusLean.BosonFiniteCertificate
