import torus.shared.RelativeJetGramKernelSum
import torus.shared.RelativeJetMapFamilyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetFrame
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.RelativeJetGramKernelSum
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
open scoped TensorProduct

/-- Full-COM finite output Gram bound for the actual jets, with every entry
identified from absolute periodization, not supplied as a premise. -/
theorem relativeJetTruncation_gram_error (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (f : RelativeCOMTruncation G theta D) :
    |‖(relativeJetTruncation G theta D).adjoint f‖^2 - ‖f‖^2| ≤ allowance * ‖f‖^2 :=
  relativeJetTruncation_gram_error_of_entries G theta D hD hL
    (fun j m => relativeJet_comp_adjoint_eq_entry G theta j m (le_trans (by norm_num) hL)) f

theorem relativeJetTruncation_adjoint_bound (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (f : RelativeCOMTruncation G theta D) :
    ‖(relativeJetTruncation G theta D).adjoint f‖^2 ≤ (1+allowance) * ‖f‖^2 :=
  relativeJetTruncation_adjoint_bound_of_entries G theta D hD hL
    (fun j m => relativeJet_comp_adjoint_eq_entry G theta j m (le_trans (by norm_num) hL)) f

theorem relativeJetTruncation_opNorm (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G) :
    ‖relativeJetTruncation G theta D‖ ≤ Real.sqrt (1+allowance) :=
  relativeJetTruncation_opNorm_of_entries G theta D hD hL
    (fun j m => relativeJet_comp_adjoint_eq_entry G theta j m (le_trans (by norm_num) hL))

/-- Actual relative frame bound on the whole physical charge-two tensor.
No COM truncation, independent norm assumption, or dimension loss is used. -/
theorem relativeJetTruncation_energy (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    ‖relativeJetTruncation G theta D ψ‖^2 ≤ (1+allowance) * ‖ψ‖^2 :=
  relativeJetTruncation_energy_of_entries G theta D hD hL
    (fun j m => relativeJet_comp_adjoint_eq_entry G theta j m (le_trans (by norm_num) hL)) ψ

theorem relativeJetTruncation_input_form (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    (inner ℂ ψ ((relativeJetTruncation G theta D).adjoint
      (relativeJetTruncation G theta D ψ))).re ≤ (1+allowance) * ‖ψ‖^2 :=
  relativeJetTruncation_input_form_of_entries G theta D hD hL
    (fun j m => relativeJet_comp_adjoint_eq_entry G theta j m (le_trans (by norm_num) hL)) ψ

#print axioms relativeJetTruncation_gram_error
#print axioms relativeJetTruncation_adjoint_bound
#print axioms relativeJetTruncation_opNorm
#print axioms relativeJetTruncation_energy
#print axioms relativeJetTruncation_input_form
end TorusLean.Shared.RelativeJetFrame
