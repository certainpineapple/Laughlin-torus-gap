import torus.shared.RelativeJetMap
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.NormalJetBridge
open scoped TensorProduct ComplexConjugate BigOperators

/-- Finite relative-index output with the actual Hilbert direct-sum norm.
Every component is the entire original charge-(a+b) physical LLL. -/
abbrev RelativeCOMFamily (G : Geometry) (theta : Twist) (a b : ℕ)
    [NeZero (a+b)] (D : Finset ℕ) :=
  PiLp 2 (fun _ : {d : ℕ // d ∈ D} => LLL G theta (a+b))

/-- The finite family of the actual relative derivatives, with L² sum norm. -/
def relativeJetFamily (G : Geometry) (theta : Twist) (a b : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)] (D : Finset ℕ) :
    (LLL G theta a ⊗[ℂ] LLL G theta b) →L[ℂ] RelativeCOMFamily G theta a b D :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun d => relativeJet G theta a b d.val))

@[simp] theorem relativeJetFamily_apply (G : Geometry) (theta : Twist) (a b : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)] (D : Finset ℕ)
    (ψ : LLL G theta a ⊗[ℂ] LLL G theta b) (d : {d : ℕ // d ∈ D}) :
    relativeJetFamily G theta a b D ψ d = relativeJet G theta a b d.val ψ := rfl

/-- Exact physical finite-frame energy, retaining all COM components. -/
theorem relativeJetFamily_norm_sq (G : Geometry) (theta : Twist) (a b : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)] (D : Finset ℕ)
    (ψ : LLL G theta a ⊗[ℂ] LLL G theta b) :
    ‖relativeJetFamily G theta a b D ψ‖^2 =
      ∑ d : {d : ℕ // d ∈ D},
        ∫ C, ‖localNormalJet a b d.val (rawPairFunction G theta a b ψ) C‖^2
          ∂cellMeasure G (a+b) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro d _
  exact relativeJet_cell_norm_sq G theta a b d.val ψ

/-- No completion beyond the already complete finite physical tensor is
being hidden when the bounded map is formed. -/
theorem relativeJet_domain_complete (G : Geometry) (theta : Twist) (a b : ℕ)
    [NeZero a] [NeZero b] : CompleteSpace (LLL G theta a ⊗[ℂ] LLL G theta b) :=
  FiniteDimensional.complete ℂ _

/-- The full COM family has its actual Hilbert inner product. -/
theorem relativeJetFamily_inner (G : Geometry) (theta : Twist) (a b : ℕ)
    [NeZero a] [NeZero b] [NeZero (a+b)] (D : Finset ℕ)
    (ψ φ : LLL G theta a ⊗[ℂ] LLL G theta b) :
    inner ℂ (relativeJetFamily G theta a b D ψ) (relativeJetFamily G theta a b D φ) =
      ∑ d : {d : ℕ // d ∈ D}, cellInner G (a+b)
        (relativeJet G theta a b d.val ψ).val (relativeJet G theta a b d.val φ).val := rfl

/-- Exchange of actual equal-charge tensors swaps their two arguments. -/
theorem rawPairFunction_comm (G : Geometry) (theta : Twist) (a : ℕ)
    (ψ : RawLLLModule G theta a ⊗[ℂ] RawLLLModule G theta a) (z : ℂ × ℂ) :
    rawPairFunction G theta a a (TensorProduct.comm ℂ _ _ ψ) z =
      rawPairFunction G theta a a ψ (z.2,z.1) := by
  induction ψ using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => simp [mul_comm]
  | add ψ φ hψ hφ => simp only [map_add, Pi.add_apply, hψ, hφ]

/-- Equal-charge exchange is exactly parity of the original relative jet,
with no extra square root or factorial. -/
theorem localNormalJet_swap_equal_charge (a : ℝ) (d : ℕ) (Ψ : ℂ × ℂ → ℂ) (C : ℂ) :
    localNormalJet a a d (fun z => Ψ (z.2,z.1)) C =
      (-1 : ℂ)^d * localNormalJet a a d Ψ C := by
  let H : ℂ → ℂ := fun r => Complex.exp ((relativeCharge a a : ℂ) * (r * conj r) / 2) *
    Ψ (jacobiFirst a a C r, jacobiSecond a a C r)
  have heq : (fun r : ℂ => Complex.exp ((relativeCharge a a : ℂ) * (r * conj r) / 2) *
      Ψ (jacobiSecond a a C r, jacobiFirst a a C r)) = fun r => H (-r) := by
    funext r
    simp [H, jacobiFirst, jacobiSecond, sub_eq_add_neg]
  unfold localNormalJet
  rw [heq, iteratedDeriv_comp_neg]
  simp only [neg_zero, smul_eq_mul]
  ring

/-- Parity holds on every full equal-charge tensor before any statistics
restriction, so it cannot hide a missing COM component. -/
theorem relativeJet_comm (G : Geometry) (theta : Twist) (a d : ℕ)
    [NeZero a] [NeZero (a+a)] (ψ : LLL G theta a ⊗[ℂ] LLL G theta a) :
    relativeJet G theta a a d (TensorProduct.comm ℂ _ _ ψ) =
      (-1 : ℂ)^d • relativeJet G theta a a d ψ := by
  apply Subtype.ext
  funext C
  change localNormalJet a a d
    (rawPairFunction G theta a a (TensorProduct.comm ℂ _ _ ψ)) C = _
  rw [show rawPairFunction G theta a a (TensorProduct.comm ℂ _ _ ψ) =
    (fun z => rawPairFunction G theta a a ψ (z.2,z.1)) from funext (rawPairFunction_comm G theta a ψ)]
  exact localNormalJet_swap_equal_charge a d _ C

end TorusLean.Shared.RelativeJetMap
