import torus.shared.FermionRelativeFrameCoefficientsPaper
import torus.shared.ThermalCoherentFermionAnchoredCAR

/-! Literal finite planar m=1 coefficients for the anchored fermion source.
The indices are canonical orbital levels, with p+1 the pair total degree.
The same paperPairWeight already identified in the actual torus CAR
pairDescendant is used here. These coefficients do not define a torus H. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open OAI.Laughlin.Fock TorusLean.Fermion
open TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators ComplexConjugate

/-- Antisymmetric continuation of the original i<j coefficient, including
its degree delta and the paper's negative ground-pair orientation. -/
def planePairCoefficient (p i j : ℕ) : ℝ :=
  if i+j=p+1 then ((i:ℝ)-(j:ℝ))*paperPairWeight p i j else 0

/-- True finite canonical pair creator, not a rank form specified afterward. -/
def planePairCreate (Q p : ℕ) : Module.End ℂ (Space Q) :=
  coefficientPairCreate Q (fun i j => (planePairCoefficient p i.val j.val:ℂ))

def planePairRemove (Q p : ℕ) : Module.End ℂ (Space Q) :=
  coefficientPairRemove Q (fun i j => (planePairCoefficient p i.val j.val:ℂ))

theorem planePairCoefficient_antisymm (p i j : ℕ) :
    planePairCoefficient p j i = -planePairCoefficient p i j := by
  unfold planePairCoefficient
  rw [Nat.add_comm j i,paperPairWeight_symm p j i]
  split_ifs <;> ring

theorem planePairCoefficient_ground (p : ℕ) :
    planePairCoefficient p 0 1 = if p=0 then -1 else 0 := by
  by_cases hp : p=0
  · subst p
    norm_num [planePairCoefficient,paperPairWeight]
  · have h : 0+1≠p+1 := by omega
    simp only [planePairCoefficient,h,ite_false,hp]

theorem planePairCoefficient_zero_orbital (p l : ℕ) :
    planePairCoefficient p 0 l =
      if l=p+1 then -(l:ℝ)*paperPairWeight p 0 l else 0 := by
  simp only [planePairCoefficient,Nat.zero_add,Nat.cast_zero,zero_sub]

theorem planePairCoefficient_one_orbital (p l : ℕ) :
    planePairCoefficient p 1 l =
      if l=p then (1-(l:ℝ))*paperPairWeight p 1 l else 0 := by
  simp only [planePairCoefficient,Nat.cast_one]
  simp only [show (1+l=p+1) ↔ l=p by omega]

/-- The raw CAR computation reduces the genuine pair row to exactly its
three occupied pairs; the (0,1) channel is isolated before subtracting I. -/
theorem planePairRemove_anchored_triple (Q p : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) :
    planePairRemove Q p (rawTripleVector Q (mode a) (mode b) (mode d)) =
      ((if p=0 then -1 else 0):ℂ) • rawCreate Q (mode d) 1 -
      ((if d.val=p+1 then -(d.val:ℝ)*paperPairWeight p 0 d.val else 0):ℂ) •
        rawCreate Q (mode b) 1 +
      ((if d.val=p then (1-(d.val:ℝ))*paperPairWeight p 1 d.val else 0):ℂ) •
        rawCreate Q (mode a) 1 := by
  rw [planePairRemove,coefficientPairRemove_tripleVector]
  · simp only [Complex.conj_ofReal,ha,hb]
    rw [planePairCoefficient_ground,planePairCoefficient_zero_orbital,
      planePairCoefficient_one_orbital]
    simp only [apply_ite, Complex.ofReal_neg, Complex.ofReal_zero,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_natCast]
  · intro i j
    exact_mod_cast planePairCoefficient_antisymm p i.val j.val

/-- A pair cannot remove more orbital degree than is present in the
actual three-mode word. This is independent of any Hamiltonian cutoff. -/
theorem planePairRemove_triple_high_zero (Q p : ℕ) (a b d : Fin (Q+1))
    (h : a.val+b.val+d.val≤p) :
    planePairRemove Q p (rawTripleVector Q (mode a) (mode b) (mode d))=0 := by
  rw [planePairRemove,coefficientPairRemove_tripleVector]
  · have hab : a.val+b.val≠p+1 := by omega
    have had : a.val+d.val≠p+1 := by omega
    have hbd : b.val+d.val≠p+1 := by omega
    simp only [planePairCoefficient,hab,had,hbd,ite_false,Complex.ofReal_zero,
      map_zero,zero_smul,sub_zero,add_zero]
  · intro i j
    exact_mod_cast planePairCoefficient_antisymm p i.val j.val

/-- Every pair channel above the anchor's actual degree is genuinely zero.
This follows from the occupied CAR channels, rather than a chosen H cutoff. -/
theorem planePairRemove_anchored_high_zero (Q p : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (hp : d.val<p) :
    planePairRemove Q p (rawTripleVector Q (mode a) (mode b) (mode d))=0 := by
  rw [planePairRemove_anchored_triple Q p a b d ha hb]
  have hp0 : p≠0 := by omega
  have hd1 : d.val≠p+1 := by omega
  have hd : d.val≠p := by omega
  simp only [hp0,hd1,hd,ite_false,zero_smul,sub_zero,add_zero]

theorem planePairCreate_adjoint (Q p : ℕ) (x y : Space Q) :
    occupationInner Q (planePairCreate Q p x) y =
      occupationInner Q x (planePairRemove Q p y) :=
  coefficientPairCreate_adjoint Q _ x y

end TorusLean.Shared.ThermalCoherentFermionAnchored
