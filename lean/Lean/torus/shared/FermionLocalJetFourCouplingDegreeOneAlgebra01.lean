import torus.shared.FermionLocalJetFourCouplingIntegerSourceReflection01

/-!
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json.
No final source, vacuum, or raising identity is assumed here.
The only finite decisions are inequalities between literal elements of Fin 4.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open SourceCheckReflection01
namespace DegreeOneAlgebraCandidate

private theorem choose_factorial_int (n p : ℕ) (hp : p ≤ n) :
    (n.choose p : ℤ) * (p.factorial : ℤ) * ((n-p).factorial : ℤ) =
      (n.factorial : ℤ) := by
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp

private theorem coeff1_left_factorial (j k : ℕ) :
    (if j ≠ 0 then ((j+k-1).choose (j-1) : ℤ) else 0) *
        (j.factorial : ℤ) * (k.factorial : ℤ) =
      (j : ℤ) * ((j+k-1).factorial : ℤ) := by
  by_cases hj : j = 0
  · subst j
    simp
  · have hpred : j-1+1=j := by omega
    have hdiff : j+k-1-(j-1)=k := by omega
    have hc := choose_factorial_int (j+k-1) (j-1) (by omega)
    rw [hdiff] at hc
    have hf : (j.factorial : ℤ) = (j : ℤ) * ((j-1).factorial : ℤ) := by
      have h := Nat.factorial_succ (j-1)
      rw [hpred] at h
      exact_mod_cast h
    rw [if_pos hj, hf]
    calc
      _ = (j : ℤ) *
          (((j+k-1).choose (j-1) : ℤ) * ((j-1).factorial : ℤ) *
            (k.factorial : ℤ)) := by ring
      _ = _ := by rw [hc]

private theorem coeff1_right_factorial (j k : ℕ) :
    (if k ≠ 0 then ((j+k-1).choose j : ℤ) else 0) *
        (j.factorial : ℤ) * (k.factorial : ℤ) =
      (k : ℤ) * ((j+k-1).factorial : ℤ) := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hpred : k-1+1=k := by omega
    have hdiff : j+k-1-j=k-1 := by omega
    have hc := choose_factorial_int (j+k-1) j (by omega)
    rw [hdiff] at hc
    have hf : (k.factorial : ℤ) = (k : ℤ) * ((k-1).factorial : ℤ) := by
      have h := Nat.factorial_succ (k-1)
      rw [hpred] at h
      exact_mod_cast h
    rw [if_pos hk, hf]
    calc
      _ = (k : ℤ) *
          (((j+k-1).choose j : ℤ) * (j.factorial : ℤ) *
            ((k-1).factorial : ℤ)) := by ring
      _ = _ := by rw [hc]

theorem coeff1_factorial (j k : ℕ) :
    coeff1 (j+k) j * (j.factorial : ℤ) * (k.factorial : ℤ) =
      ((j : ℤ)-(k : ℤ)) * ((j+k-1).factorial : ℤ) := by
  have hrow : coeff1 (j+k) j =
      (if j ≠ 0 then ((j+k-1).choose (j-1) : ℤ) else 0) -
      (if k ≠ 0 then ((j+k-1).choose j : ℤ) else 0) := by
    simp only [coeff1, Nat.add_sub_cancel_left]
    by_cases hj : j=0
    · subst j
      simp
    · by_cases hk : k=0
      · subst k
        simp [hj]
      · have hl : j-1+k=j+k-1 := by omega
        have hr : j+(k-1)=j+k-1 := by omega
        simp [hj, hk, hl, hr]
  rw [hrow, sub_mul, sub_mul, coeff1_left_factorial, coeff1_right_factorial]
  ring

theorem coeff0_factorial (T p j k : ℕ)
    (hT : p+j+k=T) (hjk : 1 ≤ j+k) :
    coeff0 (T-1) p * (p.factorial : ℤ) * ((j+k-1).factorial : ℤ) =
      ((T-1).factorial : ℤ) := by
  have hp : p ≤ T-1 := by omega
  have hdiff : T-1-p=j+k-1 := by omega
  have hsum : p+(T-1-p)=T-1 := by omega
  have hsum' : p+(j+k-1)=T-1 := by omega
  have hc := choose_factorial_int (T-1) p hp
  simpa only [coeff0, hdiff, hsum', ite_true] using hc

/-- The a<b indicator is retained. The j<k indicator remains in HalfInputIndex. -/
theorem sourceCoefficient_closed (T p j k a : ℕ)
    (hT : p+j+k=T) (hjk : 1 ≤ j+k) :
    sourceCoefficient T p j k a =
      if a<p+1-a then
        ((a : ℤ)-((p+1-a : ℕ) : ℤ)) * ((j : ℤ)-(k : ℤ)) *
          ((T-1).factorial : ℤ)
      else 0 := by
  by_cases ha : a<p+1-a
  · simp only [sourceCoefficient, ha, hjk, and_self, if_true]
    calc
      _ = ((a : ℤ)-((p+1-a : ℕ) : ℤ)) *
          (coeff0 (T-1) p * (p.factorial : ℤ)) *
          (coeff1 (j+k) j * (j.factorial : ℤ) * (k.factorial : ℤ)) := by ring
      _ = ((a : ℤ)-((p+1-a : ℕ) : ℤ)) *
          (coeff0 (T-1) p * (p.factorial : ℤ)) *
          (((j : ℤ)-(k : ℤ)) * ((j+k-1).factorial : ℤ)) := by
            rw [coeff1_factorial]
      _ = ((a : ℤ)-((p+1-a : ℕ) : ℤ)) * ((j : ℤ)-(k : ℤ)) *
          (coeff0 (T-1) p * (p.factorial : ℤ) * ((j+k-1).factorial : ℤ)) := by ring
      _ = _ := by rw [coeff0_factorial T p j k hT hjk]
  · simp [sourceCoefficient, ha]

/-- Same original summation set and same original words, with the coefficient simplified. -/
theorem integerSourceWords_closed (T : ℕ) :
    integerSourceWords 1 T 1 =
      ∑ q : HalfInputIndex T, ∑ a : Fin (q.val.1.val+2),
        Finsupp.single ![a.val,q.val.1.val+1-a.val,q.val.2.val,T-q.val.1.val-q.val.2.val]
          (if a.val<q.val.1.val+1-a.val then
            ((a.val : ℤ)-((q.val.1.val+1-a.val : ℕ) : ℤ)) *
            ((q.val.2.val : ℤ)-((T-q.val.1.val-q.val.2.val : ℕ) : ℤ)) *
            ((T-1).factorial : ℤ)
           else 0) := by
  classical
  unfold integerSourceWords
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [sourceCoefficient_sound]
  apply sourceCoefficient_closed
  · have hp := q.val.1.isLt
    have hj := q.val.2.isLt
    omega
  · have hh := q.property
    omega

/- Scalar alternation core. All natural-label values remain symbolic. -/
def pairCut (a b : ℕ) : ℤ := if a<b then (a : ℤ)-(b : ℤ) else 0

theorem pairCut_skew (a b : ℕ) : pairCut a b - pairCut b a = (a : ℤ)-(b : ℤ) := by
  unfold pairCut
  split_ifs <;> omega

def halfKernel (v : Fin 4 → ℕ) : ℤ := pairCut (v 0) (v 1) * pairCut (v 2) (v 3)
def fullKernel (v : Fin 4 → ℕ) : ℤ :=
  ((v 0 : ℤ)-(v 1 : ℤ)) * ((v 2 : ℤ)-(v 3 : ℤ))

def alt (f : (Fin 4 → ℕ) → ℤ) (w : Fin 4 → ℕ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 4), (Equiv.Perm.sign σ : ℤ) * f (w ∘ σ)

private theorem alt_add (f g : (Fin 4 → ℕ) → ℤ) (w : Fin 4 → ℕ) :
    alt (fun v => f v+g v) w = alt f w+alt g w := by
  simp [alt, mul_add, Finset.sum_add_distrib]

private theorem alt_sub (f g : (Fin 4 → ℕ) → ℤ) (w : Fin 4 → ℕ) :
    alt (fun v => f v-g v) w = alt f w-alt g w := by
  simp [alt, mul_sub, Finset.sum_sub_distrib]

/-- Right multiplication reindexes the permutation sum and flips its sign. -/
theorem alt_preSwap (f : (Fin 4 → ℕ) → ℤ) (w : Fin 4 → ℕ)
    (a b : Fin 4) (hab : a ≠ b) :
    alt (fun v => f (v ∘ Equiv.swap a b)) w = -alt f w := by
  have hr := Equiv.sum_comp (Equiv.mulRight (Equiv.swap a b))
    (fun σ : Equiv.Perm (Fin 4) => (Equiv.Perm.sign σ : ℤ) * f (w ∘ σ))
  have he : -alt (fun v => f (v ∘ Equiv.swap a b)) w = alt f w := by
    simpa [alt, Equiv.coe_mulRight, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hab, Units.val_mul, Units.val_neg,
      Equiv.Perm.mul_apply, Function.comp_def, Finset.sum_neg_distrib] using hr
  omega

/-- A product using only two slots is fixed by swapping the other two slots. -/
theorem alt_monomial_zero (w : Fin 4 → ℕ) (i j a b : Fin 4)
    (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    alt (fun v => (v i : ℤ)*(v j : ℤ)) w = 0 := by
  have h := alt_preSwap (fun v => (v i : ℤ)*(v j : ℤ)) w a b hab
  have hf : (fun v : Fin 4 → ℕ =>
        ((v ∘ Equiv.swap a b) i : ℤ)*((v ∘ Equiv.swap a b) j : ℤ)) =
      (fun v : Fin 4 → ℕ => (v i : ℤ)*(v j : ℤ)) := by
    funext v
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hia hib,
      Equiv.swap_apply_of_ne_of_ne hja hjb]
  rw [hf] at h
  omega

theorem alt_fullKernel_zero (w : Fin 4 → ℕ) : alt fullKernel w = 0 := by
  have h02 := alt_monomial_zero w 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h03 := alt_monomial_zero w 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h12 := alt_monomial_zero w 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h13 := alt_monomial_zero w 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf : fullKernel = (fun v : Fin 4 → ℕ =>
      (v 0 : ℤ)*(v 2 : ℤ) - (v 0 : ℤ)*(v 3 : ℤ) -
      (v 1 : ℤ)*(v 2 : ℤ) + (v 1 : ℤ)*(v 3 : ℤ)) := by
    funext v
    unfold fullKernel
    ring
  rw [hf, alt_add, alt_sub, alt_sub, h02, h03, h12, h13]
  norm_num

theorem fullKernel_eq_four_half (v : Fin 4 → ℕ) :
    fullKernel v = halfKernel v - halfKernel (v ∘ Equiv.swap 0 1) -
      halfKernel (v ∘ Equiv.swap 2 3) +
      halfKernel ((v ∘ Equiv.swap 0 1) ∘ Equiv.swap 2 3) := by
  simp only [fullKernel, halfKernel]
  norm_num [Function.comp_def, Equiv.swap_apply_def]
  rw [← pairCut_skew (v 0) (v 1), ← pairCut_skew (v 2) (v 3)]
  ring

/-- This is the complete scalar cancellation, including both ordering indicators. -/
theorem alt_halfKernel_zero (w : Fin 4 → ℕ) : alt halfKernel w = 0 := by
  have h01 := alt_preSwap halfKernel w 0 1 (by decide)
  have h23 := alt_preSwap halfKernel w 2 3 (by decide)
  have hboth := alt_preSwap (fun v => halfKernel (v ∘ Equiv.swap 2 3)) w 0 1 (by decide)
  have he : fullKernel = (fun v => halfKernel v - halfKernel (v ∘ Equiv.swap 0 1) -
      halfKernel (v ∘ Equiv.swap 2 3) +
      halfKernel ((v ∘ Equiv.swap 0 1) ∘ Equiv.swap 2 3)) :=
    funext fullKernel_eq_four_half
  have hz := alt_fullKernel_zero w
  rw [he, alt_add, alt_sub, alt_sub, h01, hboth, h23] at hz
  omega

end DegreeOneAlgebraCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.coeff1_factorial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.coeff0_factorial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.sourceCoefficient_closed
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.integerSourceWords_closed
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.pairCut_skew
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.alt_preSwap
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.alt_monomial_zero
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.alt_fullKernel_zero
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.fullKernel_eq_four_half
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.DegreeOneAlgebraCandidate.alt_halfKernel_zero
