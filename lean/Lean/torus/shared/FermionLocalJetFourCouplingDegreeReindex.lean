import torus.shared.FermionLocalJetFourCouplingComplete

/-! Exact finite reindexing of the complete original coupling basis.
The codomain includes every odd copy in every degree1..23, including zero
and dependent exterior columns.  Only the original D<=T support is imposed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

abbrev FourCopy := (d : Fin 23) × OddMode (d.val+1)
abbrev FourCopyBelow (T : ℕ) := {c : FourCopy // c.1.val+1≤T}

def fullCopyToBelow (T : ℕ) (hT : T≤23) (c : HalfInputIndex T) : FourCopyBelow T := by
  have h := fullCopy_range T c
  have hpos : 1≤fullCopyDegree T c := by unfold fullCopyDegree fullCopyRelative; omega
  let d : Fin 23 := ⟨fullCopyDegree T c-1,by omega⟩
  let r : OddMode (d.val+1) := ⟨⟨fullCopyRelative T c,by dsimp [d]; omega⟩,h.1⟩
  exact ⟨⟨d,r⟩,by dsimp [d]; omega⟩

theorem fullCopyToBelow_degree (T : ℕ) (hT : T≤23) (c : HalfInputIndex T) :
    (fullCopyToBelow T hT c).val.1.val+1=fullCopyDegree T c := by
  have hpos : 1≤fullCopyDegree T c := by unfold fullCopyDegree fullCopyRelative; omega
  change fullCopyDegree T c-1+1=fullCopyDegree T c
  omega

theorem fullCopyToBelow_relative (T : ℕ) (hT : T≤23) (c : HalfInputIndex T) :
    (fullCopyToBelow T hT c).val.2.val.val=fullCopyRelative T c := rfl

theorem fullCopyToBelow_bijective (T : ℕ) (hT : T≤23) :
    Function.Bijective (fullCopyToBelow T hT) := by
  constructor
  · intro c e h
    apply (fullCopy_eq_iff T c e).mp
    constructor
    · have hh := congrArg (fun z : FourCopyBelow T => z.val.1.val+1) h
      simpa only [fullCopyToBelow_degree] using hh
    · have hh := congrArg (fun z : FourCopyBelow T => z.val.2.val.val) h
      simpa only [fullCopyToBelow_relative] using hh
  · rintro ⟨⟨d,r⟩,hd⟩
    obtain ⟨c,hD,hr⟩ := fullCopy_surjective T (d.val+1) r.val.val hd
      (Nat.le_of_lt_succ r.val.isLt) r.property
    refine ⟨c,?_⟩
    apply Subtype.ext
    have he : (fullCopyToBelow T hT c).val.1=d := by
      apply Fin.ext
      have hh := fullCopyToBelow_degree T hT c
      omega
    apply Sigma.ext he
    cases he
    apply heq_of_eq
    apply Subtype.ext
    apply Fin.ext
    exact hr

def fullCopyBelowEquiv (T : ℕ) (hT : T≤23) : HalfInputIndex T ≃ FourCopyBelow T :=
  Equiv.ofBijective (fullCopyToBelow T hT) (fullCopyToBelow_bijective T hT)

/-- The original full coupling set is exactly the guarded degree/copy sum. -/
theorem fullCopy_sum_degrees {V : Type*} [AddCommMonoid V]
    (T : ℕ) (hT : T≤23) (f : FourCopy → V) :
    (∑ c : HalfInputIndex T, f (fullCopyToBelow T hT c).val) =
      ∑ d : Fin 23, ∑ r : OddMode (d.val+1), if d.val+1≤T then f ⟨d,r⟩ else 0 := by
  classical
  calc
    _ = ∑ c : FourCopyBelow T, f c.val :=
      (fullCopyBelowEquiv T hT).sum_comp (fun c => f c.val)
    _ = ∑ c ∈ Finset.univ.filter (fun c : FourCopy => c.1.val+1≤T), f c :=
      (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by rw [Finset.sum_filter,Fintype.sum_sigma]

/-- Only equality of the two relative degrees is imposed. Within each degree
all r,s entries of F remain, with their original signs and ordering. -/
theorem fullCopy_double_sum_degree_diagonal (T : ℕ) (hT : T≤23)
    (F : FourCopy → FourCopy → ℂ) :
    (∑ c : HalfInputIndex T, ∑ e : HalfInputIndex T,
      if (fullCopyToBelow T hT c).val.1=(fullCopyToBelow T hT e).val.1 then
        F (fullCopyToBelow T hT c).val (fullCopyToBelow T hT e).val else 0) =
    ∑ d : Fin 23, ∑ r : OddMode (d.val+1), ∑ s : OddMode (d.val+1),
      if d.val+1≤T then F ⟨d,r⟩ ⟨d,s⟩ else 0 := by
  classical
  rw [fullCopy_sum_degrees T hT (fun c =>
    ∑ e : HalfInputIndex T, if c.1=(fullCopyToBelow T hT e).val.1 then
      F c (fullCopyToBelow T hT e).val else 0)]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro r hr
  rw [fullCopy_sum_degrees T hT (fun e => if d=e.1 then F ⟨d,r⟩ e else 0)]
  by_cases h : d.val+1≤T
  · simp only [if_pos h]
    rw [Finset.sum_eq_single d]
    · simp [h]
    · intro e he hed
      simp [Ne.symm hed]
    · simp
  · simp [h]

#print axioms fullCopyToBelow_degree
#print axioms fullCopyToBelow_relative
#print axioms fullCopyToBelow_bijective
#print axioms fullCopy_sum_degrees
#print axioms fullCopy_double_sum_degree_diagonal
end TorusLean.Shared.FermionLocalJet.FourCoupling
