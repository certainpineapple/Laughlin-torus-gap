import torus.shared.FermionLocalJetFourCouplingAllDegrees
import Mathlib.Data.Matrix.Mul

/-! Completeness, not just Bessel, of the literal S transformation at total T.
A square indexing of all j<k inputs also enumerates every odd relative copy
(D,r) exactly once: r=2h+1 and D=n+r. The enumeration is proved explicitly.
The matrix inverse is taken only for the formal orthogonal S transform,
never for the physical wedge Gram matrix G_D. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators ComplexConjugate

abbrev HalfInputIndex (T : ℕ) := {q : InputIndex T // q.2.val<T-q.1.val-q.2.val}

/-- Copy-coordinate label h corresponds to the odd relative mode 2h+1. -/
def fullCopyRelative (T : ℕ) (c : HalfInputIndex T) : ℕ := 2*c.val.2.val+1

/-- The other coordinate n is D-r, not the COM descendant degree T-D. -/
def fullCopyDegree (T : ℕ) (c : HalfInputIndex T) : ℕ := c.val.1.val+fullCopyRelative T c

theorem fullCopy_range (T : ℕ) (c : HalfInputIndex T) :
    Odd (fullCopyRelative T c) ∧ fullCopyRelative T c≤fullCopyDegree T c ∧
      fullCopyDegree T c≤T := by
  have hp := c.val.1.isLt
  have hj := c.val.2.isLt
  have hh := c.property
  refine ⟨⟨c.val.2.val,by unfold fullCopyRelative; omega⟩,?_,?_⟩ <;>
    unfold fullCopyDegree fullCopyRelative <;> omega

theorem fullCopy_eq_iff (T : ℕ) (c d : HalfInputIndex T) :
    (fullCopyDegree T c=fullCopyDegree T d ∧ fullCopyRelative T c=fullCopyRelative T d) ↔ c=d := by
  constructor
  · rintro ⟨hD,hr⟩
    rcases c with ⟨⟨p,j⟩,hc⟩
    rcases d with ⟨⟨p',j'⟩,hd⟩
    dsimp only [fullCopyDegree,fullCopyRelative] at hD hr
    have hj : j.val=j'.val := by omega
    have hp : p=p' := Fin.ext (by omega)
    subst p'
    have hj' : j=j' := Fin.ext hj
    subst j'
    rfl
  · rintro rfl
    exact ⟨rfl,rfl⟩

/-- No original odd copy is omitted, including columns with zero wedge image. -/
theorem fullCopy_surjective (T D r : ℕ) (hD : D≤T) (hrD : r≤D) (hr : Odd r) :
    ∃ c : HalfInputIndex T, fullCopyDegree T c=D ∧ fullCopyRelative T c=r := by
  rcases hr with ⟨h,hh⟩
  have hp : D-r<T+1 := by omega
  have hj : h<T-(D-r)+1 := by omega
  have hhalf : h<T-(D-r)-h := by omega
  let c : HalfInputIndex T :=
    ⟨⟨⟨D-r,hp⟩,⟨h,hj⟩⟩,hhalf⟩
  refine ⟨c,?_,?_⟩ <;> dsimp only [fullCopyDegree,fullCopyRelative,c] <;> omega

theorem halfInput_sum {V : Type*} [AddCommMonoid V] (T : ℕ) (f : InputIndex T → V) :
    (∑ q : HalfInputIndex T, f q.val) =
      ∑ p : Fin (T+1), ∑ j : Fin (T-p.val+1),
        if j.val<T-p.val-j.val then f ⟨p,j⟩ else 0 := by
  classical
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q : InputIndex T => q.2.val<T-q.1.val-q.2.val), f q :=
      (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by rw [Finset.sum_filter,Fintype.sum_sigma]

/-- Actual original S_r(D,T;p,j,k), on the complete finite input and copy sets. -/
def completeS45 (T : ℕ) (c q : HalfInputIndex T) : ℂ :=
  paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T
    q.val.1.val q.val.2.val (T-q.val.1.val-q.val.2.val)

theorem completeS45_star (T : ℕ) (c q : HalfInputIndex T) :
    star (completeS45 T c q)=completeS45 T c q := paperS45_star _ _ _ _ _ _

theorem completeS45_rows (T : ℕ) (c d : HalfInputIndex T) :
    (∑ q : HalfInputIndex T, star (completeS45 T c q) * completeS45 T d q) =
      if c=d then 1 else 0 := by
  classical
  have hc := fullCopy_range T c
  have hd := fullCopy_range T d
  unfold completeS45
  rw [halfInput_sum T (fun q : InputIndex T =>
    star (paperS45 (fullCopyRelative T c) (fullCopyDegree T c) T
      q.1.val q.2.val (T-q.1.val-q.2.val)) *
    paperS45 (fullCopyRelative T d) (fullCopyDegree T d) T
      q.1.val q.2.val (T-q.1.val-q.2.val))]
  rw [paperS45_rows_orthonormal _ _ _ _ _ hc.2.2 hd.2.2 hc.2.1 hd.2.1 hc.1 hd.1]
  simp only [fullCopy_eq_iff]

/-- Column completeness follows from the square real orthogonal transform.
This is independent of all physical raw-jet or exterior-image inner products. -/
theorem completeS45_columns (T : ℕ) (q v : HalfInputIndex T) :
    (∑ c : HalfInputIndex T, completeS45 T c q * completeS45 T c v) =
      if q=v then 1 else 0 := by
  classical
  let M : Matrix (HalfInputIndex T) (HalfInputIndex T) ℂ := completeS45 T
  have hM : M * M.transpose=1 := by
    ext c d
    change (∑ u : HalfInputIndex T, M c u * M d u) = if c=d then 1 else 0
    simpa only [M,completeS45_star] using completeS45_rows T c d
  have hMt : M.transpose * M=1 := mul_eq_one_comm.mp hM
  have he := congrFun (congrFun hMt q) v
  change (∑ c : HalfInputIndex T, M c q * M c v) = (if q=v then 1 else 0) at he
  exact he

/-- Exact reconstruction after arbitrary linear substitution, in particular
the genuine full-Fock c_k c_j B_p coordinates. No Gram premise is supplied. -/
theorem completeS45_reconstruct {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : ℕ) (a : HalfInputIndex T → V) (q : HalfInputIndex T) :
    (∑ c : HalfInputIndex T, completeS45 T c q •
      (∑ v : HalfInputIndex T, completeS45 T c v • a v)) = a q := by
  classical
  simp only [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,completeS45_columns]
  simp

#print axioms fullCopy_range
#print axioms fullCopy_eq_iff
#print axioms fullCopy_surjective
#print axioms halfInput_sum
#print axioms completeS45_star
#print axioms completeS45_rows
#print axioms completeS45_columns
#print axioms completeS45_reconstruct
end TorusLean.Shared.FermionLocalJet.FourCoupling
