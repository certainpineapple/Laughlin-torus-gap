import torus.shared.FermionLocalJetFourCouplingIntegerWords
import Mathlib.GroupTheory.Perm.Fin

/-!
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json.
An earlier draft had a list-negation commutativity error; the selected source
is the version accepted by the complete local rebuild.
No native evaluation is used. The only final decision procedures operate on
an inductive trie containing lists of four-tuples and integers. Soundness is
proved by interpreting that data back into the ORIGINAL IntegerFourWords.

The trie key is only an acceleration hint: collisions do not affect soundness,
because a leaf still compares the complete four-tuple. There is deliberately
no support cutoff, injectivity premise, or assumed source/ladder identity.
-/
set_option autoImplicit false
set_option maxRecDepth 262144
set_option maxHeartbeats 0

namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate
open scoped BigOperators

namespace SourceCheckReflection01

structure Word where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

def Word.vec (w : Word) : Fin 4 → ℕ := ![w.a,w.b,w.c,w.d]
def Word.ofVec (v : Fin 4 → ℕ) : Word := ⟨v 0,v 1,v 2,v 3⟩

@[simp] theorem Word.vec_ofVec (v : Fin 4 → ℕ) : (Word.ofVec v).vec = v := by
  funext i
  fin_cases i <;> rfl

structure Term where
  word : Word
  coeff : ℤ
  deriving DecidableEq

noncomputable def Term.meaning (t : Term) : IntegerFourWords :=
  Finsupp.single t.word.vec t.coeff

noncomputable def meaning (ts : List Term) : IntegerFourWords :=
  (ts.map Term.meaning).sum

@[simp] theorem meaning_nil : meaning [] = 0 := rfl
@[simp] theorem meaning_cons (t : Term) (ts : List Term) :
    meaning (t::ts) = t.meaning + meaning ts := rfl
@[simp] theorem meaning_append (s t : List Term) :
    meaning (s++t) = meaning s+meaning t := by
  simp [meaning]

def singletonTerm (t : Term) : List Term :=
  if t.coeff=0 then [] else [t]

@[simp] theorem meaning_singletonTerm (t : Term) :
    meaning (singletonTerm t) = t.meaning := by
  by_cases h : t.coeff=0 <;> simp [singletonTerm,h,Term.meaning]

def collect {n : ℕ} (f : Fin n → List Term) : List Term := (List.ofFn f).flatten

@[simp] theorem meaning_collect {n : ℕ} (f : Fin n → List Term) :
    meaning (collect f) = ∑ i, meaning (f i) := by
  simp [meaning,collect,List.map_flatten,List.sum_flatten,List.map_map,
    List.map_ofFn,List.sum_ofFn]

/- The zero and first polynomial rows, with ALL arithmetic data executable. -/
def coeff0 (n p : ℕ) : ℤ :=
  if p+(n-p)=n then (n.choose p : ℤ) else 0

def coeff1 (n p : ℕ) : ℤ :=
  (if p≠0 then
    if p-1+(n-p)=n-1 then ((n-1).choose (p-1) : ℤ) else 0 else 0) -
  (if n-p≠0 then
    if p+(n-p-1)=n-1 then ((n-1).choose p : ℤ) else 0 else 0)

private theorem exponent_sub0 (j k : ℕ) :
    twoExponent j k - Finsupp.single 0 1 = twoExponent (j-1) k := by
  ext i
  fin_cases i <;> simp [twoExponent]

private theorem exponent_sub1 (j k : ℕ) :
    twoExponent j k - Finsupp.single 1 1 = twoExponent j (k-1) := by
  ext i
  fin_cases i <;> simp [twoExponent]

theorem coeff0_sound (n p : ℕ) : integerS45Coefficient 0 n p = coeff0 n p := by
  simp [integerS45Coefficient,integerS45Polynomial,coeff0,
    MvPolynomial.coeff_add_pow,twoExponent]

theorem coeff1_sound (n p : ℕ) : integerS45Coefficient 1 n p = coeff1 n p := by
  classical
  unfold integerS45Coefficient integerS45Polynomial
  rw [pow_one,sub_mul,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
    MvPolynomial.coeff_X_mul',MvPolynomial.coeff_X_mul']
  simp only [exponent_sub0,exponent_sub1]
  simp [coeff1,MvPolynomial.coeff_add_pow,twoExponent]

def sourceCoefficient (T p j k a : ℕ) : ℤ :=
  if a<p+1-a ∧ 1≤j+k then
    coeff1 (j+k) j * coeff0 (T-1) p *
      ((a:ℤ)-((p+1-a:ℕ):ℤ)) *
      (p.factorial:ℤ) * (j.factorial:ℤ) * (k.factorial:ℤ)
  else 0

theorem sourceCoefficient_sound (T p j k a : ℕ) :
    integerPairSpectatorCoefficient 1 T 1 p j k a =
      sourceCoefficient T p j k a := by
  simp only [integerPairSpectatorCoefficient,Nat.sub_self,coeff0_sound,coeff1_sound,
    sourceCoefficient]

def sourceTerms (T : ℕ) : List Term :=
  collect fun p : Fin (T+1) =>
    collect fun j : Fin (T-p.val+1) =>
      if j.val<T-p.val-j.val then
        collect fun a : Fin (p.val+2) =>
          singletonTerm ⟨⟨a.val,p.val+1-a.val,j.val,T-p.val-j.val⟩,
            sourceCoefficient T p.val j.val (T-p.val-j.val) a.val⟩
      else []

theorem sourceTerms_sound (T : ℕ) :
    meaning (sourceTerms T) = integerSourceWords 1 T 1 := by
  classical
  rw [integerSourceWords]
  rw [halfInput_sum T (fun q : InputIndex T =>
    ∑ a : Fin (q.1.val+2),
      Finsupp.single ![a.val,q.1.val+1-a.val,q.2.val,T-q.1.val-q.2.val]
        (integerPairSpectatorCoefficient 1 T 1 q.1.val q.2.val
          (T-q.1.val-q.2.val) a.val))]
  simp only [sourceTerms,meaning_collect]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [meaning_collect,Term.meaning,Word.vec,sourceCoefficient_sound]

/- Reification of the ORIGINAL lower and raise maps, without support cutoffs. -/
def lowerTerm (t : Term) : List Term :=
  collect fun a : Fin 4 =>
    if t.word.vec a=0 then []
    else [⟨Word.ofVec (Function.update t.word.vec a (t.word.vec a-1)),t.coeff⟩]

def raiseTerm (t : Term) : List Term :=
  collect fun a : Fin 4 =>
    [⟨Word.ofVec (Function.update t.word.vec a (t.word.vec a+1)),
      t.coeff * ((t.word.vec a+1:ℕ):ℤ)⟩]

theorem lowerTerm_sound (t : Term) :
    meaning (lowerTerm t) = lowerIntegerFourWords t.meaning := by
  classical
  simp only [lowerTerm,meaning_collect,Term.meaning,lowerIntegerFourWords,
    Finsupp.linearCombination_single,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp [Term.meaning,Finsupp.smul_single,smul_eq_mul]

theorem raiseTerm_sound (t : Term) :
    meaning (raiseTerm t) = raiseIntegerFourWords t.meaning := by
  classical
  simp [raiseTerm,meaning_collect,Term.meaning,raiseIntegerFourWords,
    Finsupp.linearCombination_single,Finset.smul_sum,Finsupp.smul_single,smul_eq_mul,
    mul_add,Finsupp.single_add]

def lowerTerms (ts : List Term) : List Term := ts.flatMap lowerTerm
def raiseTerms (ts : List Term) : List Term := ts.flatMap raiseTerm

theorem lowerTerms_sound (ts : List Term) :
    meaning (lowerTerms ts) = lowerIntegerFourWords (meaning ts) := by
  induction ts with
  | nil => simp [lowerTerms]
  | cons t ts ih => simp [lowerTerms,List.flatMap_cons,lowerTerm_sound,← ih]

theorem raiseTerms_sound (ts : List Term) :
    meaning (raiseTerms ts) = raiseIntegerFourWords (meaning ts) := by
  induction ts with
  | nil => simp [raiseTerms]
  | cons t ts ih => simp [raiseTerms,List.flatMap_cons,raiseTerm_sound,← ih]

/- Executable enumeration, carrying the sign as an INTEGER, not reducing sign. -/
def signedPerms : (n : ℕ) → List (Equiv.Perm (Fin n) × ℤ)
  | 0 => [(1,1)]
  | n+1 => (List.ofFn fun i : Fin (n+1) =>
      (signedPerms n).map fun q =>
        (Equiv.Perm.decomposeFin.symm (i,q.1),
          (if i=0 then (1:ℤ) else -1)*q.2)).flatten

private theorem list_sum_zsmul {A M : Type*} [AddCommGroup M]
    (xs : List A) (f : A → M) (k : ℤ) :
    (xs.map (fun x => k • f x)).sum = k • (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,smul_add]

private theorem list_sum_neg' {A M : Type*} [AddCommGroup M]
    (xs : List A) (f : A → M) :
    (xs.map (fun x => -f x)).sum = -(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,neg_add,add_comm]

theorem signedPerms_sound {M : Type*} [AddCommGroup M]
    (n : ℕ) (f : Equiv.Perm (Fin n) → M) :
    ((signedPerms n).map fun q => q.2 • f q.1).sum =
      ∑ σ, (Equiv.Perm.sign σ:ℤ) • f σ := by
  classical
  induction n with
  | zero => simp [signedPerms]
  | succ n ih =>
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm
      (fun σ : Equiv.Perm (Fin (n+1)) => (Equiv.Perm.sign σ:ℤ) • f σ)]
    rw [Fintype.sum_prod_type]
    simp only [signedPerms,List.map_flatten,List.sum_flatten,List.map_map,
      List.map_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i hi
    have hs := ih (fun σ => f (Equiv.Perm.decomposeFin.symm (i,σ)))
    by_cases hi0 : i=0
    · simpa [Function.comp_def,Equiv.Perm.decomposeFin.symm_sign,hi0] using hs
    · simpa [Function.comp_def,Equiv.Perm.decomposeFin.symm_sign,hi0,
        Units.val_neg,neg_smul,list_sum_neg',Finset.sum_neg_distrib] using
          congrArg (fun x : M => -x) hs

def alternateTerm (t : Term) : List Term :=
  (signedPerms 4).map fun q =>
    ⟨Word.ofVec (t.word.vec ∘ q.1),q.2*t.coeff⟩

theorem alternateTerm_sound (t : Term) :
    meaning (alternateTerm t) = alternateIntegerFourWords t.meaning := by
  classical
  have h := signedPerms_sound 4
    (fun σ => permuteIntegerFourWords σ t.meaning)
  simpa [meaning,alternateTerm,List.map_map,Function.comp_def,Term.meaning,
    permuteIntegerFourWords,Finsupp.linearCombination_single,Finsupp.smul_single,
    alternateIntegerFourWords,LinearMap.sum_apply,LinearMap.smul_apply] using h

def alternateTerms (ts : List Term) : List Term := ts.flatMap alternateTerm

theorem alternateTerms_sound (ts : List Term) :
    meaning (alternateTerms ts) = alternateIntegerFourWords (meaning ts) := by
  induction ts with
  | nil => simp [alternateTerms]
  | cons t ts ih => simp [alternateTerms,List.flatMap_cons,alternateTerm_sound,← ih]

/- A collision-safe sparse trie, with a proved interpretation homomorphism. -/
def addTerm (t : Term) : List Term → List Term
  | [] => if t.coeff=0 then [] else [t]
  | u::us =>
      if t.word=u.word then
        if t.coeff+u.coeff=0 then us
        else ⟨u.word,t.coeff+u.coeff⟩::us
      else u::addTerm t us

theorem addTerm_sound (t : Term) (ts : List Term) :
    meaning (addTerm t ts) = t.meaning+meaning ts := by
  classical
  induction ts with
  | nil =>
    by_cases h : t.coeff=0 <;> simp [addTerm,h,Term.meaning]
  | cons u us ih =>
    by_cases hw : t.word=u.word
    · by_cases hc : t.coeff+u.coeff=0
      · have hz : t.meaning+u.meaning=0 := by
          simp only [Term.meaning,hw,← Finsupp.single_add,hc,Finsupp.single_zero]
        simp only [addTerm,if_pos hw,if_pos hc,meaning_cons]
        rw [← add_assoc,hz,zero_add]
      · simp [addTerm,hw,hc,Term.meaning,hw,Finsupp.single_add,add_assoc]
    · simp [addTerm,hw,ih,add_comm,add_left_comm,add_assoc]

inductive Trie : ℕ → Type
  | empty {n : ℕ} : Trie n
  | leaf (ts : List Term) : Trie 0
  | node {n : ℕ} (l r : Trie n) : Trie (n+1)
  deriving DecidableEq

noncomputable def trieMeaning : {n : ℕ} → Trie n → IntegerFourWords
  | _,.empty => 0
  | _,.leaf ts => meaning ts
  | _,.node l r => trieMeaning l+trieMeaning r

def mkLeaf (ts : List Term) : Trie 0 :=
  match ts with
  | [] => .empty
  | _::_ => .leaf ts

def mkNode {n : ℕ} (l r : Trie n) : Trie (n+1) :=
  match l,r with
  | .empty,.empty => .empty
  | _,_ => .node l r

@[simp] theorem trieMeaning_mkLeaf (ts : List Term) :
    trieMeaning (mkLeaf ts) = meaning ts := by
  cases ts <;> rfl

@[simp] theorem trieMeaning_mkNode {n : ℕ} (l r : Trie n) :
    trieMeaning (mkNode l r) = trieMeaning l+trieMeaning r := by
  cases l <;> cases r <;> simp [mkNode,trieMeaning]

-- No injectivity or bound is required for this hash.
def wordKey (w : Word) : ℕ := w.a+32*w.b+1024*w.c+32768*w.d

def insert : {n : ℕ} → ℕ → Term → Trie n → Trie n
  | 0,_,t,.empty => mkLeaf (addTerm t [])
  | 0,_,t,.leaf ts => mkLeaf (addTerm t ts)
  | n+1,k,t,.empty =>
      if k%2=0 then mkNode (insert (k/2) t (.empty : Trie n)) .empty
      else mkNode .empty (insert (k/2) t (.empty : Trie n))
  | n+1,k,t,.node l r =>
      if k%2=0 then mkNode (insert (k/2) t l) r
      else mkNode l (insert (k/2) t r)

theorem insert_sound {n : ℕ} (k : ℕ) (t : Term) (tr : Trie n) :
    trieMeaning (insert k t tr) = t.meaning+trieMeaning tr := by
  induction n generalizing k with
  | zero => cases tr <;> simp [insert,trieMeaning,addTerm_sound]
  | succ n ih =>
    cases tr <;> simp only [insert] <;> split_ifs <;>
      simp [trieMeaning,ih,add_comm,add_left_comm,add_assoc]

def pack : List Term → Trie 20
  | [] => .empty
  | t::ts => insert (wordKey t.word) t (pack ts)

theorem pack_sound (ts : List Term) : trieMeaning (pack ts) = meaning ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa only [pack,insert_sound,meaning_cons,ih]

theorem meaning_eq_zero_of_pack (ts : List Term) (h : pack ts = .empty) :
    meaning ts = 0 := by
  rw [← pack_sound,h]
  rfl

def vacuumCheck : Prop := pack (alternateTerms (lowerTerms (sourceTerms 1))) = .empty

def raiseCheck (T : ℕ) : Prop :=
  pack (alternateTerms (raiseTerms (sourceTerms T))) = .empty ∧
  pack (alternateTerms (sourceTerms (T+1))) = .empty

instance : Decidable vacuumCheck := inferInstanceAs (Decidable (_ = _))
instance (T : ℕ) : Decidable (raiseCheck T) :=
  inferInstanceAs (Decidable ((_ = _) ∧ (_ = _)))

theorem vacuumCheck_sound (h : vacuumCheck) :
    alternateIntegerFourWords (lowerIntegerFourWords (integerSourceWords 1 1 1)) = 0 := by
  have hs := meaning_eq_zero_of_pack _ h
  simpa only [alternateTerms_sound,lowerTerms_sound,sourceTerms_sound] using hs

theorem raiseCheck_sound (T : ℕ) (h : raiseCheck T) :
    alternateIntegerFourWords (raiseIntegerFourWords (integerSourceWords 1 T 1)) =
      alternateIntegerFourWords (integerSourceWords 1 (T+1) 1) := by
  have hl := meaning_eq_zero_of_pack _ h.1
  have hr := meaning_eq_zero_of_pack _ h.2
  simp only [alternateTerms_sound,raiseTerms_sound,sourceTerms_sound] at hl hr
  exact hl.trans hr.symm

theorem oddMode_one (r : OddMode 1) : r.val.val=1 := by
  have hr := r.property
  have hb := r.val.isLt
  rcases hr with ⟨k,hk⟩
  omega

end SourceCheckReflection01

open SourceCheckReflection01


#print axioms SourceCheckReflection01.sourceTerms_sound
#print axioms SourceCheckReflection01.alternateTerms_sound
#print axioms SourceCheckReflection01.pack_sound
end TorusLean.Shared.FermionLocalJet.FourCoupling
