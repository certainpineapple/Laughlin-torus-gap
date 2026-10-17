import torus.shared.FermionLocalJetFourCouplingGeneralSourceEncoding
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json.

The source bridge below works for every r ≤ D ≤ T, without a parity
hypothesis. Oddness is needed later for the spectator antisymmetry, not here.
No vacuum, raising, finite certificate, or numerical interpolation premise
occurs in this file. The only pre-existing coefficient identity used is the
proved `difference_sum_power_coeff` for the original signed pair polynomial.

The key block-coefficient lemma is valid for an ARBITRARY two-variable
polynomial. Its proof uses monomial/add induction, separated variable blocks,
and homogeneous-degree exclusion. Consequently no four-variable expansion
or bounded support truncation is necessary.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open GeneralSourcePolynomialCandidate GeneralSourceEncodingCandidate
namespace GeneralSourceCoefficientBridgeCandidate

abbrev TwoPolynomial := MvPolynomial (Fin 2) ℤ

def exponentOfWord (w : Fin 4 → ℕ) : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm w

def fourExponent (a b j k : ℕ) : Fin 4 →₀ ℕ := exponentOfWord ![a,b,j,k]

@[simp] theorem exponentOfWord_apply (w : Fin 4 → ℕ) (i : Fin 4) :
    exponentOfWord w i = w i := rfl

@[simp] theorem twoExponent_eta (m : Fin 2 →₀ ℕ) : twoExponent (m 0) (m 1) = m := by
  ext i
  fin_cases i <;> simp [twoExponent]

@[simp] theorem twoExponent_degree (a b : ℕ) : (twoExponent a b).degree = a+b := by
  simp [twoExponent,map_add]

@[simp] theorem exponentOfWord_degree (w : Fin 4 → ℕ) :
    (exponentOfWord w).degree = ∑ i : Fin 4, w i := by
  rw [Finsupp.degree_eq_sum]
  rfl

def leftEmbedding : Fin 2 → Fin 4 := ![0,1]
def rightEmbedding : Fin 2 → Fin 4 := ![2,3]

theorem left_mapDomain (m : Fin 2 →₀ ℕ) :
    m.mapDomain leftEmbedding = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
  conv_lhs => rw [← twoExponent_eta m]
  simp [twoExponent,Finsupp.mapDomain_add,Finsupp.mapDomain_single,leftEmbedding]

theorem right_mapDomain (m : Fin 2 →₀ ℕ) :
    m.mapDomain rightEmbedding = Finsupp.single 2 (m 0) + Finsupp.single 3 (m 1) := by
  conv_lhs => rw [← twoExponent_eta m]
  simp [twoExponent,Finsupp.mapDomain_add,Finsupp.mapDomain_single,rightEmbedding]

/-- The split exponent is unique; this is the entire tensor support argument. -/
theorem splitExponent_eq_iff (m n : Fin 2 →₀ ℕ) (a b j k : ℕ) :
    m.mapDomain leftEmbedding + n.mapDomain rightEmbedding = fourExponent a b j k ↔
      m=twoExponent a b ∧ n=twoExponent j k := by
  rw [left_mapDomain,right_mapDomain]
  constructor
  · intro h
    have h0 := congrArg (fun d : Fin 4 →₀ ℕ => d 0) h
    have h1 := congrArg (fun d : Fin 4 →₀ ℕ => d 1) h
    have h2 := congrArg (fun d : Fin 4 →₀ ℕ => d 2) h
    have h3 := congrArg (fun d : Fin 4 →₀ ℕ => d 3) h
    simp [fourExponent] at h0 h1 h2 h3
    constructor
    · ext i
      fin_cases i <;> simp [twoExponent,h0,h1]
    · ext i
      fin_cases i <;> simp [twoExponent,h2,h3]
  · rintro ⟨rfl,rfl⟩
    ext i
    fin_cases i <;> simp [twoExponent,fourExponent]

/-- Coefficients of disjoint polynomial blocks multiply with no binomial
or factorial prefactor. Both polynomials are completely arbitrary. -/
theorem coeff_separated_blocks (f g : TwoPolynomial) (a b j k : ℕ) :
    (MvPolynomial.rename leftEmbedding f * MvPolynomial.rename rightEmbedding g).coeff
      (fourExponent a b j k) = f.coeff (twoExponent a b) * g.coeff (twoExponent j k) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f₁ f₂ hf₁ hf₂ =>
    simp only [map_add,add_mul,MvPolynomial.coeff_add,hf₁,hf₂]
  | monomial m z =>
    induction g using MvPolynomial.induction_on' with
    | add g₁ g₂ hg₁ hg₂ =>
      simp only [map_add,mul_add,MvPolynomial.coeff_add,hg₁,hg₂]
    | monomial n t =>
      simp only [MvPolynomial.rename_monomial,MvPolynomial.monomial_mul_monomial,
        MvPolynomial.coeff_monomial,splitExponent_eq_iff]
      by_cases hm : m=twoExponent a b <;> by_cases hn : n=twoExponent j k <;>
        simp [hm,hn]

def pairBlock (p : ℕ) : TwoPolynomial :=
  (MvPolynomial.X 0-MvPolynomial.X 1) * (MvPolynomial.X 0+MvPolynomial.X 1)^p

def spectatorBlock (r q : ℕ) : TwoPolynomial :=
  (MvPolynomial.X 0-MvPolynomial.X 1)^r * (MvPolynomial.X 0+MvPolynomial.X 1)^q

def pairSum : FourPolynomial := MvPolynomial.X 0+MvPolynomial.X 1
def spectatorSum : FourPolynomial := MvPolynomial.X 2+MvPolynomial.X 3

def blockSubstitute : TwoPolynomial →+* FourPolynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![pairSum,spectatorSum]

theorem pairBlock_homogeneous (p : ℕ) : (pairBlock p).IsHomogeneous (p+1) := by
  have hx (i : Fin 2) : (MvPolynomial.X i : TwoPolynomial).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℤ i
  simpa [pairBlock,one_mul,Nat.add_comm] using
    ((hx 0).sub (hx 1)).mul (((hx 0).add (hx 1)).pow p)

theorem spectatorBlock_homogeneous (r q : ℕ) :
    (spectatorBlock r q).IsHomogeneous (r+q) := by
  have hx (i : Fin 2) : (MvPolynomial.X i : TwoPolynomial).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℤ i
  simpa [spectatorBlock,one_mul] using
    (((hx 0).sub (hx 1)).pow r).mul (((hx 0).add (hx 1)).pow q)

theorem pairBlock_coeff_zero (p a b : ℕ) (h : a+b≠p+1) :
    (pairBlock p).coeff (twoExponent a b)=0 :=
  (pairBlock_homogeneous p).coeff_eq_zero (by simpa using h)

theorem spectatorBlock_coeff_zero (r q j k : ℕ) (h : j+k≠r+q) :
    (spectatorBlock r q).coeff (twoExponent j k)=0 :=
  (spectatorBlock_homogeneous r q).coeff_eq_zero (by simpa using h)

/-- Clearing the two pair factorials preserves the sign a-b, including a=0
or b=0. The imported theorem is already proved for all boundary cases. -/
theorem pairBlock_coeff_factorial (p a b : ℕ) (hab : a+b=p+1) :
    (pairBlock p).coeff (twoExponent a b) * (a.factorial : ℤ) * (b.factorial : ℤ) =
      ((a : ℤ)-(b : ℤ)) * (p.factorial : ℤ) := by
  have hm : ((pairBlock p).coeff (twoExponent a b) : ℂ) =
      (((MvPolynomial.X 0-MvPolynomial.X 1) *
        (MvPolynomial.X 0+MvPolynomial.X 1)^p : MvPolynomial (Fin 2) ℂ).coeff
          (twoExponent a b)) := by
    have h := MvPolynomial.coeff_map (Int.castRingHom ℂ) (pairBlock p) (twoExponent a b)
    simpa only [pairBlock,map_mul,map_pow,map_sub,map_add,MvPolynomial.map_X,
      Int.coe_castRingHom] using h.symm
  have hf (n : ℕ) : (n.factorial : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc : ((pairBlock p).coeff (twoExponent a b) : ℂ) *
      (a.factorial : ℂ) * (b.factorial : ℂ) =
      ((a : ℂ)-(b : ℂ)) * (p.factorial : ℂ) := by
    rw [hm,difference_sum_power_coeff p a b hab]
    field_simp [hf] <;> ring
  exact_mod_cast hc

/-- Monomial substitution, with every coefficient and both variable blocks
shown explicitly. -/
theorem blockSubstitute_monomial (m : Fin 2 →₀ ℕ) (z : ℤ) (r : ℕ) :
    pairDifference * spectatorDifference^r * blockSubstitute (MvPolynomial.monomial m z) =
      MvPolynomial.C z *
        (MvPolynomial.rename leftEmbedding (pairBlock (m 0)) *
          MvPolynomial.rename rightEmbedding (spectatorBlock r (m 1))) := by
  rw [blockSubstitute,MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fin.prod_univ_two]
  simp only [pairBlock,spectatorBlock,map_mul,map_pow,map_sub,map_add,
    MvPolynomial.rename_X,leftEmbedding,rightEmbedding,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  unfold pairDifference spectatorDifference pairSum spectatorSum
  ring

/-- Core coefficient extraction. The outer polynomial f is arbitrary, not
assumed homogeneous or assumed to be the desired source. -/
theorem blockCoefficient (f : TwoPolynomial) (r p a b j k : ℕ)
    (hab : a+b=p+1) (hrjk : r≤j+k) :
    (pairDifference * spectatorDifference^r * blockSubstitute f).coeff (fourExponent a b j k) =
      f.coeff (twoExponent p (j+k-r)) * (pairBlock p).coeff (twoExponent a b) *
        integerS45Coefficient r (j+k) j := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [map_add,mul_add,MvPolynomial.coeff_add,hf,hg,add_mul]
  | monomial m z =>
    rw [blockSubstitute_monomial,MvPolynomial.coeff_C_mul,coeff_separated_blocks]
    by_cases hp : m 0=p
    · by_cases hq : m 1=j+k-r
      · have hm : m=twoExponent p (j+k-r) := by
          rw [← twoExponent_eta m,hp,hq]
        rw [hm]
        simp [twoExponent,integerS45Coefficient,integerS45Polynomial,spectatorBlock,mul_assoc]
      · have hz : (spectatorBlock r (m 1)).coeff (twoExponent j k)=0 :=
          spectatorBlock_coeff_zero r (m 1) j k (by omega)
        have hm : m≠twoExponent p (j+k-r) := by
          intro h
          have hh := congrArg (fun n : Fin 2 →₀ ℕ => n 1) h
          simp [twoExponent] at hh
          exact hq hh
        simp [hz,MvPolynomial.coeff_monomial,hm]
    · have hz : (pairBlock (m 0)).coeff (twoExponent a b)=0 :=
        pairBlock_coeff_zero (m 0) a b (by omega)
      have hm : m≠twoExponent p (j+k-r) := by
        intro h
        have hh := congrArg (fun n : Fin 2 →₀ ℕ => n 0) h
        simp [twoExponent] at hh
        exact hp hh
      simp [hz,MvPolynomial.coeff_monomial,hm]

/-- The spectator degree is at least r, with no assumption on f or a,b. -/
theorem blockCoefficient_below (f : TwoPolynomial) (r a b j k : ℕ) (h : j+k<r) :
    (pairDifference * spectatorDifference^r * blockSubstitute f).coeff (fourExponent a b j k)=0 := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add,mul_add,MvPolynomial.coeff_add,hf,hg,add_zero]
  | monomial m z =>
    rw [blockSubstitute_monomial,MvPolynomial.coeff_C_mul,coeff_separated_blocks,
      spectatorBlock_coeff_zero r (m 1) j k (by omega)]
    ring

/-- Both powers in the outer factor are precisely those of the ORIGINAL
integerS45Polynomial. This is where r≤D≤T is essential. -/
theorem fullSourcePolynomial_blockSubstitute (D T r : ℕ) (hrD : r≤D) (hDT : D≤T) :
    fullSourcePolynomial D T r =
      pairDifference * spectatorDifference^r * blockSubstitute (integerS45Polynomial (D-r) (T-r)) := by
  have hn : T-r-(D-r)=T-D := by omega
  have hd : pairSpectatorDifference=pairSum-spectatorSum := by
    unfold pairSpectatorDifference pairSum spectatorSum
    ring
  have hs : collectiveSum=pairSum+spectatorSum := by
    unfold collectiveSum pairSum spectatorSum
    ring
  simp only [fullSourcePolynomial,blockSubstitute,integerS45Polynomial,map_mul,map_pow,
    map_sub,map_add,MvPolynomial.eval₂Hom_X',Matrix.cons_val_zero,Matrix.cons_val_one,hn,hd,hs]
  ring

theorem fullSourcePolynomial_coeff (D T r p a b j k : ℕ)
    (hrD : r≤D) (hDT : D≤T) (hT : p+j+k=T) (hab : a+b=p+1) (hrjk : r≤j+k) :
    (fullSourcePolynomial D T r).coeff (fourExponent a b j k) =
      integerS45Coefficient (D-r) (T-r) p * (pairBlock p).coeff (twoExponent a b) *
        integerS45Coefficient r (j+k) j := by
  rw [fullSourcePolynomial_blockSubstitute D T r hrD hDT,blockCoefficient _ r p a b j k hab hrjk]
  have hn : T-r-p=j+k-r := by omega
  simp only [integerS45Coefficient,hn]

theorem fullSourcePolynomial_coeff_below (D T r a b j k : ℕ)
    (hrD : r≤D) (hDT : D≤T) (h : j+k<r) :
    (fullSourcePolynomial D T r).coeff (fourExponent a b j k)=0 := by
  rw [fullSourcePolynomial_blockSubstitute D T r hrD hDT]
  exact blockCoefficient_below _ r a b j k h

/-- Exact coefficient formula for E, independent of source homogeneity. -/
theorem factorialWeightedWords_apply (f : FourPolynomial) (w : Fin 4 → ℕ) :
    factorialWeightedWords f w = f.coeff (exponentOfWord w) * integerFactorialWeight w := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add,Finsupp.add_apply,MvPolynomial.coeff_add,hf,hg,add_mul]
  | monomial m z =>
    rw [factorialWeightedWords_monomial,MvPolynomial.coeff_monomial,Finsupp.single_apply]
    have he : (fun i => m i)=w ↔ m=exponentOfWord w := by
      constructor
      · intro h
        ext i
        exact congrFun h i
      · intro h
        subst m
        rfl
    by_cases h : m=exponentOfWord w
    · subst m
      simp
    · simp [h,he]

/-- Signed, denominator-free four-label coefficient. No 2-power or other
scalar remains: E uses the product of all four factorials. -/
theorem fullSourcePolynomial_weighted_coefficient (D T r p a b j k : ℕ)
    (hrD : r≤D) (hDT : D≤T) (hT : p+j+k=T) (hab : a+b=p+1) :
    factorialWeightedWords (fullSourcePolynomial D T r) ![a,b,j,k] =
      if r≤j+k then
        integerS45Coefficient r (j+k) j * integerS45Coefficient (D-r) (T-r) p *
          ((a : ℤ)-(b : ℤ)) * (p.factorial : ℤ) * (j.factorial : ℤ) * (k.factorial : ℤ)
      else 0 := by
  rw [factorialWeightedWords_apply]
  change (fullSourcePolynomial D T r).coeff (fourExponent a b j k) * _ = _
  by_cases h : r≤j+k
  · rw [if_pos h,fullSourcePolynomial_coeff D T r p a b j k hrD hDT hT hab h]
    simp only [integerFactorialWeight,Fin.prod_univ_four,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.tail_cons,Matrix.head_cons]
    have hp := pairBlock_coeff_factorial p a b hab
    calc
      _ = integerS45Coefficient r (j+k) j * integerS45Coefficient (D-r) (T-r) p *
          ((pairBlock p).coeff (twoExponent a b) * (a.factorial : ℤ) * (b.factorial : ℤ)) *
          (j.factorial : ℤ) * (k.factorial : ℤ) := by ring
      _ = _ := by rw [hp]; ring
  · rw [if_neg h,fullSourcePolynomial_coeff_below D T r a b j k hrD hDT (by omega),zero_mul]

/-- The total degree is T+1, with no support cutoff. -/
theorem fullSourcePolynomial_homogeneous (D T r : ℕ) (hrD : r≤D) (hDT : D≤T) :
    (fullSourcePolynomial D T r).IsHomogeneous (T+1) := by
  have hx (i : Fin 4) : (MvPolynomial.X i : FourPolynomial).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X ℤ i
  have hp : pairDifference.IsHomogeneous 1 := (hx 0).sub (hx 1)
  have hr : spectatorDifference.IsHomogeneous 1 := (hx 2).sub (hx 3)
  have hd : pairSpectatorDifference.IsHomogeneous 1 :=
    (((hx 0).add (hx 1)).sub (hx 2)).sub (hx 3)
  have hs : collectiveSum.IsHomogeneous 1 :=
    (((hx 0).add (hx 1)).add (hx 2)).add (hx 3)
  have h := ((hp.mul (hr.pow r)).mul (hd.pow (D-r))).mul (hs.pow (T-D))
  have hn : 1+1*r+1*(D-r)+1*(T-D)=T+1 := by omega
  simpa only [fullSourcePolynomial,hn] using h

theorem factorialWeightedWords_source_zero_of_total (D T r : ℕ) (w : Fin 4 → ℕ)
    (hrD : r≤D) (hDT : D≤T) (h : (∑ i : Fin 4, w i)≠T+1) :
    factorialWeightedWords (fullSourcePolynomial D T r) w=0 := by
  rw [factorialWeightedWords_apply,
    (fullSourcePolynomial_homogeneous D T r hrD hDT).coeff_eq_zero (by simpa using h),zero_mul]

/- Source indexing below repeats only the generic indexing argument of the
accepted degree-one source bridge; no degree-one coefficient result is used. -/
abbrev SourceIndex (T : ℕ) := (q : HalfInputIndex T) × Fin (q.val.1.val+2)

def sourceWord {T : ℕ} (x : SourceIndex T) : Fin 4 → ℕ :=
  ![x.2.val,x.1.val.1.val+1-x.2.val,x.1.val.2.val,T-x.1.val.1.val-x.1.val.2.val]

def sourceCoefficient (D T r : ℕ) (x : SourceIndex T) : ℤ :=
  integerPairSpectatorCoefficient D T r x.1.val.1.val x.1.val.2.val
    (T-x.1.val.1.val-x.1.val.2.val) x.2.val

theorem sourceWord_injective (T : ℕ) : Function.Injective (sourceWord (T:=T)) := by
  intro x y h
  rcases x with ⟨⟨⟨p,j⟩,hq⟩,a⟩
  rcases y with ⟨⟨⟨p',j'⟩,hq'⟩,a'⟩
  have h0 := congrFun h (0 : Fin 4)
  change a.val=a'.val at h0
  have h1 := congrFun h (1 : Fin 4)
  change p.val+1-a.val=p'.val+1-a'.val at h1
  have h2 := congrFun h (2 : Fin 4)
  change j.val=j'.val at h2
  have hp : p=p' := by
    apply Fin.ext
    have ha : a.val < p.val+2 := a.isLt
    have ha' : a'.val < p'.val+2 := a'.isLt
    omega
  subst p'
  have hj : j=j' := Fin.ext h2
  subst j'
  have ha : a=a' := Fin.ext h0
  subst a'
  rfl

theorem sourceWord_total {T : ℕ} (x : SourceIndex T) :
    (∑ i : Fin 4, sourceWord x i)=T+1 := by
  have hp : x.1.val.1.val < T+1 := x.1.val.1.isLt
  have hj : x.1.val.2.val < T-x.1.val.1.val+1 := x.1.val.2.isLt
  have ha : x.2.val < x.1.val.1.val+2 := x.2.isLt
  rw [Fin.sum_univ_four]
  change x.2.val+(x.1.val.1.val+1-x.2.val)+x.1.val.2.val+
    (T-x.1.val.1.val-x.1.val.2.val)=T+1
  omega

theorem sourceWord_exists (T : ℕ) (w : Fin 4 → ℕ)
    (htotal : (∑ i : Fin 4, w i)=T+1) (h01 : w 0<w 1) (h23 : w 2<w 3) :
    ∃ x : SourceIndex T, sourceWord x=w := by
  have hw : w 0+w 1+w 2+w 3=T+1 := by simpa only [Fin.sum_univ_four] using htotal
  let p : Fin (T+1) := ⟨w 0+w 1-1,by omega⟩
  let j : Fin (T-p.val+1) := ⟨w 2,by dsimp [p]; omega⟩
  have hk : T-p.val-j.val=w 3 := by dsimp [p,j]; omega
  let q : HalfInputIndex T := ⟨⟨p,j⟩,by change j.val<T-p.val-j.val; rw [hk]; exact h23⟩
  let a : Fin (q.val.1.val+2) := ⟨w 0,by dsimp [q,p]; omega⟩
  refine ⟨⟨q,a⟩,?_⟩
  funext i
  fin_cases i <;> simp [sourceWord,q,a,p,j] <;> omega

theorem source_as_singleSum (D T r : ℕ) :
    integerSourceWords D T r =
      ∑ x : SourceIndex T, Finsupp.single (sourceWord x) (sourceCoefficient D T r x) := by
  classical
  rw [integerSourceWords,Fintype.sum_sigma]
  rfl

theorem source_generated (D T r : ℕ) (x : SourceIndex T) :
    (integerSourceWords D T r) (sourceWord x)=sourceCoefficient D T r x := by
  classical
  rw [source_as_singleSum,Finsupp.finsetSum_apply,Finset.sum_eq_single x]
  · simp
  · intro y hy hyx
    exact Finsupp.single_eq_of_ne' ((sourceWord_injective T).ne hyx)
  · simp

theorem source_zero_of_not_generated (D T r : ℕ) (w : Fin 4 → ℕ)
    (h : ¬∃ x : SourceIndex T, sourceWord x=w) : (integerSourceWords D T r) w=0 := by
  classical
  rw [source_as_singleSum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finsupp.single_eq_of_ne'
  intro he
  exact h ⟨x,he⟩

def halfSpace (w : Fin 4 → ℕ) : Prop := w 0<w 1 ∧ w 2<w 3

local instance halfSpace_decidable : DecidablePred halfSpace := fun w => by
  unfold halfSpace
  infer_instance

theorem source_zero_of_not_halfSpace (D T r : ℕ) (w : Fin 4 → ℕ) (h : ¬halfSpace w) :
    (integerSourceWords D T r) w=0 := by
  classical
  by_cases hex : ∃ x : SourceIndex T, sourceWord x=w
  · obtain ⟨x,rfl⟩ := hex
    rw [source_generated]
    have h23 : x.1.val.2.val<T-x.1.val.1.val-x.1.val.2.val := x.1.property
    have h01 : ¬x.2.val<x.1.val.1.val+1-x.2.val := by
      intro hh
      exact h ⟨hh,h23⟩
    simp [sourceCoefficient,integerPairSpectatorCoefficient,h01]
  · exact source_zero_of_not_generated D T r w hex

theorem sourceCoefficient_eq_weighted (D T r : ℕ) (x : SourceIndex T)
    (hrD : r≤D) (hDT : D≤T) (h01 : sourceWord x 0<sourceWord x 1) :
    sourceCoefficient D T r x = factorialWeightedWords (fullSourcePolynomial D T r) (sourceWord x) := by
  have hp : x.1.val.1.val < T+1 := x.1.val.1.isLt
  have hj : x.1.val.2.val < T-x.1.val.1.val+1 := x.1.val.2.isLt
  have ha : x.2.val < x.1.val.1.val+2 := x.2.isLt
  have hT : x.1.val.1.val+x.1.val.2.val+(T-x.1.val.1.val-x.1.val.2.val)=T := by omega
  have hab : x.2.val+(x.1.val.1.val+1-x.2.val)=x.1.val.1.val+1 := by omega
  change x.2.val<x.1.val.1.val+1-x.2.val at h01
  rw [sourceWord,fullSourcePolynomial_weighted_coefficient D T r x.1.val.1.val
    x.2.val (x.1.val.1.val+1-x.2.val) x.1.val.2.val
    (T-x.1.val.1.val-x.1.val.2.val) hrD hDT hT hab]
  simp only [sourceCoefficient,integerPairSpectatorCoefficient,h01,true_and]

/-- Faithful source bridge in the FREE INTEGER ORDERED-WORD SPACE.
The filter includes both original restrictions a<b and j<k. It is not an
exterior equality and carries no target-vacuum or target-raising premise. -/
theorem integerSourceWords_eq_filter_factorialWeightedWords (D T r : ℕ)
    (hrD : r≤D) (hDT : D≤T) :
    integerSourceWords D T r =
      (factorialWeightedWords (fullSourcePolynomial D T r)).filter halfSpace := by
  classical
  ext w
  rw [Finsupp.filter_apply]
  by_cases hh : halfSpace w
  · rw [if_pos hh]
    by_cases ht : (∑ i : Fin 4, w i)=T+1
    · obtain ⟨x,rfl⟩ := sourceWord_exists T w ht hh.1 hh.2
      rw [source_generated]
      exact sourceCoefficient_eq_weighted D T r x hrD hDT hh.1
    · rw [factorialWeightedWords_source_zero_of_total D T r w hrD hDT ht]
      apply source_zero_of_not_generated
      rintro ⟨x,rfl⟩
      exact ht (sourceWord_total x)
  · rw [if_neg hh]
    exact source_zero_of_not_halfSpace D T r w hh

end GeneralSourceCoefficientBridgeCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.exponentOfWord_apply
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.twoExponent_eta
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.twoExponent_degree
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.exponentOfWord_degree
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.left_mapDomain
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.right_mapDomain
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.splitExponent_eq_iff
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.coeff_separated_blocks
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.pairBlock_homogeneous
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.spectatorBlock_homogeneous
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.pairBlock_coeff_zero
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.spectatorBlock_coeff_zero
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.pairBlock_coeff_factorial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.blockSubstitute_monomial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.blockCoefficient
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.blockCoefficient_below
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.fullSourcePolynomial_blockSubstitute
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.fullSourcePolynomial_coeff
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.fullSourcePolynomial_coeff_below
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.factorialWeightedWords_apply
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.fullSourcePolynomial_weighted_coefficient
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.fullSourcePolynomial_homogeneous
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.factorialWeightedWords_source_zero_of_total
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.sourceWord_injective
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.sourceWord_total
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.sourceWord_exists
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.source_as_singleSum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.source_generated
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.source_zero_of_not_generated
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.source_zero_of_not_halfSpace
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.sourceCoefficient_eq_weighted
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceCoefficientBridgeCandidate.integerSourceWords_eq_filter_factorialWeightedWords
