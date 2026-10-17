import torus.shared.ThermalCoherentFermionAnchoredGround
import torus.shared.ThermalCoherentFermionAnchoredJacobiInsertion

/-! Explicit truncation from the original Nat exterior source into the
existing finite OAI exterior algebra. It preserves the actual exterior product
and the negative ground-pair sign. The coefficient reconciliation for arbitrary
p is deliberately not replaced by an assumed isometry or rank identity. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open OAI.Laughlin.Fock TorusLean.Fermion
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators

/-- Canonical orbital truncation; modes beyond Q are sent to zero. -/
def canonicalTruncatedMode (Q j : ℕ) : Orbital Q :=
  if h : j≤Q then mode ⟨j,by omega⟩ else 0

def formalCanonicalOrbitalMap (Q : ℕ) : FormalOrbital →ₗ[ℂ] Orbital Q :=
  Finsupp.linearCombination ℂ (canonicalTruncatedMode Q)

def formalCanonicalExteriorMap (Q : ℕ) : FormalExterior →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (formalCanonicalOrbitalMap Q)

theorem canonicalTruncatedMode_fin (Q : ℕ) (i : Fin (Q+1)) :
    canonicalTruncatedMode Q i.val=mode i := by
  rw [canonicalTruncatedMode,dif_pos (by omega)]

theorem canonicalTruncatedMode_above (Q j : ℕ) (hj : Q<j) :
    canonicalTruncatedMode Q j=0 := by
  rw [canonicalTruncatedMode,dif_neg (by omega)]

theorem formalCanonicalExteriorMap_jet (Q j : ℕ) :
    formalCanonicalExteriorMap Q (formalJet j)=
      ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q j) := by
  simp only [formalCanonicalExteriorMap,formalJet,ExteriorAlgebra.map_apply_ι,
    formalCanonicalOrbitalMap,Finsupp.linearCombination_single,one_smul]

theorem formalCanonicalExteriorMap_jet_fin (Q : ℕ) (i : Fin (Q+1)) :
    formalCanonicalExteriorMap Q (formalJet i.val)=ExteriorAlgebra.ι ℂ (mode i) := by
  rw [formalCanonicalExteriorMap_jet,canonicalTruncatedMode_fin]

theorem formalCanonicalExteriorMap_jet_above (Q j : ℕ) (hj : Q<j) :
    formalCanonicalExteriorMap Q (formalJet j)=0 := by
  rw [formalCanonicalExteriorMap_jet,canonicalTruncatedMode_above Q j hj,map_zero]

/-- Literal finite sum retained by the truncation, with the unchanged
unordered pair coefficients and unchanged annihilation orientation. -/
theorem formalCanonicalExteriorMap_pair (Q p : ℕ) :
    formalCanonicalExteriorMap Q (formalPair p)=
      ∑ i : Fin (p+2),
        (TorusLean.Shared.FermionLocalJet.pairLeftCoefficient p i.val:ℂ) •
          (ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q i.val) *
            ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q (p+1-i.val))) := by
  simp only [formalPair,map_sum,map_smul,map_mul,formalCanonicalExteriorMap_jet]

/-- The original negative anchor maps to the existing finite Slater word.
No demand Q>=l+1 is introduced: Q>=l is already encoded by d. -/
theorem formalCanonicalExteriorMap_anchor (Q : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) :
    formalCanonicalExteriorMap Q (formalAnchoredSeed d.val)=
      -rawTripleVector Q (mode a) (mode b) (mode d) := by
  rw [formalAnchoredSeed,formalThreeSeed,formalPair_ground,map_mul,map_neg,map_mul]
  have h0 : formalCanonicalExteriorMap Q (formalJet 0)=ExteriorAlgebra.ι ℂ (mode a) := by
    simpa only [ha] using formalCanonicalExteriorMap_jet_fin Q a
  have h1 : formalCanonicalExteriorMap Q (formalJet 1)=ExteriorAlgebra.ι ℂ (mode b) := by
    simpa only [hb] using formalCanonicalExteriorMap_jet_fin Q b
  rw [h0,h1,formalCanonicalExteriorMap_jet_fin]
  simp only [rawTripleVector,rawCreate,LinearMap.coe_mk,AddHom.coe_mk,mul_one,
    neg_mul,mul_assoc]

/-- A top pair component with the repeated spectator is genuinely zero
before truncation; this is why Q=l suffices for the anchored l column. -/
theorem formal_top_pair_spectator_zero (l : ℕ) :
    formalJet 0*formalJet (l+1)*formalJet 0=0 := by
  rw [mul_assoc]
  have hs : formalJet (l+1)*formalJet 0=-(formalJet 0*formalJet (l+1)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [hs,mul_neg,← mul_assoc]
  simp only [formalJet,ExteriorAlgebra.ι_sq_zero,zero_mul,neg_zero]


private theorem sum_square_extend {V : Type*} [AddCommMonoid V]
    (a b : ℕ) (hab : a≤b) (F : ℕ → ℕ → V)
    (hz : ∀ i j, a≤ i ∨ a≤j → F i j=0) :
    (∑ i∈Finset.range a, ∑ j∈Finset.range a, F i j) =
      ∑ i∈Finset.range b, ∑ j∈Finset.range b, F i j := by
  classical
  calc
    _ = ∑ i∈Finset.range a, ∑ j∈Finset.range b, F i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_subset (Finset.range_mono hab)
      intro j hj hja
      exact hz i j (Or.inr (by simpa only [Finset.mem_range,not_lt] using hja))
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hab)
      intro i hi hia
      apply Finset.sum_eq_zero
      intro j hj
      exact hz i j (Or.inl (by simpa only [Finset.mem_range,not_lt] using hia))

private def finitePairTerm (Q p i j : ℕ) : Space Q :=
  if i<j then (planePairCoefficient p i j:ℂ) •
    (ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q i) *
      ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q j)) else 0

private theorem finitePairTerm_above_cutoff (Q p i j : ℕ)
    (h : Q+1≤ i ∨ Q+1≤j) : finitePairTerm Q p i j=0 := by
  unfold finitePairTerm
  split_ifs
  · rcases h with hi | hj
    · rw [canonicalTruncatedMode_above Q i (by omega),map_zero,zero_mul,smul_zero]
    · rw [canonicalTruncatedMode_above Q j (by omega),map_zero,mul_zero,smul_zero]
  · rfl

private theorem finitePairTerm_above_degree (Q p i j : ℕ)
    (h : p+2≤ i ∨ p+2≤j) : finitePairTerm Q p i j=0 := by
  have hd : i+j≠p+1 := by rcases h with h | h <;> omega
  simp only [finitePairTerm,planePairCoefficient,hd,if_false,Complex.ofReal_zero,zero_smul]
  simp

private theorem finitePairTerm_single_sum (Q p i : ℕ) (hi : i∈Finset.range (p+2)) :
    (∑ j∈Finset.range (p+2), finitePairTerm Q p i j) =
      (pairLeftCoefficient p i:ℂ) •
        (ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q i) *
          ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q (p+1-i))) := by
  have hi' : i≤p+1 := by have := Finset.mem_range.mp hi; omega
  rw [Finset.sum_eq_single (p+1-i)]
  · simp only [finitePairTerm,planePairCoefficient,Nat.add_sub_of_le hi',if_true]
    by_cases hij : i<p+1-i
    · simp only [hij,if_true,pairLeftCoefficient]
    · simp only [hij,if_false,pairLeftCoefficient,Complex.ofReal_zero,zero_smul]
  · intro j hj hne
    have hd : i+j≠p+1 := by omega
    simp [finitePairTerm,planePairCoefficient,hd]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- Exact arbitrary-Q bridge between the original Nat pair and the original
finite coefficient creator. Truncated modes vanish, so no stronger Q>=p+1
hypothesis is silently imposed on the anchored Q>=l application. -/
theorem formalCanonicalExteriorMap_pair_eq_plane (Q p : ℕ) :
    formalCanonicalExteriorMap Q (formalPair p)=planePairCreate Q p 1 := by
  classical
  have hQ := sum_square_extend (Q+1) (max (Q+1) (p+2)) (le_max_left _ _)
    (finitePairTerm Q p) (finitePairTerm_above_cutoff Q p)
  have hp := sum_square_extend (p+2) (max (Q+1) (p+2)) (le_max_right _ _)
    (finitePairTerm Q p) (finitePairTerm_above_degree Q p)
  have hrect := hQ.trans hp.symm
  rw [planePairCreate_unordered]
  simp only [LinearMap.sum_apply]
  have he : (∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
      (if i<j then (planePairCoefficient p i.val j.val:ℂ) •
        rawPairCreate Q (mode i) (mode j) else 0) 1) =
      ∑ i∈Finset.range (Q+1), ∑ j∈Finset.range (Q+1), finitePairTerm Q p i j := by
    calc
      _ = ∑ i : Fin (Q+1), ∑ j : Fin (Q+1), finitePairTerm Q p i.val j.val := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i<j
        · have hv : i.val<j.val := hij
          simp only [hij,ite_true,LinearMap.smul_apply,finitePairTerm,hv,
            canonicalTruncatedMode_fin,rawPairCreate,Module.End.mul_apply,
            rawCreate,LinearMap.coe_mk,AddHom.coe_mk,mul_one]
        · have hv : ¬i.val<j.val := hij
          simp only [hij,ite_false,LinearMap.zero_apply,finitePairTerm,hv]
      _ = _ := (Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (Q+1),
        finitePairTerm Q p i j.val) (Q+1)).trans (by
          apply Finset.sum_congr rfl
          intro i hi
          exact Fin.sum_univ_eq_sum_range (finitePairTerm Q p i) (Q+1))
  rw [he,hrect,formalCanonicalExteriorMap_pair,
    Fin.sum_univ_eq_sum_range (fun i => (pairLeftCoefficient p i:ℂ) •
      (ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q i) *
        ExteriorAlgebra.ι ℂ (canonicalTruncatedMode Q (p+1-i)))) (p+2)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (finitePairTerm_single_sum Q p i hi).symm

private theorem planePairCreate_eq_vacuum_mul (Q p : ℕ) (x : Space Q) :
    planePairCreate Q p x=planePairCreate Q p 1*x := by
  simp only [planePairCreate,coefficientPairCreate,LinearMap.smul_apply,
    LinearMap.sum_apply,rawPairCreate,Module.End.mul_apply,rawCreate,
    LinearMap.coe_mk,AddHom.coe_mk,mul_one,Finset.sum_mul,smul_mul_assoc,mul_assoc]

/-- Exact original pair/spectator column bridge, for every Q and p. -/
theorem formalCanonicalExteriorMap_threeSeed (Q p : ℕ) (j : Fin (Q+1)) :
    formalCanonicalExteriorMap Q (formalThreeSeed p j.val)=
      planePairCreate Q p (rawCreate Q (mode j) 1) := by
  rw [formalThreeSeed,map_mul,formalCanonicalExteriorMap_pair_eq_plane,
    formalCanonicalExteriorMap_jet_fin,
    planePairCreate_eq_vacuum_mul Q p (rawCreate Q (mode j) 1)]
  simp only [rawCreate,LinearMap.coe_mk,AddHom.coe_mk,mul_one]


private theorem pairRoot_factorized (p : ℕ) :
    Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ))=
      (Real.sqrt (2:ℝ))^p*Real.sqrt (p.factorial:ℝ) := by
  have hs : Real.sqrt ((2:ℝ)^p)=(Real.sqrt (2:ℝ))^p := by
    induction p with
    | zero => simp
    | succ p ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [Real.sqrt_mul (by positivity),hs]

private theorem factorialRoot_succ (p : ℕ) :
    Real.sqrt ((p+1).factorial:ℝ)=
      Real.sqrt (p+1:ℝ)*Real.sqrt (p.factorial:ℝ) := by
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity)]
  norm_cast

private theorem two_power_root_product (p : ℕ) :
    (2:ℝ)^p=(Real.sqrt (2:ℝ))^p*(Real.sqrt (2:ℝ))^p := by
  rw [←mul_pow,Real.mul_self_sqrt (by norm_num)]

private theorem connected_pair_coefficient (p : ℕ) :
    ((2:ℝ)^(p+1)*Real.sqrt ((p+1).factorial:ℝ))⁻¹ *
      ((p:ℝ)*Real.sqrt ((2:ℝ)^(p+1)*((p+1).factorial:ℝ))) =
        (p:ℝ)/(Real.sqrt (2:ℝ))^(p+1) := by
  have hf : Real.sqrt ((p+1).factorial:ℝ)≠0 := by positivity
  have h2 : (Real.sqrt (2:ℝ))^(p+1)≠0 := by positivity
  rw [pairRoot_factorized,two_power_root_product]
  field_simp [hf,h2]
  <;> ring

private theorem connected_spectator_coefficient (p : ℕ) :
    ((2:ℝ)^(p+1)*Real.sqrt ((p+1).factorial:ℝ))⁻¹ *
      ((2*(p+1:ℝ))*Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ))) =
        Real.sqrt (p+1:ℝ)/(Real.sqrt (2:ℝ))^p := by
  have hf : Real.sqrt (p.factorial:ℝ)≠0 := by positivity
  have ht : Real.sqrt (p+1:ℝ)≠0 := by positivity
  have h2 : (Real.sqrt (2:ℝ))^p≠0 := by positivity
  calc
    _ = ((p+1:ℝ)/Real.sqrt (p+1:ℝ))/(Real.sqrt (2:ℝ))^p := by
      rw [pairRoot_factorized,factorialRoot_succ,pow_succ,two_power_root_product p]
      field_simp [hf,ht,h2]
      <;> ring
    _ = _ := by rw [Real.div_sqrt]

/-- The true Nat exterior source itself has the normalized two columns.
This precedes every finite cutoff map and every physical periodization. -/
theorem formalConnectedAnchoredSeed_explicit (p : ℕ) :
    formalConnectedAnchoredSeed (p+1) =
      ((p:ℝ)/(Real.sqrt (2:ℝ))^(p+1):ℂ) • formalThreeSeed (p+1) 0 -
      (Real.sqrt (p+1:ℝ)/(Real.sqrt (2:ℝ))^p:ℂ) • formalThreeSeed p 1 := by
  have hα := congrArg (fun r : ℝ => (r:ℂ)) (connected_pair_coefficient p)
  have hβ := congrArg (fun r : ℝ => (r:ℂ)) (connected_spectator_coefficient p)
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv,
    Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_natCast,
    Complex.ofReal_add,Complex.ofReal_one] at hα hβ
  rw [formalConnectedAnchoredSeed_two_columns]
  simp only [smul_sub,smul_smul]
  rw [hα,hβ]
  simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]

/-- Exact normalized second-column bridge, with the true minus sign on
v_(l-1) wedge e_1 and plus sign on v_l wedge e_0. -/
theorem formalCanonicalExteriorMap_connected_two_columns (Q p : ℕ)
    (a b : Fin (Q+1)) (ha : a.val=0) (hb : b.val=1) :
    formalCanonicalExteriorMap Q (formalConnectedAnchoredSeed (p+1)) =
      ((p:ℝ)/(Real.sqrt (2:ℝ))^(p+1):ℂ) •
        planePairCreate Q (p+1) (rawCreate Q (mode a) 1) -
      (Real.sqrt (p+1:ℝ)/(Real.sqrt (2:ℝ))^p:ℂ) •
        planePairCreate Q p (rawCreate Q (mode b) 1) := by
  have hA : formalCanonicalExteriorMap Q (formalThreeSeed (p+1) 0)=
      planePairCreate Q (p+1) (rawCreate Q (mode a) 1) := by
    simpa only [ha] using formalCanonicalExteriorMap_threeSeed Q (p+1) a
  have hB : formalCanonicalExteriorMap Q (formalThreeSeed p 1)=
      planePairCreate Q p (rawCreate Q (mode b) 1) := by
    simpa only [hb] using formalCanonicalExteriorMap_threeSeed Q p b
  have hα := congrArg (fun r : ℝ => (r:ℂ)) (connected_pair_coefficient p)
  have hβ := congrArg (fun r : ℝ => (r:ℂ)) (connected_spectator_coefficient p)
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv,
    Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_natCast,
    Complex.ofReal_add,Complex.ofReal_one] at hα hβ
  rw [formalConnectedAnchoredSeed_two_columns,map_smul,map_sub,map_smul,map_smul,hA,hB]
  simp only [smul_sub,smul_smul]
  rw [hα,hβ]
  simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]

/-- The actual finite H-I column of the original negative anchor is precisely
the exterior image of the two marked polynomial columns. No stronger cutoff
or assumed source equality is used. -/
theorem formalCanonicalExteriorMap_connected (Q D : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (hl : 1<d.val) (hD : d.val≤D) :
    formalCanonicalExteriorMap Q (formalConnectedAnchoredSeed d.val) =
      (planePairHamiltonian Q D-1)
        (formalCanonicalExteriorMap Q (formalAnchoredSeed d.val)) := by
  have hd : d.val-1+1=d.val := by omega
  have h := formalCanonicalExteriorMap_connected_two_columns Q (d.val-1) a b ha hb
  rw [hd] at h
  rw [h,formalCanonicalExteriorMap_anchor Q a b d ha hb,map_neg,
    planePairHamiltonian_connected_anchor Q D a b d ha hb hl hD]
  have hcplus : ((d.val-1:ℕ):ℝ)+1=(d.val:ℝ) := by exact_mod_cast hd
  have hc : ((d.val-1:ℕ):ℝ)=(d.val:ℝ)-1 := by linarith only [hcplus]
  rw [hc,sub_add_cancel]
  module

/-- End-to-end genuine finite anchored row, in terms of the original
negative Nat exterior anchor and the derived marked two-column bra. -/
theorem planeAnchoredKernel_formal_source_row (Q D : ℕ) (a b d : Fin (Q+1))
    (ha : a.val=0) (hb : b.val=1) (hl : 1<d.val) (hD : d.val≤D)
    (f : Space Q) (hf : f∈threeDegreeSpan Q (d.val+1)) :
    planeAnchoredKernel Q D a b f =
      occupationInner Q
        (formalCanonicalExteriorMap Q (formalConnectedAnchoredSeed d.val)) f •
          formalCanonicalExteriorMap Q (formalAnchoredSeed d.val) := by
  rw [formalCanonicalExteriorMap_connected Q D a b d ha hb hl hD,
    formalCanonicalExteriorMap_anchor Q a b d ha hb,map_neg]
  rw [planeAnchoredKernel_rank_one Q D a b d ha hb f hf]
  have hn (x y : Space Q) : occupationInner Q (-x) y= -occupationInner Q x y := by
    simp only [occupationInner,map_neg,Finsupp.neg_apply,star_neg,neg_mul,
      Finset.sum_neg_distrib]
  rw [hn,neg_smul,smul_neg,neg_neg]

end TorusLean.Shared.ThermalCoherentFermionAnchored
