import torus.shared.CellHilbert
import Mathlib.Analysis.InnerProductSpace.PiL2
import torus.boson.PolynomialInnerAdjoint
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Sym2Evaluation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Finsupp.Multiset
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.List.OfFn

/-!
# Actual finite-particle functions in the physical cell product measure

Every orbital below is the actual Gaussian-holomorphic magnetic section in
`orbitalBasis`; every integral uses the original `mu_1^N`, with no
division by the cell mass. Empty products retain the scalar vacuum.

This file develops the physical function Gram matrix before identifying the
normal-ordered contact lift with the sum of particle-pair contacts. No
isometry, dimension equality, or nonempty physical mode index is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace TorusLean.Shared.PhysicalBosonSector

open MeasureTheory TorusLean.Boson
open scoped BigOperators ComplexConjugate TensorProduct

/-- The actual physical dimension can be zero; no dim=M premise is used. -/
abbrev OrbitalIndex (G : Geometry) (theta : Twist) :=
  Fin (Module.finrank ℂ (LLL G theta 1))

/-- The same standard actual cell orthonormal basis used by C coordinates. -/
def orbitalBasis (G : Geometry) (theta : Twist) :
    OrthonormalBasis (OrbitalIndex G theta) ℂ (LLL G theta 1) :=
  stdOrthonormalBasis ℂ (LLL G theta 1)

abbrev Configuration (N : ℕ) := Fin N → ℂ
abbrev Word (G : Geometry) (theta : Twist) (N : ℕ) :=
  Fin N → OrbitalIndex G theta

/-- The original cell measure in every labeled particle coordinate. -/
def sectorMeasure (G : Geometry) (N : ℕ) : Measure (Configuration N) :=
  Measure.pi (fun _ : Fin N => cellMeasure G 1)

/-- Integral inner product on actual universal-cover particle functions. -/
def sectorInner (G : Geometry) (N : ℕ)
    (f g : Configuration N → ℂ) : ℂ :=
  ∫ z, conj (f z) * g z ∂sectorMeasure G N

/-- A labeled tensor product of the actual physical cell-normalized orbitals. -/
def wordFunction (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (z : Configuration N) : ℂ :=
  ∏ a, (orbitalBasis G theta (w a)).val (z a)

theorem wordFunction_zero (G : Geometry) (theta : Twist)
    (w : Word G theta 0) (z : Configuration 0) :
    wordFunction G theta 0 w z = 1 := by
  simp [wordFunction]

theorem wordFunction_continuous (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) : Continuous (wordFunction G theta N w) := by
  unfold wordFunction
  apply continuous_finsetProd
  intro a ha
  exact (rawLLL_continuous G theta 1
    (orbitalBasis G theta (w a))).comp (continuous_apply a)

theorem wordFunction_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) :
    Integrable (wordFunction G theta N w) (sectorMeasure G N) := by
  apply Integrable.fintype_prod
  intro a
  exact continuous_integrable_cellMeasure G 1
    (rawLLL_continuous G theta 1 (orbitalBasis G theta (w a)))

theorem wordFunction_inner_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N) :
    Integrable (fun z => conj (wordFunction G theta N w z) *
      wordFunction G theta N v z) (sectorMeasure G N) := by
  have hi := Integrable.fintype_prod (μ := fun _ : Fin N => cellMeasure G 1)
    (fun a => cellInner_integrable G 1
      (orbitalBasis G theta (w a)).val
      (orbitalBasis G theta (v a)).val
      (rawLLL_continuous G theta 1 (orbitalBasis G theta (w a)))
      (rawLLL_continuous G theta 1 (orbitalBasis G theta (v a))))
  simpa only [wordFunction, sectorMeasure, map_prod, Finset.prod_mul_distrib] using hi

/-- Fubini in the original physical measure, including the empty product. -/
theorem wordFunction_inner_product (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N) :
    sectorInner G N (wordFunction G theta N w) (wordFunction G theta N v) =
      ∏ a, inner ℂ (orbitalBasis G theta (w a))
        (orbitalBasis G theta (v a)) := by
  have hF := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin N => cellMeasure G 1)
    (fun a (x : ℂ) => conj ((orbitalBasis G theta (w a)).val x) *
      (orbitalBasis G theta (v a)).val x)
  calc
    _ = ∏ a, cellInner G 1 (orbitalBasis G theta (w a)).val
        (orbitalBasis G theta (v a)).val := by
      simpa only [sectorInner, wordFunction, sectorMeasure, map_prod,
        ← Finset.prod_mul_distrib, cellInner] using hF
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a ha
      exact (lll_inner_eq_cellInner G theta 1 _ _).symm

/-- Actual labeled physical products form an orthonormal family for every N. -/
theorem wordFunction_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N) :
    sectorInner G N (wordFunction G theta N w) (wordFunction G theta N v) =
      if w = v then 1 else 0 := by
  classical
  rw [wordFunction_inner_product]
  simp only [orthonormal_iff_ite.mp (orbitalBasis G theta).orthonormal]
  by_cases h : w = v
  · subst v
    simp
  · obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)

/-- Actual occupation counts, without a cutoff or a chosen nonempty mode. -/
def wordOccupation (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) : OrbitalIndex G theta →₀ ℕ :=
  ∑ a, Finsupp.single (w a) 1

theorem wordOccupation_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (i : OrbitalIndex G theta) :
    wordOccupation G theta N w i = Fintype.card {a : Fin N // w a = i} := by
  classical
  simp [wordOccupation, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Fintype.card_subtype, Finset.sum_boole]

theorem wordOccupation_degree (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) : (wordOccupation G theta N w).degree = N := by
  simp [wordOccupation, map_sum]

theorem wordOccupation_comp_perm (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (σ : Equiv.Perm (Fin N)) :
    wordOccupation G theta N (w ∘ σ) = wordOccupation G theta N w := by
  unfold wordOccupation
  exact Equiv.sum_comp σ (fun a => Finsupp.single (w a) 1)

/-- The factorial multiplicity comes from actual stabilizers of labeled
particle words; it is the existing occupation weight, rather than a new norm. -/
theorem word_stabilizer_card (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) :
    Fintype.card {σ : Equiv.Perm (Fin N) // w ∘ σ = w} =
      occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) := by
  classical
  rw [DomMulAct.stabilizer_card]
  simp only [occupationMetricWeight, one_pow, mul_one, wordOccupation_apply]

/-- Equal occupation counts are exactly permutation-related labeled words. -/
theorem wordOccupation_eq_iff (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N) :
    wordOccupation G theta N w = wordOccupation G theta N v ↔
      ∃ σ : Equiv.Perm (Fin N), v ∘ σ = w := by
  classical
  constructor
  · intro h
    let e : ∀ i : OrbitalIndex G theta,
        {a : Fin N // w a = i} ≃ {a : Fin N // v a = i} := fun i =>
      Fintype.equivOfCardEq (by
        rw [← wordOccupation_apply G theta N w i,
          ← wordOccupation_apply G theta N v i, h])
    exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩
  · rintro ⟨σ, hσ⟩
    rw [← hσ, wordOccupation_comp_perm]

/-- Standard bosonic monomial function: every permutation is counted,
including the multiplicities from repeated labels; the factor is 1/sqrt(N!). -/
def symWordFunction (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (z : Configuration N) : ℂ :=
  (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
    ∑ σ : Equiv.Perm (Fin N), wordFunction G theta N (w ∘ σ) z

theorem symWordFunction_comp_perm (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (σ : Equiv.Perm (Fin N)) :
    symWordFunction G theta N (w ∘ σ) = symWordFunction G theta N w := by
  classical
  funext z
  unfold symWordFunction
  congr 1
  simpa only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_def] using
    Equiv.sum_comp (Equiv.mulLeft σ)
      (fun τ => wordFunction G theta N (w ∘ τ) z)

theorem symWordFunction_eq_of_occupation_eq (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N)
    (h : wordOccupation G theta N w = wordOccupation G theta N v) :
    symWordFunction G theta N w = symWordFunction G theta N v := by
  obtain ⟨σ, hσ⟩ := (wordOccupation_eq_iff G theta N w v).mp h
  rw [← hσ, symWordFunction_comp_perm]

/-- The physical Gram integral of finite sums, derived from their actual
integrability rather than from a supplied tensor isometry. -/
theorem sectorInner_wordSums {A B : Type*} (G : Geometry) (theta : Twist) (N : ℕ)
    (s : Finset A) (t : Finset B)
    (w : A → Word G theta N) (v : B → Word G theta N) :
    sectorInner G N
      (fun z => ∑ a ∈ s, wordFunction G theta N (w a) z)
      (fun z => ∑ b ∈ t, wordFunction G theta N (v b) z) =
      ∑ a ∈ s, ∑ b ∈ t, if w a = v b then (1 : ℂ) else 0 := by
  classical
  simp only [sectorInner, map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum s (fun a ha =>
    integrable_finsetSum t (fun b hb => wordFunction_inner_integrable G theta N _ _))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum t (fun b hb => wordFunction_inner_integrable G theta N _ _)]
  apply Finset.sum_congr rfl
  intro b hb
  exact wordFunction_inner G theta N (w a) (v b)

theorem sectorInner_const_mul (G : Geometry) (N : ℕ)
    (c d : ℂ) (f g : Configuration N → ℂ) :
    sectorInner G N (fun z => c * f z) (fun z => d * g z) =
      conj c * d * sectorInner G N f g := by
  unfold sectorInner
  simp only [map_mul]
  simp_rw [show ∀ z, conj c * conj (f z) * (d * g z) =
    (conj c * d) * (conj (f z) * g z) by intro z; ring]
  exact integral_const_mul _ _

theorem permutation_match_card (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (σ : Equiv.Perm (Fin N)) :
    Fintype.card {τ : Equiv.Perm (Fin N) // w ∘ σ = w ∘ τ} =
      occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) := by
  classical
  let e : {ρ : Equiv.Perm (Fin N) // w ∘ ρ = w} ≃
      {τ : Equiv.Perm (Fin N) // w ∘ σ = w ∘ τ} :=
    Equiv.subtypeEquiv (Equiv.mulRight σ) (fun ρ => by
      constructor
      · intro h
        funext a
        exact (congrFun h (σ a)).symm
      · intro h
        funext a
        simpa only [Equiv.coe_mulRight, Equiv.Perm.mul_apply,
          Function.comp_apply, Equiv.apply_symm_apply] using
          (congrFun h (σ.symm a)).symm)
  rw [← Fintype.card_congr e, word_stabilizer_card]

/-- The unnormalized permutation Gram sum has the exact factor N! times
the old occupation weight, derived by counting actual word stabilizers. -/
theorem permutation_gram_self (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) :
    (∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      if w ∘ σ = w ∘ τ then (1 : ℂ) else 0) =
        (N.factorial : ℂ) *
          occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) := by
  classical
  have hc (σ : Equiv.Perm (Fin N)) :
      (∑ τ : Equiv.Perm (Fin N), if w ∘ σ = w ∘ τ then (1 : ℂ) else 0) =
        (occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) : ℂ) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype,
      permutation_match_card G theta N w σ]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

/-- Exact factorial norm in the original mu_1^N measure for every particle
number; the standard 1/sqrt(N!) normalization is part of the definition. -/
theorem symWordFunction_inner_self (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) :
    sectorInner G N (symWordFunction G theta N w) (symWordFunction G theta N w) =
      (occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) : ℂ) := by
  classical
  unfold symWordFunction
  rw [sectorInner_const_mul, sectorInner_wordSums, permutation_gram_self]
  have hs : conj (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) =
        ((N.factorial : ℂ))⁻¹ := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [hs]
  have hn : (N.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem symWordFunction_inner_of_occupation_ne (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N)
    (h : wordOccupation G theta N w ≠ wordOccupation G theta N v) :
    sectorInner G N (symWordFunction G theta N w) (symWordFunction G theta N v) = 0 := by
  classical
  have hne (σ τ : Equiv.Perm (Fin N)) : w ∘ σ ≠ v ∘ τ := by
    intro he
    apply h
    rw [← wordOccupation_comp_perm G theta N w σ, he, wordOccupation_comp_perm]
  unfold symWordFunction
  rw [sectorInner_const_mul, sectorInner_wordSums]
  simp [hne]

/-- Actual occupation Gram matrix, for the canonical factorial monomials. -/
theorem symWordFunction_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (w v : Word G theta N) :
    sectorInner G N (symWordFunction G theta N w) (symWordFunction G theta N v) =
      if wordOccupation G theta N w = wordOccupation G theta N v then
        (occupationMetricWeight (fun _ => 1) (wordOccupation G theta N w) : ℂ)
      else 0 := by
  classical
  by_cases h : wordOccupation G theta N w = wordOccupation G theta N v
  · rw [if_pos h, ← symWordFunction_eq_of_occupation_eq G theta N w v h,
      symWordFunction_inner_self]
  · rw [if_neg h]
    exact symWordFunction_inner_of_occupation_ne G theta N w v h

theorem symWordFunction_zero (G : Geometry) (theta : Twist)
    (w : Word G theta 0) : symWordFunction G theta 0 w = fun _ => 1 := by
  funext z
  simp [symWordFunction, wordFunction]

/-- Vacuum norm is one even when the actual physical orbital index is empty. -/
theorem vacuum_inner (G : Geometry) (theta : Twist) :
    sectorInner G 0 (fun _ => 1) (fun _ => 1) = 1 := by
  let w : Word G theta 0 := Fin.elim0
  have h := symWordFunction_inner_self G theta 0 w
  simpa [symWordFunction_zero, wordOccupation, occupationMetricWeight] using h

theorem wordOccupation_ofFn (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) :
    wordOccupation G theta N w = (List.ofFn w : Multiset (OrbitalIndex G theta)).toFinsupp := by
  classical
  induction N with
  | zero => simp [wordOccupation]
  | succ N ih =>
    simp only [wordOccupation, Fin.sum_univ_succ, List.ofFn_succ,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add,
      Multiset.toFinsupp_singleton]
    exact congrArg (Finsupp.single (w 0) 1 + ·) (ih (fun a => w a.succ))

/-- Every occupation of total particle degree N has an actual labeled word.
This includes the unique empty word at N=0 and requires no nonempty mode. -/
theorem exists_word_of_degree (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) (hn : n.degree = N) :
    ∃ w : Word G theta N, wordOccupation G theta N w = n := by
  classical
  let l := n.toMultiset.toList
  have hl : l.length = N := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hn
  let w : Word G theta N := fun a => l.get (Fin.cast hl.symm a)
  have hw : List.ofFn w = l := by
    unfold w
    rw [← List.ofFn_congr hl, List.ofFn_get]
  refine ⟨w, ?_⟩
  rw [wordOccupation_ofFn, hw, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]

def occupationWord (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) (hn : n.degree = N) : Word G theta N :=
  Classical.choose (exists_word_of_degree G theta N n hn)

theorem occupationWord_spec (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) (hn : n.degree = N) :
    wordOccupation G theta N (occupationWord G theta N n hn) = n :=
  Classical.choose_spec (exists_word_of_degree G theta N n hn)

/-- The concrete physical image of an occupation monomial. The zero branch
only concerns degrees outside the fixed N-sector. -/
def occupationFunction (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) : Configuration N → ℂ :=
  if hn : n.degree = N then
    symWordFunction G theta N (occupationWord G theta N n hn)
  else 0

theorem occupationFunction_word (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) :
    occupationFunction G theta N (wordOccupation G theta N w) =
      symWordFunction G theta N w := by
  classical
  rw [occupationFunction, dif_pos (wordOccupation_degree G theta N w)]
  exact symWordFunction_eq_of_occupation_eq G theta N _ w
    (occupationWord_spec G theta N _ _)

/-- Gram orthogonality of all actual occupation monomial functions, with
the unchanged factorial weight and the original cell product measure. -/
theorem occupationFunction_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (n m : OrbitalIndex G theta →₀ ℕ) (hn : n.degree = N) (hm : m.degree = N) :
    sectorInner G N (occupationFunction G theta N n) (occupationFunction G theta N m) =
      if n = m then (occupationMetricWeight (fun _ => 1) n : ℂ) else 0 := by
  classical
  rw [occupationFunction, dif_pos hn, occupationFunction, dif_pos hm,
    symWordFunction_inner, occupationWord_spec, occupationWord_spec]

theorem occupationFunction_inner_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (n m : OrbitalIndex G theta →₀ ℕ) :
    Integrable (fun z => conj (occupationFunction G theta N n z) *
      occupationFunction G theta N m z) (sectorMeasure G N) := by
  classical
  unfold occupationFunction
  split_ifs with hn hm
  · simp only [symWordFunction, map_mul, map_sum, Finset.sum_mul, Finset.mul_sum]
    have hsum : Integrable
        (fun z => ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
          conj (wordFunction G theta N (occupationWord G theta N n hn ∘ σ) z) *
            wordFunction G theta N (occupationWord G theta N m hm ∘ τ) z)
        (sectorMeasure G N) :=
      integrable_finsetSum _ (fun σ hσ =>
        integrable_finsetSum _ (fun τ hτ => wordFunction_inner_integrable G theta N _ _))
    convert hsum.const_mul
      (conj (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ)) using 1
    funext z
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro τ hτ
    ring
  · simp
  · simp
  · simp

theorem sectorInner_self_re (G : Geometry) (N : ℕ) (f : Configuration N → ℂ) :
    (sectorInner G N f f).re = ∫ z, ‖f z‖ ^ 2 ∂sectorMeasure G N := by
  have h : sectorInner G N f f =
      ((∫ z, ‖f z‖ ^ 2 ∂sectorMeasure G N : ℝ) : ℂ) := by
    simp only [sectorInner, Complex.conj_mul', ← Complex.ofReal_pow]
    exact integral_complex_ofReal
  rw [h, Complex.ofReal_re]

theorem occupationFunction_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) (hn : n.degree = N) :
    (∫ z, ‖occupationFunction G theta N n z‖ ^ 2 ∂sectorMeasure G N) =
      (occupationMetricWeight (fun _ => 1) n : ℝ) := by
  rw [← sectorInner_self_re, occupationFunction_inner G theta N n n hn hn]
  simp


/-- The standard all-N construction reduces to the actual one-particle
orbital, with no extra cell-mass factor. -/
theorem symWordFunction_one (G : Geometry) (theta : Twist)
    (w : Word G theta 1) (z : Configuration 1) :
    symWordFunction G theta 1 w z = (orbitalBasis G theta (w 0)).val (z 0) := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by decide
  simp [symWordFunction, wordFunction, hu, Fin.prod_univ_one, Function.comp_def]

/-- Explicit accepted two-particle normalization: the occupation monomial
is sqrt(2) times the symmetrized physical tensor function. -/
theorem symWordFunction_two (G : Geometry) (theta : Twist)
    (w : Word G theta 2) (z : Configuration 2) :
    symWordFunction G theta 2 w z =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        ((orbitalBasis G theta (w 0)).val (z 0) *
            (orbitalBasis G theta (w 1)).val (z 1) +
          (orbitalBasis G theta (w 1)).val (z 0) *
            (orbitalBasis G theta (w 0)).val (z 1)) := by
  classical
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  simp [symWordFunction, wordFunction, hu, Fin.prod_univ_two,
    Function.comp_def, Equiv.swap_apply_def, Finset.sum_insert, hne]


def coreCoefficients (G : Geometry) (theta : Twist) :
    Core (OrbitalIndex G theta) ℂ →ₗ[ℂ] ((OrbitalIndex G theta →₀ ℕ) →₀ ℂ)  :=
  (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem coreCoefficients_apply (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : coreCoefficients G theta f = f.coeff := rfl

/-- Concrete standard symmetrized function map on the finite polynomial core. -/
def coreFunction (G : Geometry) (theta : Twist) (N : ℕ) :
    Core (OrbitalIndex G theta) ℂ →ₗ[ℂ] (Configuration N → ℂ) :=
  (Finsupp.linearCombination ℂ (occupationFunction G theta N)).comp
    (coreCoefficients G theta)

theorem coreFunction_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (z : Configuration N) :
    coreFunction G theta N f z =
      ∑ n ∈ f.support, f.coeff n * occupationFunction G theta N n z := by
  simp only [coreFunction, LinearMap.comp_apply, coreCoefficients_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, MvPolynomial.finsupp_support_eq_support]

theorem coreFunction_monomial (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) (c : ℂ) :
    coreFunction G theta N (MvPolynomial.monomial n c) =
      c • occupationFunction G theta N n := by
  classical
  have hc : (MvPolynomial.monomial n c).coeff = Finsupp.single n c := by
    ext m
    simp [MvPolynomial.coeff_monomial, Finsupp.single_apply, eq_comm]
  rw [coreFunction, LinearMap.comp_apply, coreCoefficients_apply, hc,
    Finsupp.linearCombination_single]

theorem sectorInner_finiteSums {A B : Type*} (G : Geometry) (N : ℕ)
    (s : Finset A) (t : Finset B)
    (f : A → Configuration N → ℂ) (g : B → Configuration N → ℂ)
    (hi : ∀ a ∈ s, ∀ b ∈ t,
      Integrable (fun z => conj (f a z) * g b z) (sectorMeasure G N)) :
    sectorInner G N (fun z => ∑ a ∈ s, f a z) (fun z => ∑ b ∈ t, g b z) =
      ∑ a ∈ s, ∑ b ∈ t, sectorInner G N (f a) (g b) := by
  classical
  simp only [sectorInner, map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum s (fun a ha =>
    integrable_finsetSum t (fun b hb => hi a ha b hb))]
  apply Finset.sum_congr rfl
  intro a ha
  exact integral_finsetSum t (fun b hb => hi a ha b hb)

theorem scaled_occupation_inner_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (n m : OrbitalIndex G theta →₀ ℕ) (c d : ℂ) :
    Integrable (fun z => conj (c * occupationFunction G theta N n z) *
      (d * occupationFunction G theta N m z)) (sectorMeasure G N) := by
  have h := (occupationFunction_inner_integrable G theta N n m).const_mul (conj c * d)
  convert h using 1
  funext z
  simp only [map_mul]
  ring

/-- The function map preserves the full old factorial inner product on
every finite homogeneous sector, including N=0 and N=1. -/
theorem coreFunction_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : Core (OrbitalIndex G theta) ℂ)
    (hf : f.IsHomogeneous N) (hg : g.IsHomogeneous N) :
    sectorInner G N (coreFunction G theta N f) (coreFunction G theta N g) =
      occupationInner (fun _ => 1) f g := by
  classical
  have hd {p : Core (OrbitalIndex G theta) ℂ} (hp : p.IsHomogeneous N)
      {n : OrbitalIndex G theta →₀ ℕ} (hn : n ∈ p.support) : n.degree = N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hn)
  have hfun (p : Core (OrbitalIndex G theta) ℂ) :
      coreFunction G theta N p =
        fun z => ∑ n ∈ p.support, p.coeff n * occupationFunction G theta N n z :=
    funext (coreFunction_apply G theta N p)
  rw [hfun f, hfun g]
  rw [sectorInner_finiteSums G N f.support g.support
    (fun n z => f.coeff n * occupationFunction G theta N n z)
    (fun m z => g.coeff m * occupationFunction G theta N m z)
    (fun n hn m hm => scaled_occupation_inner_integrable G theta N n m _ _)]
  unfold occupationInner
  simp only [Finsupp.sum, MvPolynomial.finsupp_support_eq_support]
  apply Finset.sum_congr rfl
  intro n hn
  have hrow : (∑ m ∈ g.support,
      sectorInner G N
        (fun z => f.coeff n * occupationFunction G theta N n z)
        (fun z => g.coeff m * occupationFunction G theta N m z)) =
      ∑ m ∈ g.support, conj (f.coeff n) * g.coeff m *
        (if n = m then (occupationMetricWeight (fun _ => 1) n : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [sectorInner_const_mul, occupationFunction_inner G theta N n m
      (hd hf hn) (hd hg hm)]
  rw [hrow]
  by_cases hng : n ∈ g.support
  · simp only [mul_ite, mul_zero, Finset.sum_ite_eq, if_pos hng]
    simp only [Complex.star_def]
    ring
  · have hg0 := MvPolynomial.notMem_support_iff.mp hng
    simp [mul_ite, Finset.sum_ite_eq, hng, hg0]

/-- The original occupation norm equals the actual mu_1^N function norm. -/
theorem coreFunction_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous N) :
    (∫ z, ‖coreFunction G theta N f z‖ ^ 2 ∂sectorMeasure G N) =
      occupationMetricNormSq (fun _ => 1) f := by
  rw [← sectorInner_self_re, coreFunction_inner G theta N f f hf hf,
    occupationInner_self_re]

/-- Actual finite-sector map, with the physical function norm proved above. -/
def sectorFunction (G : Geometry) (theta : Twist) (N : ℕ) :
    MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N →ₗ[ℂ]
      (Configuration N → ℂ) :=
  (coreFunction G theta N).comp
    (MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N).subtype

theorem sectorFunction_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N) :
    sectorInner G N (sectorFunction G theta N f) (sectorFunction G theta N g) =
      occupationInner (fun _ => 1) f.val g.val :=
  coreFunction_inner G theta N f.val g.val f.property g.property

theorem sectorFunction_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (f : MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N) :
    (∫ z, ‖sectorFunction G theta N f z‖ ^ 2 ∂sectorMeasure G N) =
      occupationMetricNormSq (fun _ => 1) f.val :=
  coreFunction_normSq G theta N f.val f.property


theorem wordFunction_permute_configuration (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (σ : Equiv.Perm (Fin N)) (z : Configuration N) :
    wordFunction G theta N w (z ∘ σ) =
      wordFunction G theta N (w ∘ σ.symm) z := by
  unfold wordFunction
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using
    (Equiv.prod_comp σ.symm (fun a => (orbitalBasis G theta (w a)).val (z (σ a)))).symm

/-- Bosonic symmetry is actual permutation invariance of the N-point function. -/
theorem symWordFunction_permute_configuration (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) (σ : Equiv.Perm (Fin N)) (z : Configuration N) :
    symWordFunction G theta N w (z ∘ σ) = symWordFunction G theta N w z := by
  classical
  unfold symWordFunction
  congr 1
  simp only [wordFunction_permute_configuration]
  simpa only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Function.comp_def] using
    Equiv.sum_comp (Equiv.mulRight σ.symm)
      (fun τ => wordFunction G theta N (w ∘ τ) z)

theorem occupationFunction_permute_configuration (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) (σ : Equiv.Perm (Fin N)) (z : Configuration N) :
    occupationFunction G theta N n (z ∘ σ) = occupationFunction G theta N n z := by
  classical
  unfold occupationFunction
  split_ifs with hn
  · exact symWordFunction_permute_configuration G theta N _ σ z
  · rfl

theorem coreFunction_permute_configuration (G : Geometry) (theta : Twist) (N : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (σ : Equiv.Perm (Fin N)) (z : Configuration N) :
    coreFunction G theta N f (z ∘ σ) = coreFunction G theta N f z := by
  simp only [coreFunction_apply, occupationFunction_permute_configuration]

theorem occupationFunction_zero (G : Geometry) (theta : Twist) :
    occupationFunction G theta 0 0 = fun _ => 1 := by
  classical
  rw [occupationFunction, dif_pos (by simp), symWordFunction_zero]

/-- A genuine scalar vacuum survives, including the empty physical orbital space. -/
theorem coreFunction_C_vacuum (G : Geometry) (theta : Twist) (c : ℂ) :
    coreFunction G theta 0 (MvPolynomial.C c) = fun _ => c := by
  have hc : (MvPolynomial.C c : Core (OrbitalIndex G theta) ℂ) =
      MvPolynomial.monomial 0 c := rfl
  rw [hc, coreFunction_monomial, occupationFunction_zero]
  funext z
  simp [Pi.smul_apply, smul_eq_mul]

theorem sectorFunction_injective (G : Geometry) (theta : Twist) (N : ℕ) :
    Function.Injective (sectorFunction G theta N) := by
  intro f g h
  have hz : sectorFunction G theta N (f - g) = 0 := by
    rw [map_sub, h, sub_self]
  have hn := sectorFunction_normSq G theta N (f - g)
  rw [hz] at hn
  simp only [Pi.zero_apply, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    integral_zero] at hn
  apply Subtype.ext
  by_contra he
  have hp := occupationMetricNormSq_pos (fun _ : OrbitalIndex G theta => 1)
    (fun _ => by omega) (f.val - g.val) (sub_ne_zero.mpr he)
  change 0 = occupationMetricNormSq (fun _ => 1) (f.val - g.val) at hn
  linarith

/-- Empty physical orbital space kills positive-particle sectors while
the independently proved scalar vacuum remains. -/
theorem homogeneous_eq_zero_of_empty (G : Geometry) (theta : Twist) (N : ℕ)
    (he : ¬ Nonempty (OrbitalIndex G theta)) (hN : 0 < N)
    (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous N) : f = 0 := by
  classical
  by_contra hzero
  obtain ⟨n, hn⟩ := MvPolynomial.support_nonempty.mpr hzero
  have hd : n.degree = N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.mp hn)
  obtain ⟨w, hw⟩ := exists_word_of_degree G theta N n hd
  exact he ⟨w ⟨0, hN⟩⟩


/-- Exact compatibility with the existing inherited-norm physical Sym2:
the unnormalized occupation monomial is sqrt(2) times its actual symmetric
tensor function, so the accepted Fock coefficient 1/sqrt(2) recovers Sym2. -/
theorem occupationFunction_two_symTensor (G : Geometry) (theta : Twist)
    (i j : OrbitalIndex G theta) (z : Configuration 2) :
    occupationFunction G theta 2 (Finsupp.single i 1 + Finsupp.single j 1) z =
      (Real.sqrt 2 : ℂ) *
        rawPairFunction G theta 1 1
          (TorusLean.Boson.Sym2Evaluation.symTensor
            (orbitalBasis G theta i) (orbitalBasis G theta j)).val (z 0, z 1) := by
  classical
  let w : Word G theta 2 := ![i, j]
  have hn : wordOccupation G theta 2 w = Finsupp.single i 1 + Finsupp.single j 1 := by
    simp [wordOccupation, Fin.sum_univ_two, w]
  rw [← hn, occupationFunction_word, symWordFunction_two]
  simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one,
    TorusLean.Boson.Sym2Evaluation.symTensor_val, map_smul, map_add,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hp (f g : LLL G theta 1) :
      rawPairFunction G theta 1 1 (f ⊗ₜ[ℂ] g) (z 0, z 1) = f.val (z 0) * g.val (z 1) :=
    rawPairFunction_tmul_apply G theta 1 1 (lllRawEquiv G theta 1 f)
      (lllRawEquiv G theta 1 g) (z 0, z 1)
  rw [hp, hp]
  have hs : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    rw [inv_eq_one_div, div_eq_div_iff hn (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs, Complex.ofReal_div]
  norm_num
  ring


end TorusLean.Shared.PhysicalBosonSector
