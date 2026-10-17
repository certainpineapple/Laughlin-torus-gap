import ThetaAnalyticBoundary
import ThetaAnalyticNormal
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

/-!
Every sequence in the previously classified coefficient recurrence is realized
by an entire function with the exact theta boundary laws. This is a construction
theorem. Fourier extraction/uniqueness for arbitrary entire sections and physical
kernel identification remain separate obligations.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaAnalytic

open Complex Real ThetaFactorization

def realizedSection (d : ℕ) (tau sigma psi : ℂ) (v : ZMod d → ℂ) (z : ℂ) : ℂ :=
  ∑ r : Fin d, v (r.val : ZMod d) * residueSection d tau sigma psi (r.val : ℤ) z

def weightedFourierTerm (d : ℕ) (tau sigma psi : ℂ) (v : ZMod d → ℂ)
    (z : ℂ) (n : ℤ) : ℂ :=
  physicalWeight d tau sigma psi n * v (n : ZMod d) *
    exp (2 * π * I * ((n : ℂ) + sigma) * z)

def residueIndexEquiv (d : ℕ) [NeZero d] : (Fin d × ℤ) ≃ ℤ :=
  (Equiv.prodComm (Fin d) ℤ).trans (Int.divModEquiv d).symm

theorem realizedSection_differentiable (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) :
    Differentiable ℂ (realizedSection d tau sigma psi v) := by
  classical
  unfold realizedSection
  apply Differentiable.fun_sum
  intro r _
  exact (residueSection_differentiable d tau sigma psi hτ (r.val : ℤ)).const_mul _

theorem realizedSection_add_one (d : ℕ) (tau sigma psi : ℂ) (v : ZMod d → ℂ) (z : ℂ) :
    realizedSection d tau sigma psi v (z + 1) =
      exp (2 * π * I * sigma) * realizedSection d tau sigma psi v z := by
  classical
  unfold realizedSection
  simp_rw [residueSection_add_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem realizedSection_add_tau (d : ℕ) (tau sigma psi : ℂ) (v : ZMod d → ℂ) (z : ℂ) :
    realizedSection d tau sigma psi v (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * tau - 2 * π * I * (d : ℂ) * z) *
        realizedSection d tau sigma psi v z := by
  classical
  unfold realizedSection
  simp_rw [residueSection_add_tau, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem weightedFourierTerm_residue (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (v : ZMod d → ℂ) (z : ℂ) (r : Fin d) (k : ℤ) :
    weightedFourierTerm d tau sigma psi v z (residueIndexEquiv d (r, k)) =
      v (r.val : ZMod d) * residueTerm d tau sigma psi (r.val : ℤ) z k := by
  have he : residueIndexEquiv d (r, k) = (r.val : ℤ) + (d : ℤ) * k := by
    simp [residueIndexEquiv, Int.divModEquiv_symm_apply, mul_comm, add_comm]
  rw [he]
  unfold weightedFourierTerm residueTerm fourierTerm
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero]
  ring

/-- All integer modes of every coefficient solution are absolutely summable. -/
theorem weightedFourierTerm_summable (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) (z : ℂ) :
    Summable (weightedFourierTerm d tau sigma psi v z) := by
  classical
  let f : Fin d × ℤ → ℂ := fun p =>
    v (p.1.val : ZMod d) * residueTerm d tau sigma psi (p.1.val : ℤ) z p.2
  have hr (r : Fin d) : Summable (fun k : ℤ =>
      v (r.val : ZMod d) * residueTerm d tau sigma psi (r.val : ℤ) z k) :=
    (residueTerm_summable d tau sigma psi hτ (r.val : ℤ) z).mul_left (v (r.val : ZMod d))
  have hf : Summable f := by
    apply summable_norm_iff.mp
    apply (summable_prod_of_nonneg (fun p => norm_nonneg (f p))).mpr
    exact ⟨fun r => (hr r).norm, Summable.of_finite⟩
  have hcomp : Summable ((weightedFourierTerm d tau sigma psi v z) ∘ residueIndexEquiv d) :=
    hf.congr (fun p => (weightedFourierTerm_residue d tau sigma psi v z p.1 p.2).symm)
  exact (residueIndexEquiv d).summable_iff.mp hcomp

theorem weightedFourierTerm_hasSum (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) (z : ℂ) :
    HasSum (weightedFourierTerm d tau sigma psi v z) (realizedSection d tau sigma psi v z) := by
  classical
  have hs := weightedFourierTerm_summable d tau sigma psi hτ v z
  have hprod : Summable (fun p : Fin d × ℤ => v (p.1.val : ZMod d) *
      residueTerm d tau sigma psi (p.1.val : ℤ) z p.2) := by
    exact ((residueIndexEquiv d).summable_iff.mpr hs).congr
      (fun p => weightedFourierTerm_residue d tau sigma psi v z p.1 p.2)
  convert hs.hasSum using 1
  rw [← (residueIndexEquiv d).tsum_eq, show
    (fun p : Fin d × ℤ => weightedFourierTerm d tau sigma psi v z (residueIndexEquiv d p)) =
      (fun p : Fin d × ℤ => v (p.1.val : ZMod d) *
        residueTerm d tau sigma psi (p.1.val : ℤ) z p.2) by
      funext p; exact weightedFourierTerm_residue d tau sigma psi v z p.1 p.2]
  rw [hprod.tsum_prod]
  simp_rw [tsum_mul_left, residueTerm_tsum d tau sigma psi hτ]
  rw [tsum_fintype]
  rfl

/-- A single summable majorant controls every integer mode uniformly on `K`. -/
theorem weightedFourierTerm_normal_convergence (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) (K : Set ℂ) (hK : IsCompact K) :
    ∃ b : ℤ → ℝ, Summable b ∧
      ∀ z ∈ K, ∀ n : ℤ, ‖weightedFourierTerm d tau sigma psi v z n‖ ≤ b n := by
  classical
  choose b hb hbound using fun r : Fin d =>
    residueTerm_normal_convergence d tau sigma psi hτ (r.val : ℤ) K hK
  let B : Fin d × ℤ → ℝ := fun p => ‖v (p.1.val : ZMod d)‖ * ‖b p.1 p.2‖
  have hBn : 0 ≤ B := fun p =>
    mul_nonneg (norm_nonneg (v (p.1.val : ZMod d))) (norm_nonneg (b p.1 p.2))
  have hB : Summable B := by
    apply (summable_prod_of_nonneg hBn).mpr
    exact ⟨fun r => (hb r).norm.mul_left ‖v (r.val : ZMod d)‖, Summable.of_finite⟩
  refine ⟨fun n => B ((residueIndexEquiv d).symm n),
    (residueIndexEquiv d).symm.summable_iff.mpr hB, ?_⟩
  intro z hz n
  obtain ⟨⟨r, k⟩, rfl⟩ := (residueIndexEquiv d).surjective n
  rw [weightedFourierTerm_residue, norm_mul]
  change ‖v (r.val : ZMod d)‖ * ‖residueTerm d tau sigma psi (r.val : ℤ) z k‖ ≤
    B ((residueIndexEquiv d).symm (residueIndexEquiv d (r, k)))
  rw [Equiv.symm_apply_apply]
  exact mul_le_mul_of_nonneg_left ((hbound r z hz k).trans (le_norm_self _)) (norm_nonneg _)

theorem weightedFourierTerm_tendstoUniformlyOn (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun s : Finset ℤ => fun z : ℂ => ∑ n ∈ s, weightedFourierTerm d tau sigma psi v z n)
      (realizedSection d tau sigma psi v) Filter.atTop K := by
  obtain ⟨b, hb, hbound⟩ := weightedFourierTerm_normal_convergence d tau sigma psi hτ v K hK
  have h := tendstoUniformlyOn_tsum hb (fun n z hz => hbound z hz n)
  simpa only [(weightedFourierTerm_hasSum d tau sigma psi hτ v _).tsum_eq] using h

def recurrenceResidues (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (c : thetaRecurrenceSpace d (π * I * tau) (-I * psi) sigma) : ZMod d → ℂ :=
  thetaCoefficientEquiv d (π * I * tau) (-I * psi) sigma c

theorem recurrenceCoefficients_eq (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (c : thetaRecurrenceSpace d (π * I * tau) (-I * psi) sigma) (n : ℤ) :
    c.1 n = physicalWeight d tau sigma psi n * recurrenceResidues d tau sigma psi c (n : ZMod d) := by
  have h := congrArg (fun e : thetaRecurrenceSpace d (π * I * tau) (-I * psi) sigma => e.1 n)
    ((thetaCoefficientEquiv d (π * I * tau) (-I * psi) sigma).symm_apply_apply c)
  exact h.symm

/-- The existing algebraic classification is now attached to a convergent
Fourier expansion, with no truncation and no convergence premise on `c`. -/
theorem recurrenceFourier_hasSum (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (c : thetaRecurrenceSpace d (π * I * tau) (-I * psi) sigma)
    (z : ℂ) :
    HasSum (fun n : ℤ => c.1 n * exp (2 * π * I * ((n : ℂ) + sigma) * z))
      (realizedSection d tau sigma psi (recurrenceResidues d tau sigma psi c) z) := by
  have h := weightedFourierTerm_hasSum d tau sigma psi hτ (recurrenceResidues d tau sigma psi c) z
  change HasSum (fun n : ℤ => weightedFourierTerm d tau sigma psi
    (recurrenceResidues d tau sigma psi c) z n) _ at h
  simpa only [recurrenceCoefficients_eq d tau sigma psi c, weightedFourierTerm] using h

/-- Construction of an entire degree-d section from every recurrence solution.
This conclusion includes both automorphy equations and the full bilateral sum.
It does not assert that every entire section has such an expansion. -/
theorem recurrence_realization (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (c : thetaRecurrenceSpace d (π * I * tau) (-I * psi) sigma) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z, F (z + 1) = exp (2 * π * I * sigma) * F z) ∧
      (∀ z, F (z + tau) =
        exp (I * psi - π * I * (d : ℂ) * tau - 2 * π * I * (d : ℂ) * z) * F z) ∧
      (∀ z, HasSum (fun n : ℤ => c.1 n * exp (2 * π * I * ((n : ℂ) + sigma) * z)) (F z)) := by
  let v := recurrenceResidues d tau sigma psi c
  exact ⟨realizedSection d tau sigma psi v,
    realizedSection_differentiable d tau sigma psi hτ v,
    realizedSection_add_one d tau sigma psi v,
    realizedSection_add_tau d tau sigma psi v,
    recurrenceFourier_hasSum d tau sigma psi hτ c⟩

/-- Real cycle twists in the manuscript gauge `sigma = psi1 / (2*pi)`.
Every coefficient solution yields an entire section with these exact twists. -/
theorem real_twist_recurrence_realization (d : ℕ) [NeZero d] (tau : ℂ)
    (psi1 psi2 : ℝ) (hτ : 0 < tau.im)
    (c : thetaRecurrenceSpace d (π * I * tau) (-I * (psi2 : ℂ))
      ((psi1 / (2 * π) : ℝ) : ℂ)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z, F (z + 1) = exp (I * (psi1 : ℂ)) * F z) ∧
      (∀ z, F (z + tau) =
        exp (I * (psi2 : ℂ) - π * I * (d : ℂ) * (2 * z + tau)) * F z) ∧
      (∀ z, HasSum (fun n : ℤ => c.1 n *
        exp (2 * π * I * ((n : ℂ) + ((psi1 / (2 * π) : ℝ) : ℂ)) * z)) (F z)) := by
  obtain ⟨F, hF, h1, ht, hs⟩ :=
    recurrence_realization d tau ((psi1 / (2 * π) : ℝ) : ℂ) (psi2 : ℂ) hτ c
  refine ⟨F, hF, ?_, ?_, hs⟩
  · intro z
    rw [h1]
    have he : 2 * (π : ℂ) * I * ((psi1 / (2 * π) : ℝ) : ℂ) = I * (psi1 : ℂ) := by
      push_cast
      have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp [hp]
    rw [he]
  · intro z
    rw [ht]
    congr 2
    ring

end TorusLean.Geometry.ThetaAnalytic
