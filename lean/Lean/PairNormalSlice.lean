import JastrowLocalDivision
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
Exchange parity and the actual pair-normal holomorphic slice. This is a
function-level local analytic bridge, not a replacement physical Hilbert
space or Hamiltonian. Joint analyticity in all spectator coordinates and
division by the full theta-Jastrow product remain separate obligations.
-/

noncomputable section

namespace TorusLean.Geometry.JastrowDivision

open Filter
open scoped Topology

/-- Equal physical charges use precisely the manuscript Jacobi coordinates
`(C+r/2,C-r/2)`. The other particle coordinates may already be frozen in F. -/
def pairNormalSlice (F : ℂ × ℂ → ℂ) (C r : ℂ) : ℂ :=
  F (C + r / 2, C - r / 2)

theorem pairNormalSlice_analytic (F : ℂ × ℂ → ℂ) (C : ℂ)
    (hF : AnalyticAt ℂ F (C, C)) : AnalyticAt ℂ (pairNormalSlice F C) 0 := by
  have hm : AnalyticAt ℂ (fun r : ℂ => (C + r / 2, C - r / 2)) 0 := by fun_prop
  have hF' : AnalyticAt ℂ F ((fun r : ℂ => (C + r / 2, C - r / 2)) 0) := by
    simpa using hF
  exact hF'.comp (f := fun r : ℂ => (C + r / 2, C - r / 2)) (x := 0) hm

theorem pairNormalSlice_odd (F : ℂ × ℂ → ℂ)
    (hF : ∀ x y : ℂ, F (y, x) = -F (x, y)) (C r : ℂ) :
    pairNormalSlice F C (-r) = -pairNormalSlice F C r := by
  unfold pairNormalSlice
  have h := hF (C + r / 2) (C - r / 2)
  simpa only [neg_div, sub_eq_add_neg, neg_neg] using h

theorem pairNormalSlice_even (F : ℂ × ℂ → ℂ)
    (hF : ∀ x y : ℂ, F (y, x) = F (x, y)) (C r : ℂ) :
    pairNormalSlice F C (-r) = pairNormalSlice F C r := by
  unfold pairNormalSlice
  have h := hF (C + r / 2) (C - r / 2)
  simpa only [neg_div, sub_eq_add_neg, neg_neg] using h

theorem odd_even_jets_zero (f : ℂ → ℂ) (hodd : ∀ r, f (-r) = -f r) (k : ℕ) :
    iteratedDeriv (2 * k) f 0 = 0 := by
  have he : (fun r => f (-r)) = (fun r => -f r) := funext hodd
  have h := congrArg (fun g : ℂ → ℂ => iteratedDeriv (2 * k) g 0) he
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at h
  have hs : (-1 : ℂ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  simp only [hs, neg_zero, one_smul] at h
  have hz : (2 : ℂ) * iteratedDeriv (2 * k) f 0 = 0 := by
    calc
      _ = iteratedDeriv (2 * k) f 0 - -iteratedDeriv (2 * k) f 0 := by ring
      _ = 0 := by rw [← h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem even_odd_jets_zero (f : ℂ → ℂ) (heven : ∀ r, f (-r) = f r) (k : ℕ) :
    iteratedDeriv (2 * k + 1) f 0 = 0 := by
  have he : (fun r => f (-r)) = f := funext heven
  have h := congrArg (fun g : ℂ → ℂ => iteratedDeriv (2 * k + 1) g 0) he
  rw [iteratedDeriv_comp_neg] at h
  have hs : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  simp only [hs, neg_zero, neg_one_smul] at h
  have hz : (2 : ℂ) * iteratedDeriv (2 * k + 1) f 0 = 0 := by
    calc
      _ = iteratedDeriv (2 * k + 1) f 0 - -iteratedDeriv (2 * k + 1) f 0 := by ring
      _ = 0 := by rw [h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Fermionic exchange parity and the vanishing degree-one contact jet
produce the cubic divisor, rather than assuming a quotient exists. -/
theorem odd_contact_local_cubic_division (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hodd : ∀ r, f (-r) = -f r) (hcontact : deriv f 0 = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ ∀ᶠ r in 𝓝 0, f r = r ^ 3 * q r := by
  have hjets : ∀ j < 3, iteratedDeriv j f 0 = 0 := by
    intro j hj
    have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · simpa using odd_even_jets_zero f hodd 0
    · simpa only [iteratedDeriv_one] using hcontact
    · simpa using odd_even_jets_zero f hodd 1
  obtain ⟨q, hq, hfactor⟩ := local_pow_division_of_jets f 0 3 hf hjets
  exact ⟨q, hq, by simpa using hfactor⟩

/-- Bosonic exchange parity and contact value zero produce a quadratic
local divisor. -/
theorem even_contact_local_quadratic_division (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (heven : ∀ r, f (-r) = f r) (hcontact : f 0 = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ ∀ᶠ r in 𝓝 0, f r = r ^ 2 * q r := by
  have hjets : ∀ j < 2, iteratedDeriv j f 0 = 0 := by
    intro j hj
    have hc : j = 0 ∨ j = 1 := by omega
    rcases hc with rfl | rfl
    · simpa only [iteratedDeriv_zero] using hcontact
    · simpa using even_odd_jets_zero f heven 0
  obtain ⟨q, hq, hfactor⟩ := local_pow_division_of_jets f 0 2 hf hjets
  exact ⟨q, hq, by simpa using hfactor⟩

theorem antisymmetric_pair_contact_local_division (F : ℂ × ℂ → ℂ) (C : ℂ)
    (hF : AnalyticAt ℂ F (C, C))
    (hstats : ∀ x y, F (y, x) = -F (x, y))
    (hcontact : deriv (pairNormalSlice F C) 0 = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ r in 𝓝 0, F (C + r / 2, C - r / 2) = r ^ 3 * q r :=
  odd_contact_local_cubic_division (pairNormalSlice F C)
    (pairNormalSlice_analytic F C hF) (pairNormalSlice_odd F hstats C) hcontact

theorem symmetric_pair_contact_local_division (F : ℂ × ℂ → ℂ) (C : ℂ)
    (hF : AnalyticAt ℂ F (C, C))
    (hstats : ∀ x y, F (y, x) = F (x, y)) (hcontact : F (C, C) = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ r in 𝓝 0, F (C + r / 2, C - r / 2) = r ^ 2 * q r := by
  apply even_contact_local_quadratic_division (pairNormalSlice F C)
    (pairNormalSlice_analytic F C hF) (pairNormalSlice_even F hstats C)
  simpa [pairNormalSlice] using hcontact

end TorusLean.Geometry.JastrowDivision
