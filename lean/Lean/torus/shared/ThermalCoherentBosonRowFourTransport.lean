import torus.shared.ThermalCoherentBosonRowFiniteDual
import torus.shared.BosonNatFourFiniteRotation

/-! Finite source-coefficient identities transported to the existing actual
conjugate-linear annihilation rows on every finite physical core. The generic
source-form premise is explicit; the original certificate application must
discharge it using the true canonical row restriction. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowFourTransport
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ThermalCoherentFourBodyFrame
open TorusLean.Shared.BosonNatFourAnnihilator TorusLean.Shared.BosonAnchoredNatLinearActions
open TorusLean.Shared.BosonNatFourFiniteRotation
open TorusLean.Shared.ThermalCoherentBosonRowFiniteDual
open scoped BigOperators ComplexConjugate
local instance rowFourTransport_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Finite scalar coefficient equality implies the actual full-core complex
row identity, even when source images have kernels or are not orthogonal. -/
theorem finite_annihilator_weighted_cross_congr {I J : Type*} [Fintype I] [Fintype J]
    (G : Geometry) (theta : Twist) (p q : I → Core ℕ ℂ) (r s : J → Core ℕ ℂ)
    (c : I → ℂ) (d : J → ℂ)
    (h : ∀ F H : Core ℕ ℂ →ₗ[ℂ] ℂ,
      (∑ i, c i * F (p i) * star (H (q i))) = ∑ j, d j * F (r j) * star (H (s j)))
    (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, c i * ip (natFourAnnihilator G theta R (p i) f)
      (natFourAnnihilator G theta R (q i) g)) =
      ∑ j, d j * ip (natFourAnnihilator G theta R (r j) f)
        (natFourAnnihilator G theta R (s j) g) := by
  simp_rw [natFourAnnihilator_cross_expansion,Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset I)),
    Finset.sum_comm (s := (Finset.univ : Finset J))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm (s := (Finset.univ : Finset I)),
    Finset.sum_comm (s := (Finset.univ : Finset J))]
  apply Finset.sum_congr rfl
  intro b hb
  have he := h
    ((LinearMap.proj R).comp (seedDualMapNat G theta (quadVacuum a).val))
    ((LinearMap.proj R).comp (seedDualMapNat G theta (quadVacuum b).val))
  have hm := congrArg (fun z => ip (quadRemove a f) (quadRemove b g)*z) he
  simp only [Finset.mul_sum,LinearMap.comp_apply,LinearMap.proj_apply,Complex.star_def] at hm
  convert hm using 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- The missing N4-to-allN step is actual finite Riesz coefficient separation
followed by actual annihilator expansion, rather than a sector-lift assumption. -/
theorem finite_source_form_actual_cross {I J : Type*} [Fintype I] [Fintype J]
    (G : Geometry) (theta : Twist) (p q : I → Core ℕ ℂ) (r s : J → Core ℕ ℂ)
    (c : I → ℂ) (d : J → ℂ)
    (hp : ∀ i, (p i).IsHomogeneous 4) (hq : ∀ i, (q i).IsHomogeneous 4)
    (hr : ∀ j, (r j).IsHomogeneous 4) (hs : ∀ j, (s j).IsHomogeneous 4)
    (h : ∀ x y : Core ℕ ℂ, x.IsHomogeneous 4 → y.IsHomogeneous 4 →
      (∑ i, c i * star (natOccupationInner (p i) x) * natOccupationInner (q i) y) =
        ∑ j, d j * star (natOccupationInner (r j) x) * natOccupationInner (s j) y)
    (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i, c i * ip (natFourAnnihilator G theta R (p i) f)
      (natFourAnnihilator G theta R (q i) g)) =
      ∑ j, d j * ip (natFourAnnihilator G theta R (r j) f)
        (natFourAnnihilator G theta R (s j) g) :=
  finite_annihilator_weighted_cross_congr G theta p q r s c d
    (finite_source_cross_separation 4 p q r s c d hp hq hr hs h) R f g

end TorusLean.Shared.ThermalCoherentBosonRowFourTransport
