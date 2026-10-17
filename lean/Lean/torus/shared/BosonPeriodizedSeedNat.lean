import torus.shared.ThermalCoherentSeedWord

/-! Locally finite polynomial periodization with arbitrary natural mode
labels.  This is defined only on finite polynomials; no bounded map on an
infinite planar completion is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.BosonPeriodizedSeed
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.ThermalCoherentSeedWord
open TorusLean.Shared.ParameterRawJetWord
open scoped BigOperators

def anchoredSeedNat (G : Geometry) (theta : Twist) (R : ℂ) :
    Core ℕ ℂ →ₐ[ℂ] Core (OrbitalIndex G theta) ℂ :=
  MvPolynomial.aeval (fun j => modeLinear ((orbitalBasis G theta).repr (rawPlaneJet G theta j R)))

theorem anchoredSeedNat_X (G : Geometry) (theta : Twist) (R : ℂ) (j : ℕ) :
    anchoredSeedNat G theta R (MvPolynomial.X j) =
      modeLinear ((orbitalBasis G theta).repr (rawPlaneJet G theta j R)) := by
  simp [anchoredSeedNat]

theorem anchoredSeedNat_sector (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous N) :
    (anchoredSeedNat G theta R p).IsHomogeneous N := by
  simpa only [anchoredSeedNat, one_mul] using hp.aeval
    (fun j : ℕ => modeLinear ((orbitalBasis G theta).repr (rawPlaneJet G theta j R)))
    (fun j => modeLinear_sector _)

def physicalAnchoredSeedNat (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous N) : PhysicalBosonCarrier G theta N :=
  sectorPhysical G theta N ⟨anchoredSeedNat G theta R p, anchoredSeedNat_sector G theta N R p hp⟩

/-- Exact compatibility with every finite cutoff. It does not impose a
cutoff on the natural-index polynomial map. -/
theorem anchoredSeedNat_rename_fin (G : Geometry) (theta : Twist) (K : ℕ) (R : ℂ)
    (p : Core (Fin K) ℂ) :
    anchoredSeedNat G theta R (MvPolynomial.rename Fin.val p) = anchoredSeed G theta K R p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [anchoredSeedNat, anchoredSeed]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, MvPolynomial.rename_X, anchoredSeedNat_X, anchoredSeed_X, hp]

theorem anchoredSeedNat_word (G : Geometry) (theta : Twist) (k : ℕ)
    (j : Fin k → ℕ) (R : ℂ) :
    anchoredSeedNat G theta R (canonicalWord k j) =
      ∏ a, modeLinear ((orbitalBasis G theta).repr (rawPlaneJet G theta (j a) R)) := by
  simp only [canonicalWord, map_prod, anchoredSeedNat_X]

theorem anchoredSeedNat_word_expansion (G : Geometry) (theta : Twist) (k : ℕ)
    (j : Fin k → ℕ) (R : ℂ) :
    anchoredSeedNat G theta R (canonicalWord k j) =
      ∑ w : Fin k → OrbitalIndex G theta,
        rawWord G theta k (fun a => orbitalBasis G theta (w a)) j R • canonicalWord k w := by
  rw [anchoredSeedNat_word, modeLinear_word_expansion]
  simp only [rawWord, actualJetCoordinate_eq_dualRaw]

theorem anchoredSeedNat_word_dual_expansion (G : Geometry) (theta : Twist) (k : ℕ)
    (j : Fin k → ℕ) (q : Core (OrbitalIndex G theta) ℂ) (R : ℂ) :
    occupationInner (fun _ => 1) q (anchoredSeedNat G theta R (canonicalWord k j)) =
      ∑ w : Fin k → OrbitalIndex G theta,
        occupationInner (fun _ => 1) q (canonicalWord k w) *
          rawWord G theta k (fun a => orbitalBasis G theta (w a)) j R := by
  rw [anchoredSeedNat_word_expansion]
  have hs (s : Finset (Fin k → OrbitalIndex G theta))
      (g : (Fin k → OrbitalIndex G theta) → Core (OrbitalIndex G theta) ℂ) :
      occupationInner (fun _ => 1) q (∑ w ∈ s, g w) =
        ∑ w ∈ s, occupationInner (fun _ => 1) q (g w) := by
    induction s using Finset.induction_on with
    | empty => simp [occupationInner_zero_right]
    | @insert w s hw ih => simp [hw, occupationInner_add_right, ih]
  rw [hs]
  simp only [occupationInner_smul_right, mul_comm]

end TorusLean.Shared.BosonPeriodizedSeedNat
