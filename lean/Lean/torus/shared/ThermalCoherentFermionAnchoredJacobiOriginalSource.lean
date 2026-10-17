import torus.shared.ThermalCoherentFermionAnchoredJacobiOuterExchange
import torus.shared.ThermalCoherentFermionAnchoredJacobiFiniteBridge
import torus.shared.ThermalCoherentFermionAnchoredJacobiRemoval

/-! Actual S3 two columns regrouped into the original exterior anchor and
its actual connected source. The individual absolute convergence was proved
before the index shift. No finite K identity substitutes for physical S3. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOriginalSource
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.FermionLocalJet
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Fermion.LatticePacking
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAnchoredColumns
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOuterExchange
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open scoped BigOperators ComplexConjugate

def firstPhysicalColumn (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (p : ℕ) (R : ℂ) : ℂ :=
  -((Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p *
    anchoredCross G theta x y (p+1) 1 p R)

def secondPhysicalColumn (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (p : ℕ) (R : ℂ) : ℂ :=
  ((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p * anchoredCross G theta x y p 0 p R

def originalSourceCross (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (l : ℕ) (R : ℂ) : ℂ :=
  occupationInner (physicalQ G theta)
    (formalRemoval G theta R (formalAnchoredSeed l) x)
    (formalRemoval G theta R (formalConnectedAnchoredSeed l) y)

theorem originalSourceCross_zero (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (R : ℂ) :
    originalSourceCross G theta x y 0 R=0 := by
  simp [originalSourceCross,formalAnchoredSeed_zero,formalRemoval_zero,occupationInner]

theorem originalSourceCross_one (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (R : ℂ) :
    originalSourceCross G theta x y 1 R=0 := by
  simp [originalSourceCross,formalAnchoredSeed_one,formalRemoval_zero,occupationInner]

private theorem occ_sub_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y-z)=occupationInner Q x y-occupationInner Q x z := by
  simp [occupationInner,mul_sub,Finset.sum_sub_distrib]

/-- Actual source identity, including conjugation of removal coefficients. -/
theorem originalSourceCross_succ (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (p : ℕ) (R : ℂ) :
    originalSourceCross G theta x y (p+1) R =
      firstPhysicalColumn G theta x y p R+secondPhysicalColumn G theta x y (p+1) R := by
  rw [originalSourceCross,formalAnchoredSeed,formalConnectedAnchoredSeed_explicit,
    formalRemoval_sub,formalRemoval_smul,formalRemoval_smul,
    formalRemoval_three,formalRemoval_three,formalRemoval_three,
    occ_sub_right,occupationInner_smul_right,occupationInner_smul_right]
  simp only [map_div₀,map_pow,map_natCast,Complex.conj_ofReal,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_natCast,Complex.ofReal_add,Complex.ofReal_one,
    firstPhysicalColumn,secondPhysicalColumn,anchoredCross,localJetAnnihilate,
    physicalAnnihilate,physicalJetCoordinates,
    pairDescendant_zero,Nat.cast_add,Nat.cast_one]
  ring

theorem secondPhysicalColumn_zero (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (R : ℂ) :
    secondPhysicalColumn G theta x y 0 R=0 := by
  have ha : formalRemoval G theta R (formalThreeSeed 0 0) x=0 := by
    simpa only [formalAnchoredSeed] using
      (show formalRemoval G theta R (formalAnchoredSeed 0) x=0 by
        rw [formalAnchoredSeed_zero,formalRemoval_zero])
  rw [formalRemoval_three] at ha
  simp only [pairDescendant_zero,localJetAnnihilate,physicalAnnihilate] at ha
  simp [secondPhysicalColumn,anchoredCross,physicalJetCoordinates,ha,occupationInner]

theorem firstPhysicalColumn_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (p : ℕ) :
    Integrable (firstPhysicalColumn G theta x y p) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2
    (continuous_const.mul (anchoredCross_continuous G theta x y (p+1) 1 p)).neg

theorem secondPhysicalColumn_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (p : ℕ) :
    Integrable (secondPhysicalColumn G theta x y p) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2
    (continuous_const.mul (anchoredCross_continuous G theta x y p 0 p))

theorem originalSourceCross_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (l : ℕ) :
    Integrable (originalSourceCross G theta x y l) (cellMeasure G 2) := by
  cases l with
  | zero =>
    have he : originalSourceCross G theta x y 0 = fun _ : ℂ => 0 := by
      funext R
      exact originalSourceCross_zero G theta x y R
    rw [he]
    exact integrable_zero ℂ ℂ (cellMeasure G 2)
  | succ p =>
    have he : originalSourceCross G theta x y (p+1) = fun R =>
        firstPhysicalColumn G theta x y p R +
          secondPhysicalColumn G theta x y (p+1) R := by
      funext R
      exact originalSourceCross_succ G theta x y p R
    change Integrable (originalSourceCross G theta x y (p+1)) (cellMeasure G 2)
    rw [he]
    exact (firstPhysicalColumn_integrable G theta x y p).add
      (secondPhysicalColumn_integrable G theta x y (p+1))

private theorem regroup_hasSum (f g h : ℕ → ℂ) (s : ℂ)
    (hf : Summable f) (hg : Summable g) (hg0 : g 0=0) (hh0 : h 0=0)
    (hh : ∀ p, h (p+1)=f p+g (p+1)) (hs : HasSum (fun p => f p+g p) s) :
    HasSum h s := by
  have he : (∑' p, f p)+(∑' p, g p)=s := (hf.hasSum.add hg.hasSum).unique hs
  have hg' : HasSum (fun p => g (p+1)) (∑' p, g p) := by
    apply (hasSum_nat_add_iff 1).mpr
    simpa only [Finset.sum_range_one,hg0,add_zero] using hg.hasSum
  have hh' : HasSum (fun p => h (p+1)) s := by
    simpa only [hh,he] using hf.hasSum.add hg'
  have hv := (hasSum_nat_add_iff 1).mp hh'
  simpa only [Finset.sum_range_one,hh0,add_zero] using hv

/-- Physical S3 has exactly the original two exterior-source columns.
Low degree zeros are proved before reindexing, not removed by scalar fiat. -/
theorem matrixSingleContraction_original_source_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    HasSum (fun l => ∫ R, originalSourceCross G theta x y l R ∂cellMeasure G 2)
      (occupationInner (physicalQ G theta) x
        (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y)) := by
  obtain ⟨ha,hb⟩ := originalColumns_individually_absolute G theta hG x y
  have ha' : Summable (fun p : ℕ => ∫ R,
      ‖firstPhysicalColumn G theta x y p R‖ ∂cellMeasure G 2) := by
    simpa only [firstPhysicalColumn,norm_neg] using ha
  have hf := (hasSum_integral_of_summable_integral_norm
    (firstPhysicalColumn_integrable G theta x y) ha').summable
  have hg := (hasSum_integral_of_summable_integral_norm
    (secondPhysicalColumn_integrable G theta x y) hb).summable
  apply regroup_hasSum _ _ _ _ hf hg
  · simp only [secondPhysicalColumn_zero,integral_zero]
  · simp only [originalSourceCross_zero,integral_zero]
  · intro p
    simp only [originalSourceCross_succ]
    exact integral_add (firstPhysicalColumn_integrable G theta x y p)
      (secondPhysicalColumn_integrable G theta x y (p+1))
  · have hs := matrixSingleContraction_original_columns_hasSum G theta hG x y
    have he (p : ℕ) : (∫ R, originalColumnTerm G theta x y p R ∂cellMeasure G 2)=
        (∫ R, firstPhysicalColumn G theta x y p R ∂cellMeasure G 2)+
          (∫ R, secondPhysicalColumn G theta x y p R ∂cellMeasure G 2) :=
      integral_add (firstPhysicalColumn_integrable G theta x y p)
        (secondPhysicalColumn_integrable G theta x y p)
    simpa only [he] using hs

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOriginalSource
