import torus.shared.BosonNatThreeActualCOMTransport
import torus.shared.BosonNatThreeUnnormalizedTrace
import torus.shared.BosonFiniteCertificateNatCOMBasisLabels
import torus.shared.BosonFiniteCertificateNatRelative

/-! True cell trace of the nine complete source COM matrices. The integrand
retains all relative-degree cross entries until actual ladder orthogonality. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeCOMCellTrace
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonNatThreeUnnormalizedTrace
open MeasureTheory
open scoped BigOperators ComplexConjugate

theorem natCOMRelativeColumn_particle (z : Fin 9) (a : Fin (natCOMRelativeDimension z)) :
    (natCOMRelativeColumn z a).IsHomogeneous 3 := by
  fin_cases z
  · exact (k300_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k301_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k302_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k303_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k304_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k305_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k306_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k307_nat_relative_bihomogeneous (Pi.single a 1)).1
  · exact (k308_nat_relative_bihomogeneous (Pi.single a 1)).1

theorem natCOMRelativeColumn_vacuum (z : Fin 9) (a : Fin (natCOMRelativeDimension z)) :
    canonicalCOMLowerNat (natCOMRelativeColumn z a)=0 := by
  fin_cases z
  · exact k300_nat_relative_vacuum (Pi.single a 1)
  · exact k301_nat_relative_vacuum (Pi.single a 1)
  · exact k302_nat_relative_vacuum (Pi.single a 1)
  · exact k303_nat_relative_vacuum (Pi.single a 1)
  · exact k304_nat_relative_vacuum (Pi.single a 1)
  · exact k305_nat_relative_vacuum (Pi.single a 1)
  · exact k306_nat_relative_vacuum (Pi.single a 1)
  · exact k307_nat_relative_vacuum (Pi.single a 1)
  · exact k308_nat_relative_vacuum (Pi.single a 1)

theorem k300_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k300COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k300COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k300COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k300COMLevel i=k300COMLevel j then
      (3^(k300COMLevel i)*((k300COMLevel i).factorial:ℂ))*k300COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k300COMRelativeDegree i) (k300COMIndexLabel i).2) (natCOMRelativeColumn_particle (k300COMRelativeDegree i) (k300COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k300COMRelativeDegree j) (k300COMIndexLabel j).2) (natCOMRelativeColumn_particle (k300COMRelativeDegree j) (k300COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k300_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k300COMRelativeDegree i) (k300COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k300COMRelativeDegree i) (k300COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k300COMRelativeDegree i) (k300COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k300COMRelativeDegree i) (k300COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k300COMRelativeDegree i) (k300COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k300COMRelativeDegree i) (k300COMIndexLabel i).2)
      k300COMLevel k300COMLevel k300COMRankCoefficient f g

theorem k301_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k301COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k301COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k301COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k301COMLevel i=k301COMLevel j then
      (3^(k301COMLevel i)*((k301COMLevel i).factorial:ℂ))*k301COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k301COMRelativeDegree i) (k301COMIndexLabel i).2) (natCOMRelativeColumn_particle (k301COMRelativeDegree i) (k301COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k301COMRelativeDegree j) (k301COMIndexLabel j).2) (natCOMRelativeColumn_particle (k301COMRelativeDegree j) (k301COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k301_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k301COMRelativeDegree i) (k301COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k301COMRelativeDegree i) (k301COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k301COMRelativeDegree i) (k301COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k301COMRelativeDegree i) (k301COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k301COMRelativeDegree i) (k301COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k301COMRelativeDegree i) (k301COMIndexLabel i).2)
      k301COMLevel k301COMLevel k301COMRankCoefficient f g

theorem k302_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k302COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k302COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k302COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k302COMLevel i=k302COMLevel j then
      (3^(k302COMLevel i)*((k302COMLevel i).factorial:ℂ))*k302COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k302COMRelativeDegree i) (k302COMIndexLabel i).2) (natCOMRelativeColumn_particle (k302COMRelativeDegree i) (k302COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k302COMRelativeDegree j) (k302COMIndexLabel j).2) (natCOMRelativeColumn_particle (k302COMRelativeDegree j) (k302COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k302_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k302COMRelativeDegree i) (k302COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k302COMRelativeDegree i) (k302COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k302COMRelativeDegree i) (k302COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k302COMRelativeDegree i) (k302COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k302COMRelativeDegree i) (k302COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k302COMRelativeDegree i) (k302COMIndexLabel i).2)
      k302COMLevel k302COMLevel k302COMRankCoefficient f g

theorem k303_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k303COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k303COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k303COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k303COMLevel i=k303COMLevel j then
      (3^(k303COMLevel i)*((k303COMLevel i).factorial:ℂ))*k303COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k303COMRelativeDegree i) (k303COMIndexLabel i).2) (natCOMRelativeColumn_particle (k303COMRelativeDegree i) (k303COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k303COMRelativeDegree j) (k303COMIndexLabel j).2) (natCOMRelativeColumn_particle (k303COMRelativeDegree j) (k303COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k303_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k303COMRelativeDegree i) (k303COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k303COMRelativeDegree i) (k303COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k303COMRelativeDegree i) (k303COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k303COMRelativeDegree i) (k303COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k303COMRelativeDegree i) (k303COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k303COMRelativeDegree i) (k303COMIndexLabel i).2)
      k303COMLevel k303COMLevel k303COMRankCoefficient f g

theorem k304_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k304COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k304COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k304COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k304COMLevel i=k304COMLevel j then
      (3^(k304COMLevel i)*((k304COMLevel i).factorial:ℂ))*k304COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k304COMRelativeDegree i) (k304COMIndexLabel i).2) (natCOMRelativeColumn_particle (k304COMRelativeDegree i) (k304COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k304COMRelativeDegree j) (k304COMIndexLabel j).2) (natCOMRelativeColumn_particle (k304COMRelativeDegree j) (k304COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k304_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k304COMRelativeDegree i) (k304COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k304COMRelativeDegree i) (k304COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k304COMRelativeDegree i) (k304COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k304COMRelativeDegree i) (k304COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k304COMRelativeDegree i) (k304COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k304COMRelativeDegree i) (k304COMIndexLabel i).2)
      k304COMLevel k304COMLevel k304COMRankCoefficient f g

theorem k305_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k305COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k305COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k305COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k305COMLevel i=k305COMLevel j then
      (3^(k305COMLevel i)*((k305COMLevel i).factorial:ℂ))*k305COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k305COMRelativeDegree i) (k305COMIndexLabel i).2) (natCOMRelativeColumn_particle (k305COMRelativeDegree i) (k305COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k305COMRelativeDegree j) (k305COMIndexLabel j).2) (natCOMRelativeColumn_particle (k305COMRelativeDegree j) (k305COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k305_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k305COMRelativeDegree i) (k305COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k305COMRelativeDegree i) (k305COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k305COMRelativeDegree i) (k305COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k305COMRelativeDegree i) (k305COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k305COMRelativeDegree i) (k305COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k305COMRelativeDegree i) (k305COMIndexLabel i).2)
      k305COMLevel k305COMLevel k305COMRankCoefficient f g

theorem k306_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k306COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k306COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k306COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k306COMLevel i=k306COMLevel j then
      (3^(k306COMLevel i)*((k306COMLevel i).factorial:ℂ))*k306COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k306COMRelativeDegree i) (k306COMIndexLabel i).2) (natCOMRelativeColumn_particle (k306COMRelativeDegree i) (k306COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k306COMRelativeDegree j) (k306COMIndexLabel j).2) (natCOMRelativeColumn_particle (k306COMRelativeDegree j) (k306COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k306_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k306COMRelativeDegree i) (k306COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k306COMRelativeDegree i) (k306COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k306COMRelativeDegree i) (k306COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k306COMRelativeDegree i) (k306COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k306COMRelativeDegree i) (k306COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k306COMRelativeDegree i) (k306COMIndexLabel i).2)
      k306COMLevel k306COMLevel k306COMRankCoefficient f g

theorem k307_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k307COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k307COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k307COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k307COMLevel i=k307COMLevel j then
      (3^(k307COMLevel i)*((k307COMLevel i).factorial:ℂ))*k307COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k307COMRelativeDegree i) (k307COMIndexLabel i).2) (natCOMRelativeColumn_particle (k307COMRelativeDegree i) (k307COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k307COMRelativeDegree j) (k307COMIndexLabel j).2) (natCOMRelativeColumn_particle (k307COMRelativeDegree j) (k307COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k307_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k307COMRelativeDegree i) (k307COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k307COMRelativeDegree i) (k307COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k307COMRelativeDegree i) (k307COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k307COMRelativeDegree i) (k307COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k307COMRelativeDegree i) (k307COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k307COMRelativeDegree i) (k307COMIndexLabel i).2)
      k307COMLevel k307COMLevel k307COMRankCoefficient f g

theorem k308_actual_COM_cell_trace (G : Geometry) (theta : Twist)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ i, ∑ j, k308COMRankCoefficient i j *
      ip (natThreeAnnihilator G theta R (k308COMDescendantFamily i) f)
        (natThreeAnnihilator G theta R (k308COMDescendantFamily j) g)
      ∂cellMeasure G 2) =
    (2/3:ℂ) * ∑ i, ∑ j, if k308COMLevel i=k308COMLevel j then
      (3^(k308COMLevel i)*((k308COMLevel i).factorial:ℂ))*k308COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k308COMRelativeDegree i) (k308COMIndexLabel i).2) (natCOMRelativeColumn_particle (k308COMRelativeDegree i) (k308COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k308COMRelativeDegree j) (k308COMIndexLabel j).2) (natCOMRelativeColumn_particle (k308COMRelativeDegree j) (k308COMIndexLabel j).2) 0 R g) ∂cellMeasure G 3)
      else 0 := by
  simpa only [k308_COMDescendantFamily_labelled] using
    finite_unnormalized_COM_matrix_trace G theta Finset.univ Finset.univ
      (fun i => (natCOMRelativeColumn (k308COMRelativeDegree i) (k308COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn (k308COMRelativeDegree i) (k308COMIndexLabel i).2))
      (fun i => (natCOMRelativeColumn_particle (k308COMRelativeDegree i) (k308COMIndexLabel i).2)) (fun i => (natCOMRelativeColumn_particle (k308COMRelativeDegree i) (k308COMIndexLabel i).2))
      (fun i => natCOMRelativeColumn_vacuum (k308COMRelativeDegree i) (k308COMIndexLabel i).2)
      (fun i => natCOMRelativeColumn_vacuum (k308COMRelativeDegree i) (k308COMIndexLabel i).2)
      k308COMLevel k308COMLevel k308COMRankCoefficient f g

end TorusLean.Shared.BosonNatThreeCOMCellTrace
