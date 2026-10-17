import torus.shared.FermionLocalJetFourCouplingFiniteComparisonCore
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck01
import FermionBlocks.Block01
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck02
import FermionBlocks.Block02
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck03
import FermionBlocks.Block03
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck04
import FermionBlocks.Block04
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck05
import FermionBlocks.Block05
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck06
import FermionBlocks.Block06
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck07
import FermionBlocks.Block07
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck08
import FermionBlocks.Block08
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck09
import FermionBlocks.Block09
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck10
import FermionBlocks.Block10
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck11
import FermionBlocks.Block11
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck12
import FermionBlocks.Block12
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck13
import FermionBlocks.Block13
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck14
import FermionBlocks.Block14
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck15
import FermionBlocks.Block15
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck16
import FermionBlocks.Block16
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck17
import FermionBlocks.Block17
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck18
import FermionBlocks.Block18
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck19
import FermionBlocks.Block19
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck20
import FermionBlocks.Block20
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck21
import FermionBlocks.Block21
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck22
import FermionBlocks.Block22
import torus.shared.FermionLocalJetFourCouplingSlaterGramTableCheck23
import FermionBlocks.Block23

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

/-- All 23 actual Gram and PSD blocks are consumed; only the 23 exact Y-literal
identities are explicit premises for this reusable transport lemma. -/
theorem original_four_comparison_certificate_of_error_literals
    (h01 : integerFourErrorMatrix 1 = TorusLean.FermionM3.errorTable01)
    (h02 : integerFourErrorMatrix 2 = TorusLean.FermionM3.errorTable02)
    (h03 : integerFourErrorMatrix 3 = TorusLean.FermionM3.errorTable03)
    (h04 : integerFourErrorMatrix 4 = TorusLean.FermionM3.errorTable04)
    (h05 : integerFourErrorMatrix 5 = TorusLean.FermionM3.errorTable05)
    (h06 : integerFourErrorMatrix 6 = TorusLean.FermionM3.errorTable06)
    (h07 : integerFourErrorMatrix 7 = TorusLean.FermionM3.errorTable07)
    (h08 : integerFourErrorMatrix 8 = TorusLean.FermionM3.errorTable08)
    (h09 : integerFourErrorMatrix 9 = TorusLean.FermionM3.errorTable09)
    (h10 : integerFourErrorMatrix 10 = TorusLean.FermionM3.errorTable10)
    (h11 : integerFourErrorMatrix 11 = TorusLean.FermionM3.errorTable11)
    (h12 : integerFourErrorMatrix 12 = TorusLean.FermionM3.errorTable12)
    (h13 : integerFourErrorMatrix 13 = TorusLean.FermionM3.errorTable13)
    (h14 : integerFourErrorMatrix 14 = TorusLean.FermionM3.errorTable14)
    (h15 : integerFourErrorMatrix 15 = TorusLean.FermionM3.errorTable15)
    (h16 : integerFourErrorMatrix 16 = TorusLean.FermionM3.errorTable16)
    (h17 : integerFourErrorMatrix 17 = TorusLean.FermionM3.errorTable17)
    (h18 : integerFourErrorMatrix 18 = TorusLean.FermionM3.errorTable18)
    (h19 : integerFourErrorMatrix 19 = TorusLean.FermionM3.errorTable19)
    (h20 : integerFourErrorMatrix 20 = TorusLean.FermionM3.errorTable20)
    (h21 : integerFourErrorMatrix 21 = TorusLean.FermionM3.errorTable21)
    (h22 : integerFourErrorMatrix 22 = TorusLean.FermionM3.errorTable22)
    (h23 : integerFourErrorMatrix 23 = TorusLean.FermionM3.errorTable23)
    (d : Fin 23) :
    (((originalSlaterMatrixFin (d.val+1))ᴴ*originalSlaterMatrixFin (d.val+1)) *
      fourComparisonFinMatrix (d.val+1) *
      ((originalSlaterMatrixFin (d.val+1))ᴴ*originalSlaterMatrixFin (d.val+1))).PosSemidef := by
  have hfinite : (TorusLean.M2.complexify
      (OAI.Laughlin.Certificate.MatrixCompute.compressed (d.val+1)
        (integerFourErrorMatrix (d.val+1))
        (OAI.Laughlin.Certificate.gramRational (d.val+1)))).PosSemidef := by
    fin_cases d
    · rw [h01,originalSlaterGramTableCheck01]
      exact TorusLean.FermionM3.reconstructedPositive01
    · rw [h02,originalSlaterGramTableCheck02]
      exact TorusLean.FermionM3.reconstructedPositive02
    · rw [h03,originalSlaterGramTableCheck03]
      exact TorusLean.FermionM3.reconstructedPositive03
    · rw [h04,originalSlaterGramTableCheck04]
      exact TorusLean.FermionM3.reconstructedPositive04
    · rw [h05,originalSlaterGramTableCheck05]
      exact TorusLean.FermionM3.reconstructedPositive05
    · rw [h06,originalSlaterGramTableCheck06]
      exact TorusLean.FermionM3.reconstructedPositive06
    · rw [h07,originalSlaterGramTableCheck07]
      exact TorusLean.FermionM3.reconstructedPositive07
    · rw [h08,originalSlaterGramTableCheck08]
      exact TorusLean.FermionM3.reconstructedPositive08
    · rw [h09,originalSlaterGramTableCheck09]
      exact TorusLean.FermionM3.reconstructedPositive09
    · rw [h10,originalSlaterGramTableCheck10]
      exact TorusLean.FermionM3.reconstructedPositive10
    · rw [h11,originalSlaterGramTableCheck11]
      exact TorusLean.FermionM3.reconstructedPositive11
    · rw [h12,originalSlaterGramTableCheck12]
      exact TorusLean.FermionM3.reconstructedPositive12
    · rw [h13,originalSlaterGramTableCheck13]
      exact TorusLean.FermionM3.reconstructedPositive13
    · rw [h14,originalSlaterGramTableCheck14]
      exact TorusLean.FermionM3.reconstructedPositive14
    · rw [h15,originalSlaterGramTableCheck15]
      exact TorusLean.FermionM3.reconstructedPositive15
    · rw [h16,originalSlaterGramTableCheck16]
      exact TorusLean.FermionM3.reconstructedPositive16
    · rw [h17,originalSlaterGramTableCheck17]
      exact TorusLean.FermionM3.reconstructedPositive17
    · rw [h18,originalSlaterGramTableCheck18]
      exact TorusLean.FermionM3.reconstructedPositive18
    · rw [h19,originalSlaterGramTableCheck19]
      exact TorusLean.FermionM3.reconstructedPositive19
    · rw [h20,originalSlaterGramTableCheck20]
      exact TorusLean.FermionM3.reconstructedPositive20
    · rw [h21,originalSlaterGramTableCheck21]
      exact TorusLean.FermionM3.reconstructedPositive21
    · rw [h22,originalSlaterGramTableCheck22]
      exact TorusLean.FermionM3.reconstructedPositive22
    · rw [h23,originalSlaterGramTableCheck23]
      exact TorusLean.FermionM3.reconstructedPositive23

  have hroot : (originalCopyRootDiagonal (d.val+1)).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact copyInverseRoot_star _ _
  rw [original_four_compression_identity]
  simpa only [hroot.eq] using
    hfinite.mul_mul_conjTranspose_same (originalCopyRootDiagonal (d.val+1))


#print axioms original_four_comparison_certificate_of_error_literals
end TorusLean.Shared.FermionLocalJet.FourCoupling
