import torus.shared.BosonFiniteCertificateNatFourCOMRelativeFamilyData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFourRelativeColumn_gram (d : Fin 17) :
    natFamilyGram (natFourRelativeColumn d)=complexify (natFourRelativeGram d) := by
  fin_cases d
  · exact f400_actual_relative_gram
  · exact f401_actual_relative_gram
  · exact f402_actual_relative_gram
  · exact f403_actual_relative_gram
  · exact f404_actual_relative_gram
  · exact f405_actual_relative_gram
  · exact f406_actual_relative_gram
  · exact f407_actual_relative_gram
  · exact f408_actual_relative_gram
  · exact f409_actual_relative_gram
  · exact f410_actual_relative_gram
  · exact f411_actual_relative_gram
  · exact f412_actual_relative_gram
  · exact f413_actual_relative_gram
  · exact f414_actual_relative_gram
  · exact f415_actual_relative_gram
  · exact f416_actual_relative_gram

theorem natFourRelativeGram_inverse_left (d : Fin 17) :
    natFourRelativeGramInverse d*natFourRelativeGram d=1 := by
  fin_cases d
  · exact f400_relative_gram_inverse_left
  · exact f401_relative_gram_inverse_left
  · exact f402_relative_gram_inverse_left
  · exact f403_relative_gram_inverse_left
  · exact f404_relative_gram_inverse_left
  · exact f405_relative_gram_inverse_left
  · exact f406_relative_gram_inverse_left
  · exact f407_relative_gram_inverse_left
  · exact f408_relative_gram_inverse_left
  · exact f409_relative_gram_inverse_left
  · exact f410_relative_gram_inverse_left
  · exact f411_relative_gram_inverse_left
  · exact f412_relative_gram_inverse_left
  · exact f413_relative_gram_inverse_left
  · exact f414_relative_gram_inverse_left
  · exact f415_relative_gram_inverse_left
  · exact f416_relative_gram_inverse_left

theorem natFourRelativeGram_inverse_right (d : Fin 17) :
    natFourRelativeGram d*natFourRelativeGramInverse d=1 := by
  fin_cases d
  · exact f400_relative_gram_inverse_right
  · exact f401_relative_gram_inverse_right
  · exact f402_relative_gram_inverse_right
  · exact f403_relative_gram_inverse_right
  · exact f404_relative_gram_inverse_right
  · exact f405_relative_gram_inverse_right
  · exact f406_relative_gram_inverse_right
  · exact f407_relative_gram_inverse_right
  · exact f408_relative_gram_inverse_right
  · exact f409_relative_gram_inverse_right
  · exact f410_relative_gram_inverse_right
  · exact f411_relative_gram_inverse_right
  · exact f412_relative_gram_inverse_right
  · exact f413_relative_gram_inverse_right
  · exact f414_relative_gram_inverse_right
  · exact f415_relative_gram_inverse_right
  · exact f416_relative_gram_inverse_right

theorem natFourRelativeGramInverse_symmetric (d : Fin 17) :
    (natFourRelativeGramInverse d)ᵀ=natFourRelativeGramInverse d := by
  fin_cases d
  · exact f400_relative_gram_inverse_symmetric
  · exact f401_relative_gram_inverse_symmetric
  · exact f402_relative_gram_inverse_symmetric
  · exact f403_relative_gram_inverse_symmetric
  · exact f404_relative_gram_inverse_symmetric
  · exact f405_relative_gram_inverse_symmetric
  · exact f406_relative_gram_inverse_symmetric
  · exact f407_relative_gram_inverse_symmetric
  · exact f408_relative_gram_inverse_symmetric
  · exact f409_relative_gram_inverse_symmetric
  · exact f410_relative_gram_inverse_symmetric
  · exact f411_relative_gram_inverse_symmetric
  · exact f412_relative_gram_inverse_symmetric
  · exact f413_relative_gram_inverse_symmetric
  · exact f414_relative_gram_inverse_symmetric
  · exact f415_relative_gram_inverse_symmetric
  · exact f416_relative_gram_inverse_symmetric

#print axioms natFourRelativeColumn_gram
#print axioms natFourRelativeGram_inverse_left
#print axioms natFourRelativeGram_inverse_right
#print axioms natFourRelativeGramInverse_symmetric
end TorusLean.BosonFiniteCertificate
