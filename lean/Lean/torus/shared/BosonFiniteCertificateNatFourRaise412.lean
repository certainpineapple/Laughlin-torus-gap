import Mathlib.Data.List.Sort
import torus.shared.BosonFiniteCertificateNatFourExpandedWords
import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourRationalWords
import torus.shared.BosonFiniteCertificateNatFourBasis412
import torus.shared.BosonFiniteCertificateNatFourBasis413
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! True Nat COM raising from degree 12 to degree 13.
The target rectangular matrix is checked on the actual rational word action
before the invertible factorial substitution transports it to the source. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open Matrix
open scoped BigOperators

def f412raise : Matrix (Fin 39) (Fin 34) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4]

def f412raiseNat : Matrix (Fin 39) (Fin 34) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4]

private theorem f412_raise_nat_cast : ∀ b a, (f412raiseNat b a : ℚ)=f412raise b a := by
  intro b a
  fin_cases b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 0 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 0 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 1 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 1 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 2 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 2 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 3 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 3 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 4 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 4 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 5 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 5 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 6 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 6 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 7 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 7 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 8 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 8 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 9 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 9 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 10 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 10 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 11 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 11 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 12 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 12 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 13 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 13 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 14 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 14 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 15 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 15 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 16 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 16 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 17 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 17 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 18 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 18 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 19 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 19 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 20 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 20 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 21 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 21 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 22 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 22 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 23 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 23 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 24 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 24 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 25 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 25 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 26 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 26 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 27 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 27 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 28 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 28 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 29 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 29 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 30 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 30 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 31 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 31 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 32 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 32 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 33 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 33 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 34 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 34 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 35 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 35 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 36 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 36 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 37 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 37 a)
      (by decide +kernel) 0 a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (a : Fin 34) => (f412raiseNat 38 a : ℚ))
      (fun (_ : Fin 1) (a : Fin 34) => f412raise 38 a)
      (by decide +kernel) 0 a

#print axioms f412_raise_nat_cast

theorem f412_rational_raise_check : ∀ a : Fin 34,
    natFourRationalRaiseWord (f412basis a) =
      ∑ b : Fin 39, f412raise b a • (wordPolynomial (f413basis b) : Core ℕ ℚ) := by
  have hc : ∀ b a, (f412raiseNat b a : ℚ)=f412raise b a :=
    f412_raise_nat_cast
  have hp : ∀ a : Fin 34, (natFourExpandedWords ((raisedWordsNat (f412basis a)).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (f412raiseNat b a,f413basis b))) := by
    intro a
    simp only [natFourExpandedWords,natFourSortedWord,List.mergeSort_eq_insertionSort]
    fin_cases a <;> decide +kernel
  intro a
  simpa only [hc] using natFour_raise_rational_of_expanded_perm
    (f412basis a) f413basis (fun b => f412raiseNat b a) (hp a)

theorem f412_actual_raise_word (a : Fin 34) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat (f412basis a)) =
      ∑ b : Fin 39, (f412raise b a : ℂ) • scaledWord factorialRootNat (f413basis b) :=
  natFour_raise_action_of_rational_check (f412basis a) f413basis
    (fun b => f412raise b a) (f412_rational_raise_check a)

theorem f412_actual_raise_block (v : Fin 34 → ℂ) :
    canonicalCOMRaiseNat (natFourWordBlock f412basis v) =
      natFourWordBlock f413basis (complexify f412raise *ᵥ v) :=
  natFourWordBlock_rect_action f412basis f413basis canonicalCOMRaiseNat
    (complexify f412raise) f412_actual_raise_word v

#print axioms f412_rational_raise_check
#print axioms f412_actual_raise_word
#print axioms f412_actual_raise_block
end TorusLean.BosonFiniteCertificate
