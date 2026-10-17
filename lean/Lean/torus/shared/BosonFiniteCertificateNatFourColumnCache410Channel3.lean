import torus.shared.BosonFiniteCertificateNatFourColumnCache410Data

/-! One complete original signed column-Gram channel, checked directly
against all original integer rows and exact original active pair positions. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f410_source_gram_cache_channel3 :
    f410sourceGramCache 3=natFourOriginalColumnCache 3 (f410activePairs 3) := by
  decide +kernel

#print axioms f410_source_gram_cache_channel3
end TorusLean.BosonFiniteCertificate
