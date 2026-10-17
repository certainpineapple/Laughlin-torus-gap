import torus.shared.BosonFiniteCertificateNatFourColumnCache408Data

/-! One complete original signed column-Gram channel, checked directly
against all original integer rows and exact original active pair positions. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f408_source_gram_cache_channel1 :
    f408sourceGramCache 1=natFourOriginalColumnCache 1 (f408activePairs 1) := by
  decide +kernel

#print axioms f408_source_gram_cache_channel1
end TorusLean.BosonFiniteCertificate
