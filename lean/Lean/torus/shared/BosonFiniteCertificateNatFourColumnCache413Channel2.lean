import torus.shared.BosonFiniteCertificateNatFourColumnCache413Data

/-! One complete original signed column-Gram channel, checked directly
against all original integer rows and exact original active pair positions. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate

theorem f413_source_gram_cache_channel2 :
    f413sourceGramCache 2=natFourOriginalColumnCache 2 (f413activePairs 2) := by
  decide +kernel

#print axioms f413_source_gram_cache_channel2
end TorusLean.BosonFiniteCertificate
