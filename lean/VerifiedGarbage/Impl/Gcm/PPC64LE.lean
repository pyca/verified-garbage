module

-- shake: keep (exports the baseline POWER8 GHASH implementation)
public import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum

/-! # PPC64LE GHASH

POWER8 and later provide polynomial multiplication. The baseline uses
`vpmsumd`; no scalar fallback or feature dispatch is required.
-/

@[expose] public section
namespace VG.Impl.Gcm.PPC64LE
export Vpmsum (ghash)
end VG.Impl.Gcm.PPC64LE
