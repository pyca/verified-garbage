module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto -- shake: keep (exports the baseline CTR entry points)

/-! # Baseline POWER8 AES CTR entry points, in place and out of place -/

@[expose] public section
namespace VG.Impl.Aes.PPC64LE
export Crypto (ctr32 ctr32To)
end VG.Impl.Aes.PPC64LE
