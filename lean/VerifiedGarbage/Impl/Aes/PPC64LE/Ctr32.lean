module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto -- shake: keep (exports the baseline CTR entry point)

/-! # Baseline POWER8 AES CTR entry point -/

@[expose] public section
namespace VG.Impl.Aes.PPC64LE
export Crypto (ctr32)
end VG.Impl.Aes.PPC64LE
