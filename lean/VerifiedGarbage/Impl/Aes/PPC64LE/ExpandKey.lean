module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto.ExpandKey -- shake: keep (exports the baseline key-expansion entry point)

/-! # Baseline POWER8 AES key-expansion entry point -/

@[expose] public section
namespace VG.Impl.Aes.PPC64LE
export Crypto (expandKey)
end VG.Impl.Aes.PPC64LE
