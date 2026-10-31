module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto -- shake: keep (exports the baseline block entry points)

/-! # Baseline POWER8 AES block entry points -/

@[expose] public section
namespace VG.Impl.Aes.PPC64LE
export Crypto (encryptBlocks decryptBlocks)
end VG.Impl.Aes.PPC64LE
