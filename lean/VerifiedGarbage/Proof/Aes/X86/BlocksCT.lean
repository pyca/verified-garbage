import VerifiedGarbage.Proof.Aes.X86.Blocks
import VerifiedGarbage.Spec.Aes.Contract

/-!
# AES on whole blocks on x86 (32-bit): constant time, and `Verified`

The taint analysis (`VG.X86.Taint`) starts with `esp` public and knows
where the arguments are and which of them are the base addresses of the
data and the scratch buffer. As in `vg_aes_ctr32` (`Ctr32CT.lean`), the data
pointer and the count round-trip through public slots of the scratch
buffer; the stores of the blocks through the data pointer forget them, and
the code stores them again from the registers.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub Impl.Aes.X86.encryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub Impl.Aes.X86.decryptBlocks :=
  VG.Taint.constantTime (A := VG.X86.taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem encryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.encryptBlocks (Spec.Aes.encryptBlocksContract X86.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.decryptBlocks (Spec.Aes.decryptBlocksContract X86.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

end VG.Proof.Aes.X86
