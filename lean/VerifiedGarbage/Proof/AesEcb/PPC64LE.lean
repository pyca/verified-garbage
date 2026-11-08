module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# AES-ECB on PPC64LE

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` are the code of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, which write nothing in
`scratch` (`Proof.Aes.PPC64LE.encryptBlocks_written`), so that it needs no
wipe: `Verified.ecb_of_unwritten`.
-/

@[expose] public section

namespace VG.Proof.AesEcb.PPC64LE

open VG VG.PPC64LE

theorem args_length : ∀ s vals,
    PPC64LE.abi.args ((Spec.Aes.blocksSig.words PPC64LE.abi.ptrBits).map (·.bits PPC64LE.abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Aes.blocksSig.words PPC64LE.abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : PPC64LE.abi.args _ = some (regArgs Spec.Aes.blocksSig)))
  exact regArgs_length Spec.Aes.blocksSig s (by decide)

theorem encrypt_verified :
    Verified PPC64LE.target Impl.Aes.PPC64LE.encryptBlocks (Spec.AesEcb.encryptContract PPC64LE.abi) :=
  Verified.ecb_of_unwritten (Proof.Aes.encryptBlocks_keyed Proof.Aes.PPC64LE.encryptBlocks_verified)
    Proof.Aes.PPC64LE.encryptBlocks_written args_length

theorem decrypt_verified :
    Verified PPC64LE.target Impl.Aes.PPC64LE.decryptBlocks (Spec.AesEcb.decryptContract PPC64LE.abi) :=
  Verified.ecb_of_unwritten (Proof.Aes.decryptBlocks_keyed Proof.Aes.PPC64LE.decryptBlocks_verified)
    Proof.Aes.PPC64LE.decryptBlocks_written args_length

end VG.Proof.AesEcb.PPC64LE
