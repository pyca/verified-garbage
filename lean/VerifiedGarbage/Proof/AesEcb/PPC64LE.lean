module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Impl.AesEcb.PPC64LE
public import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.Zeroize.PPC64LE
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-ECB on PPC64LE

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` (`Impl/AesEcb/PPC64LE.lean`)
call `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, then zero the
whole of `scratch` (2048 bytes, which the blocks functions' proofs do not
bound) with `vg_zeroize`: `Verified.callWipe'`, with the side conditions of
`Proof/AesEcb/Wipe.lean`.
-/

@[expose] public section

namespace VG.Proof.AesEcb.PPC64LE

open VG VG.PPC64LE

theorem encrypt_verified : Verified PPC64LE.target Impl.AesEcb.PPC64LE.encrypt (Spec.AesEcb.encryptContract PPC64LE.abi 48) :=
  Verified.callWipe' (sig := Spec.Aes.blocksSig) (stack := 0) (zst := 0)
    (pre := pre 64) (post := post 64 enc) (post' := ecbPost 64 enc)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 4)
    (Proof.Aes.encryptBlocks_keyed Proof.Aes.PPC64LE.encryptBlocks_verified) Proof.Zeroize.PPC64LE.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (pre_local 64) (post_local 64 _) (post_out 64 _) (AesEcb.wiped 64 _)
    (by implies_sat [Spec.Aes.blocksSig, PPC64LE.abi, PPC64LE.argRegs, pre] [Proof.Aes.PPC64LE.blocksSat]
      using Proof.Aes.PPC64LE.blocksSat)

theorem decrypt_verified : Verified PPC64LE.target Impl.AesEcb.PPC64LE.decrypt (Spec.AesEcb.decryptContract PPC64LE.abi 48) :=
  Verified.callWipe' (sig := Spec.Aes.blocksSig) (stack := 0) (zst := 0)
    (pre := pre 64) (post := post 64 dec) (post' := ecbPost 64 dec)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 4)
    (Proof.Aes.decryptBlocks_keyed Proof.Aes.PPC64LE.decryptBlocks_verified) Proof.Zeroize.PPC64LE.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (pre_local 64) (post_local 64 _) (post_out 64 _) (AesEcb.wiped 64 _)
    (by implies_sat [Spec.Aes.blocksSig, PPC64LE.abi, PPC64LE.argRegs, pre] [Proof.Aes.PPC64LE.blocksSat]
      using Proof.Aes.PPC64LE.blocksSat)

end VG.Proof.AesEcb.PPC64LE
