module

public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
public import VerifiedGarbage.Impl.AesCbc.PPC64LE.Wiped
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.Zeroize.PPC64LE
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-CBC on PPC64LE, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` (`Impl/AesCbc/PPC64LE/Wiped.lean`)
call the CBC code, then zero the whole of `scratch` (2176 bytes, which its
proofs do not bound) with `vg_zeroize`, leaving it scrubbed
(`encrypt_scrubbed`, `decrypt_scrubbed`: `Verified.callWipe'`, with the side
conditions of `Proof/AesCbc/Wipe.lean`). `encrypt_verified` and
`decrypt_verified` are those weakened to the contracts of `Spec/Cbc/`, which
do not state it yet.
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE.Wiped

open VG VG.PPC64LE VG.Proof.AesCbc.Wipe

theorem sat (P : Spec.Cbc.aesSig.Post 64) :
    ∃ s, (Spec.Cbc.aesSig.contract PPC64LE.abi (pre 64) P false 48 none).pre s := by
  implies_sat [Spec.Cbc.aesSig, PPC64LE.abi, PPC64LE.argRegs, pre] [Proof.AesCbc.PPC64LE.sat]
    using Proof.AesCbc.PPC64LE.sat

theorem encrypt_scrubbed :
    Verified PPC64LE.target Impl.AesCbc.PPC64LE.Wiped.encrypt
      (Spec.Cbc.aesSig.contract PPC64LE.abi (pre 64) (scrubbedPost 64 (encPost 64)) false 48 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5)
    (Proof.AesCbc.encrypt_keyed Proof.AesCbc.PPC64LE.encrypt_verified) Proof.Zeroize.PPC64LE.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (pre_local 64) (encPost_local 64) (encPost_out 64) (wiped 64 _) (sat _)

theorem decrypt_scrubbed :
    Verified PPC64LE.target Impl.AesCbc.PPC64LE.Wiped.decrypt
      (Spec.Cbc.aesSig.contract PPC64LE.abi (pre 64) (scrubbedPost 64 (decPost 64)) false 48 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5)
    (Proof.AesCbc.decrypt_keyed Proof.AesCbc.PPC64LE.decrypt_verified) Proof.Zeroize.PPC64LE.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (pre_local 64) (decPost_local 64) (decPost_out 64) (wiped 64 _) (sat _)

theorem encrypt_verified :
    Verified PPC64LE.target Impl.AesCbc.PPC64LE.Wiped.encrypt (Spec.Cbc.aesEncryptContract PPC64LE.abi 48) :=
  Verified.of_scrubbed encrypt_scrubbed

theorem decrypt_verified :
    Verified PPC64LE.target Impl.AesCbc.PPC64LE.Wiped.decrypt (Spec.Cbc.aesDecryptContract PPC64LE.abi 48) :=
  Verified.of_scrubbed decrypt_scrubbed

end VG.Proof.AesCbc.PPC64LE.Wiped
