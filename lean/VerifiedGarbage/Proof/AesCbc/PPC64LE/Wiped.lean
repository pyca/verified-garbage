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
proofs do not bound) with `vg_zeroize`: `Verified.callWipe`, with the side
conditions of `Proof/AesCbc/Wipe.lean`.
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE.Wiped

open VG VG.PPC64LE VG.Proof.AesCbc.Wipe

theorem encrypt_verified :
    Verified PPC64LE.target Impl.AesCbc.PPC64LE.Wiped.encrypt (Spec.Cbc.aesEncryptContract PPC64LE.abi 48) :=
  Verified.callWipe (sig := Spec.Cbc.aesSig) (stack := 0) (zst := 0) (pre := cbcPre 64) (post := encPost 64)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5)
    (Proof.AesCbc.encrypt_keyed Proof.AesCbc.PPC64LE.encrypt_verified) Proof.Zeroize.PPC64LE.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (pre_local 64) (encPost_local 64) (encPost_out 64)
    (by implies_sat [Spec.Cbc.aesSig, PPC64LE.abi, PPC64LE.argRegs, cbcPre] [Proof.AesCbc.PPC64LE.sat]
      using Proof.AesCbc.PPC64LE.sat)

theorem decrypt_verified :
    Verified PPC64LE.target Impl.AesCbc.PPC64LE.Wiped.decrypt (Spec.Cbc.aesDecryptContract PPC64LE.abi 48) :=
  Verified.callWipe (sig := Spec.Cbc.aesSig) (stack := 0) (zst := 0) (pre := cbcPre 64) (post := decPost 64)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5)
    (Proof.AesCbc.decrypt_keyed Proof.AesCbc.PPC64LE.decrypt_verified) Proof.Zeroize.PPC64LE.verified
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (pre_local 64) (decPost_local 64) (decPost_out 64)
    (by implies_sat [Spec.Cbc.aesSig, PPC64LE.abi, PPC64LE.argRegs, cbcPre] [Proof.AesCbc.PPC64LE.sat]
      using Proof.AesCbc.PPC64LE.sat)

end VG.Proof.AesCbc.PPC64LE.Wiped
