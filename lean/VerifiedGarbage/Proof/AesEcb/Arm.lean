module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.Arm.Blocks
public import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
public import VerifiedGarbage.Proof.Zeroize.Arm

/-!
# AES-ECB on ARMv7

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` call `vg_aes_encrypt_blocks`
and `vg_aes_decrypt_blocks`, which write `scratch` (their fifth argument,
the word on the stack), by `callWipeStack`, which copies that word into its
frame for the call, then zeroes the whole of `scratch` (2048 bytes, which
the blocks functions' proofs do not bound) with `vg_zeroize`, with 24 bytes
of stack.
-/

@[expose] public section

namespace VG.Proof.AesEcb.Arm

open VG VG.Arm VG.Arm.FrameStack

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2048 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.ArmStack.callWipeStack 1 0 2048 name body "vg_zeroize" Impl.Zeroize.Arm.zeroize

/-- `vg_aes_ecb_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_encrypt_blocks" Impl.Aes.Arm.encryptBlocks

/-- `vg_aes_ecb_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_decrypt_blocks" Impl.Aes.Arm.decryptBlocks

theorem sat (g : List Byte → Spec.Aes.State → Spec.Aes.State) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 32) (ecbPost 32 g) false 24 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, Arm.abi] [Proof.Aes.Arm.Ecb.sat] using Proof.Aes.Arm.Ecb.sat

theorem wiped_verified {g : List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Aes.blocksSig.contract abi (pre 32) (post 32 g) false 0 none))
    (hd : armStack body = 0) :
    Verified target (wiped name body) (Spec.Aes.blocksSig.contract abi (pre 32) (ecbPost 32 g) false 24 none) :=
  Verified.callWipeStack' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64)
    (kk := 256) (n := 2048) (i := 4) (k := 1) (off := 0) h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by rw [hd]) (by decide) (Nat.zero_le _)
    (pre_local 32) (post_local 32 g) (post_out 32 g) (AesEcb.wiped 32 g) (sat g)

theorem encrypt_verified : Verified target encrypt (Spec.AesEcb.encryptContract abi 24) :=
  wiped_verified (Proof.Aes.encryptBlocks_keyed Proof.Aes.Arm.Ecb.encryptBlocks_verified) (by decide)

theorem decrypt_verified : Verified target decrypt (Spec.AesEcb.decryptContract abi 24) :=
  wiped_verified (Proof.Aes.decryptBlocks_keyed Proof.Aes.Arm.Ecb.decryptBlocks_verified) (by decide)

end VG.Proof.AesEcb.Arm
