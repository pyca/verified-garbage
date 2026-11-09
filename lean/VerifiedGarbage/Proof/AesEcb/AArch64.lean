module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.Framework.AArch64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-!
# AES-ECB on AArch64

For each implementation of the blocks functions (`BlocksImpl`): where it
writes nothing in `scratch` (`BlocksImpl.free`), `vg_aes_ecb_encrypt` and
`vg_aes_ecb_decrypt` are its code (`encrypt_free`, `decrypt_free`);
otherwise a call of it by `callWipe`, which then zeroes the whole of
`scratch` with `vg_zeroize` (`encrypt_verified`, `decrypt_verified`).
-/

@[expose] public section

namespace VG.Proof.AesEcb.AArch64

open VG VG.AArch64 VG.Proof.Aes.AArch64

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2048 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.AArch64.callWipe .x4 2048 name body "vg_zeroize" Impl.Zeroize.AArch64.zeroizeWide

/-- `vg_aes_ecb_encrypt` from `v`'s `vg_aes_encrypt_blocks`, wiping `scratch`. -/
def encrypt (v : BlocksImpl) : Prog isa := wiped v.enc.name v.enc.code

/-- `vg_aes_ecb_decrypt` from `v`'s `vg_aes_decrypt_blocks`, wiping `scratch`. -/
def decrypt (v : BlocksImpl) : Prog isa := wiped v.dec.name v.dec.code

theorem encBlocks (v : BlocksImpl) :
    Verified target v.enc.code (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 enc) false 0 none) :=
  Proof.Aes.encryptBlocks_keyed (Verified.of_correct v.encOk v.encCt Aese.encryptBlocks_implies)

theorem decBlocks (v : BlocksImpl) :
    Verified target v.dec.code (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 dec) false 0 none) :=
  Proof.Aes.decryptBlocks_keyed (Verified.of_correct v.decOk v.decCt Aese.decryptBlocks_implies)

theorem sat (g : List Byte → Spec.Aes.State → Spec.Aes.State) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g) false 32 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, AArch64.abi, AArch64.argRegs] [blocksSat] using blocksSat

theorem zeroize_depth : 16 * Impl.Zeroize.AArch64.zeroizeWide.aarch64Depth ≤ 0 := by
  rw [depth_of_noFrames (by decide)]

theorem wiped_verified {g : List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 g) false 0 none))
    (hd : body.noFrames = true) :
    Verified target (wiped name body) (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64)
    (k := 256) (n := 2048) (i := 4) h Proof.Zeroize.AArch64.wideVerified (by decide) rfl rfl rfl
    (by decide) (by decide) (by rw [depth_of_noFrames hd]) zeroize_depth (Nat.zero_le _)
    (pre_local 64) (post_local 64 g) (post_out 64 g) (AesEcb.wiped 64 g) (sat g)

theorem encrypt_verified (v : BlocksImpl) :
    Verified target (encrypt v) (Spec.AesEcb.encryptContract abi 32) :=
  wiped_verified (encBlocks v) v.encNoFrames

theorem decrypt_verified (v : BlocksImpl) :
    Verified target (decrypt v) (Spec.AesEcb.decryptContract abi 32) :=
  wiped_verified (decBlocks v) v.decNoFrames

theorem args_length : ∀ s vals,
    abi.args ((Spec.Aes.blocksSig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Aes.blocksSig.words abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : abi.args _ = some (regArgs Spec.Aes.blocksSig)))
  exact regArgs_length Spec.Aes.blocksSig s (by decide)

theorem encrypt_free (v : BlocksImpl) (h : v.free = true) :
    Verified target v.enc.code (Spec.AesEcb.encryptContract abi) :=
  Verified.ecb_of_unwritten (encBlocks v) (v.encFree h) args_length

theorem decrypt_free (v : BlocksImpl) (h : v.free = true) :
    Verified target v.dec.code (Spec.AesEcb.decryptContract abi) :=
  Verified.ecb_of_unwritten (decBlocks v) (v.decFree h) args_length

end VG.Proof.AesEcb.AArch64
