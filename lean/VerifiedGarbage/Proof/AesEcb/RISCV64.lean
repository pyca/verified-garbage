module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.RISCV64
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-!
# AES-ECB on RISC-V

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` call `vg_aes_encrypt_blocks`
and `vg_aes_decrypt_blocks`, which write `scratch`, by `callWipe`, which then
zeroes the whole of `scratch` with `vg_zeroize`.
-/

@[expose] public section

namespace VG.Proof.AesEcb.RISCV64

open VG VG.RISCV64

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2048 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.RISCV64.callWipe .a4 2048 name body "vg_zeroize" Impl.Zeroize.RISCV64.zeroize

/-- `vg_aes_ecb_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_encrypt_blocks" Impl.Aes.RISCV64.encryptBlocks

/-- `vg_aes_ecb_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_decrypt_blocks" Impl.Aes.RISCV64.decryptBlocks

theorem sat (g : List Byte → Spec.Aes.State → Spec.Aes.State) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g) false 32 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, RISCV64.abi, RISCV64.argRegs] [Proof.Aes.RISCV64.blocksSat]
    using Proof.Aes.RISCV64.blocksSat

theorem wiped_verified {g : List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 g) false 0 none))
    (hd : body.noFrames = true) :
    Verified target (wiped name body) (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64)
    (k := 256) (n := 2048) (i := 4) h Proof.Zeroize.RISCV64.verified (by decide) rfl rfl rfl
    (by decide) (by decide) (by rw [sdepth_of_noFrames hd])
    (by rw [sdepth_of_noFrames (by decide)]) (Nat.zero_le _)
    (pre_local 64) (post_local 64 g) (post_out 64 g) (AesEcb.wiped 64 g) (sat g)

theorem encrypt_verified : Verified target encrypt (Spec.AesEcb.encryptContract abi 32) :=
  wiped_verified (Proof.Aes.encryptBlocks_keyed Proof.Aes.RISCV64.encryptBlocks_verified) (by lit_decide)

theorem decrypt_verified : Verified target decrypt (Spec.AesEcb.decryptContract abi 32) :=
  wiped_verified (Proof.Aes.decryptBlocks_keyed Proof.Aes.RISCV64.decryptBlocks_verified) (by lit_decide)

end VG.Proof.AesEcb.RISCV64
