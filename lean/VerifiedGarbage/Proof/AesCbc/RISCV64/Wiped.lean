module

public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.RISCV64
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit

/-!
# AES-CBC on RISC-V, zeroing the scratch it writes

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` call their code, as the
internal functions `vg_aes_cbc_{en,de}crypt_unwiped`, by `callWipe`, which
then zeroes the whole of `scratch` with `vg_zeroize`. Each meets its contract
and leaves each byte of `scratch` unchanged or zero (`*_scrubbed`, the
stronger contract the Spec will state once every target's implementations
prove it; the registration takes its weakening, `*_verified`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64.Wiped

open VG VG.RISCV64 VG.Proof.AesCbc.Wipe

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2176 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.RISCV64.callWipe 32 .a5 2176 name body "vg_zeroize" Impl.Zeroize.RISCV64.zeroize

/-- `vg_aes_cbc_encrypt`, wiping `scratch`. -/
def encrypt : Prog isa := wiped "vg_aes_cbc_encrypt_unwiped" Impl.AesCbc.RISCV64.encrypt

/-- `vg_aes_cbc_decrypt`, wiping `scratch`. -/
def decrypt : Prog isa := wiped "vg_aes_cbc_decrypt_unwiped" Impl.AesCbc.RISCV64.decrypt

theorem sat (P : Spec.Cbc.aesSig.Post 64) :
    ∃ s, (Spec.Cbc.aesSig.contract abi (pre 64) P false 32 none).pre s := by
  implies_sat [Spec.Cbc.aesSig, pre, RISCV64.abi, RISCV64.argRegs] [Proof.AesCbc.RISCV64.sat]
    using Proof.AesCbc.RISCV64.sat

theorem wiped_verified {P : Spec.Cbc.aesSig.Post 64} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Cbc.aesSig.contract abi (pre 64) P false 0 none))
    (hd : body.noFrames = true)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₁ m' x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₂ m' x)
    (hout : ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (Sig.bufs Spec.Cbc.aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₁ x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₂ x) :
    Verified target (wiped name body)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 P) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := [])
    (nm := "scratch") (e := .u64) (k := 272) (n := 2176) (i := 5) h Proof.Zeroize.RISCV64.verified
    (by decide) rfl rfl rfl (by decide) (by decide) (by rw [sdepth_of_noFrames hd])
    (by rw [sdepth_of_noFrames (by decide)]) (Nat.zero_le _)
    (pre_local 64) hpost hout (Wipe.wiped 64 P) (sat _)

theorem encrypt_scrubbed :
    Verified target encrypt
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.encrypt_keyed Proof.AesCbc.RISCV64.encrypt_verified) (by lit_decide)
    (encPost_local 64) (encPost_out 64)

theorem decrypt_scrubbed :
    Verified target decrypt
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.decrypt_keyed Proof.AesCbc.RISCV64.decrypt_verified) (by lit_decide)
    (decPost_local 64) (decPost_out 64)

theorem encrypt_verified : Verified target encrypt (Spec.Cbc.aesEncryptContract abi 32) :=
  Verified.of_scrubbed encrypt_scrubbed

theorem decrypt_verified : Verified target decrypt (Spec.Cbc.aesDecryptContract abi 32) :=
  Verified.of_scrubbed decrypt_scrubbed

end VG.Proof.AesCbc.RISCV64.Wiped
