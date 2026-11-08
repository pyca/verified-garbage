module

public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
public import VerifiedGarbage.Proof.Zeroize.Arm

/-!
# AES-CBC on ARMv7, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` call the CBC code
(`Impl/AesCbc/Arm.lean`, now the internal functions
`vg_aes_cbc_encrypt_unwiped` and `vg_aes_cbc_decrypt_unwiped`) by
`callWipeStack`, which copies the two stack arguments (`n` and `scratch`)
into its frame for the call, then zero the whole of `scratch` (2176 bytes,
which the CBC proofs do not bound) with `vg_zeroize`, leaving it scrubbed
(`encrypt_scrubbed`, `decrypt_scrubbed`), with 32 bytes of stack (the CBC
code's 8 and `callWipeStack`'s 24). `encrypt_verified` and
`decrypt_verified` are those weakened to the contracts of `Spec/Cbc/`, which
do not state it yet.
-/

@[expose] public section

namespace VG.Proof.AesCbc.Arm.Wiped

open VG VG.Arm VG.Arm.FrameStack VG.Proof.AesCbc.Wipe

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2176 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.ArmStack.callWipeStack 2 4 2176 name body "vg_zeroize" Impl.Zeroize.Arm.zeroize

/-- `vg_aes_cbc_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_cbc_encrypt_unwiped" Impl.AesCbc.Arm.encrypt

/-- `vg_aes_cbc_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_cbc_decrypt_unwiped" Impl.AesCbc.Arm.decrypt

theorem sat (P : Spec.Cbc.aesSig.Post 32) :
    ∃ s, (Spec.Cbc.aesSig.contract abi (pre 32) P false 32 none).pre s := by
  implies_sat [Spec.Cbc.aesSig, pre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.AesCbc.Arm.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.AesCbc.Arm.sat

theorem wiped_verified {P : Spec.Cbc.aesSig.Post 32} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Cbc.aesSig.contract abi (pre 32) P false 8 none))
    (hd : armStack body ≤ 8)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cbc.aesSig.words 32).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 32) P vs m₁ m' x → Curry.apply (Spec.Cbc.aesSig.words 32) P vs m₂ m' x)
    (hout : ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words 32).length →
      (Sig.bufs Spec.Cbc.aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 32) P vs m m₁ x → Curry.apply (Spec.Cbc.aesSig.words 32) P vs m m₂ x) :
    Verified target (wiped name body)
      (Spec.Cbc.aesSig.contract abi (pre 32) (scrubbedPost 32 P) false 32 none) :=
  Verified.callWipeStack' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := [])
    (nm := "scratch") (e := .u64) (kk := 272) (n := 2176) (i := 5) (k := 2) (off := 4) (stack := 8)
    h Proof.Zeroize.Arm.verified
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide)
    hd (by decide) (Nat.zero_le _)
    (pre_local 32) hpost hout (Wipe.wiped 32 P) (sat _)

theorem encrypt_scrubbed :
    Verified target encrypt (Spec.Cbc.aesSig.contract abi (pre 32) (scrubbedPost 32 (encPost 32)) false 32 none) :=
  wiped_verified (Proof.AesCbc.encrypt_keyed Proof.AesCbc.Arm.encrypt_verified) (by decide)
    (encPost_local 32) (encPost_out 32)

theorem decrypt_scrubbed :
    Verified target decrypt (Spec.Cbc.aesSig.contract abi (pre 32) (scrubbedPost 32 (decPost 32)) false 32 none) :=
  wiped_verified (Proof.AesCbc.decrypt_keyed Proof.AesCbc.Arm.decrypt_verified) (by decide)
    (decPost_local 32) (decPost_out 32)

theorem encrypt_verified : Verified target encrypt (Spec.Cbc.aesEncryptContract abi 32) :=
  Verified.of_scrubbed encrypt_scrubbed

theorem decrypt_verified : Verified target decrypt (Spec.Cbc.aesDecryptContract abi 32) :=
  Verified.of_scrubbed decrypt_scrubbed

end VG.Proof.AesCbc.Arm.Wiped
