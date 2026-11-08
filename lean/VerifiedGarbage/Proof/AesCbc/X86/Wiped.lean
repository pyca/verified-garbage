module

public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.X86.Verified
public import VerifiedGarbage.Impl.AesCbc.X86.Wiped
public import VerifiedGarbage.Proof.Framework.X86.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.AesCbc.Wipe
meta import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Impl.AesCbc.X86.Wiped
meta import VerifiedGarbage.Proof.Framework.X86.CallWipe
meta import VerifiedGarbage.Proof.Zeroize.X86
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-CBC on x86, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` (`Impl/AesCbc/X86/Wiped.lean`),
for each implementation `v` of the blocks functions (`BlocksImpl`), call the
CBC code around it, then zero the whole of `scratch` (2176 bytes, which its
proofs do not bound) with `vg_zeroize`, leaving it scrubbed
(`encrypt_scrubbed`, `decrypt_scrubbed`: `Verified.callWipe'`, with the side
conditions of `Proof/AesCbc/Wipe.lean`), with 60 bytes of stack (the CBC
code's 24, the frame and the return address). `encrypt_verified` and
`decrypt_verified` are those weakened to the contracts of `Spec/Cbc/`, which
do not state it yet.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86.Wiped

open VG VG.X86 VG.Proof.Aes.X86 VG.Proof.AesCbc.Wipe

private theorem zeroize_noSp : NoSp Impl.Zeroize.X86.zeroize := NoSp.of_all (by lit_decide)

private theorem zeroize_stack : stackUse Impl.Zeroize.X86.zeroize ≤ 0 := by lit_decide

private theorem zeroize_spSafe : Impl.Zeroize.X86.zeroize.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

/-- The CBC code around `b` writes `esp` only in its frames, if `b`'s code does. -/
theorem encrypt_noSp (b : Impl.Aes.X86.Blocks) (h : NoSp b.code) : NoSp (Impl.AesCbc.X86.encrypt b) :=
  fun i hi => by
    by_cases hc : i ∈ instrs b.code
    · exact h i hc
    · simp only [Impl.AesCbc.X86.encrypt, Impl.AesCbc.X86.whole, Impl.AesCbc.X86.encBody,
        Impl.AesCbc.X86.blkCall, instrs, List.mem_append, List.mem_cons, hc, false_or, or_false,
        List.not_mem_nil] at hi
      rcases hi with hi | (hi | (rfl | rfl) | hi) | hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.setup, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.encPre, Taint.clobbers i .esp = false) i hi
      · rfl
      · rfl
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.encPost, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.restore 5, Taint.clobbers i .esp = false) i hi

theorem decrypt_noSp (b : Impl.Aes.X86.Blocks) (h : NoSp b.code) : NoSp (Impl.AesCbc.X86.decrypt b) :=
  fun i hi => by
    by_cases hc : i ∈ instrs b.code
    · exact h i hc
    · simp only [Impl.AesCbc.X86.decrypt, Impl.AesCbc.X86.whole, Impl.AesCbc.X86.decBody,
        Impl.AesCbc.X86.blkCall, instrs, List.mem_append, List.mem_cons, hc, false_or, or_false,
        List.not_mem_nil] at hi
      rcases hi with hi | (hi | (rfl | rfl) | hi) | hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.setup, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.decPre, Taint.clobbers i .esp = false) i hi
      · rfl
      · rfl
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.decPost, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.restore 5, Taint.clobbers i .esp = false) i hi

theorem encrypt_stack (b : Impl.Aes.X86.Blocks) (h : stackUse b.code = 0) :
    stackUse (Impl.AesCbc.X86.encrypt b) ≤ 24 := by
  simp only [Impl.AesCbc.X86.encrypt, Impl.AesCbc.X86.whole, Impl.AesCbc.X86.encBody,
    Impl.AesCbc.X86.blkCall, stackUse, h]
  decide

theorem decrypt_stack (b : Impl.Aes.X86.Blocks) (h : stackUse b.code = 0) :
    stackUse (Impl.AesCbc.X86.decrypt b) ≤ 24 := by
  simp only [Impl.AesCbc.X86.decrypt, Impl.AesCbc.X86.whole, Impl.AesCbc.X86.decBody,
    Impl.AesCbc.X86.blkCall, stackUse, h]
  decide

/-- A state satisfying the wrapped contracts' precondition, for any postcondition. -/
theorem sat (P : Spec.Cbc.aesSig.Post 32) :
    ∃ s, (Spec.Cbc.aesSig.contract X86.abi (pre 32) P false 60 none).pre s := by
  have a0 : arg Proof.AesCbc.X86.sat 0 = 0x1000 := by decide
  have a1 : arg Proof.AesCbc.X86.sat 1 = 10 := by decide
  have a2 : arg Proof.AesCbc.X86.sat 2 = 0x2000 := by decide
  have a3 : arg Proof.AesCbc.X86.sat 3 = 0x3000 := by decide
  have a4 : arg Proof.AesCbc.X86.sat 4 = 0 := by decide
  have a5 : arg Proof.AesCbc.X86.sat 5 = 0x4000 := by decide
  have e : argAddr Proof.AesCbc.X86.sat 0 = 0x8004 := by decide
  have esp : Proof.AesCbc.X86.sat.gpr .esp = 0x8000 := rfl
  implies_sat [Spec.Cbc.aesSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, pre]
    [a0, a1, a2, a3, a4, a5, e, esp] using Proof.AesCbc.X86.sat

theorem encrypt_scrubbed (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (scrubbedPost 32 (encPost 32)) false 60 none) :=
  Verified.callWipe' (sig := Spec.Cbc.aesSig) (stack := 24) (zst := 0)
    (pre := pre 32) (post := encPost 32)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5) (j := 5)
    (Proof.AesCbc.encrypt_keyed (Proof.AesCbc.X86.encrypt_verified v)) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    (encrypt_noSp _ v.encNosp) (encrypt_stack _ v.encStack) zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (encPost_local 32) (encPost_out 32) (wiped 32 _) (sat _)

theorem decrypt_scrubbed (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (scrubbedPost 32 (decPost 32)) false 60 none) :=
  Verified.callWipe' (sig := Spec.Cbc.aesSig) (stack := 24) (zst := 0)
    (pre := pre 32) (post := decPost 32)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5) (j := 5)
    (Proof.AesCbc.decrypt_keyed (Proof.AesCbc.X86.decrypt_verified v)) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    (decrypt_noSp _ v.decNosp) (decrypt_stack _ v.decStack) zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (decPost_local 32) (decPost_out 32) (wiped 32 _) (sat _)

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix) (Spec.Cbc.aesEncryptContract X86.abi 60) :=
  Verified.of_scrubbed (encrypt_scrubbed v)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix) (Spec.Cbc.aesDecryptContract X86.abi 60) :=
  Verified.of_scrubbed (decrypt_scrubbed v)

/-- The wrapped code writes `esp` only in its frame and calls, if the CBC code does. -/
theorem wiped_spSafe {name : String} {body : Prog isa} (h : body.all (fun i => !isa.writesSp i) = true) :
    (Impl.AesCbc.X86.Wiped.wiped name body).all (fun i => !isa.writesSp i) = true := by
  have hz := zeroize_spSafe
  simp only [isa] at h hz
  simp only [Impl.AesCbc.X86.Wiped.wiped, Impl.CallWipe.X86.callWipe, Code.all, isa, h, hz, Bool.true_and]
  decide

theorem encrypt_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (Proof.AesCbc.X86.encrypt_spSafe v)

theorem decrypt_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (Proof.AesCbc.X86.decrypt_spSafe v)

end VG.Proof.AesCbc.X86.Wiped
