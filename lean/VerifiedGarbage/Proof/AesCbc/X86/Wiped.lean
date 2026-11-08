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
for each implementation `v` of the blocks functions (`BlocksImpl`): the CBC
code around it, which zeroes what it saves in `scratch` and so leaves each
byte of `scratch` from offset `v.encWritten` (`v.decWritten`) on unchanged
or zero (`tailPost`); where that is 0, the CBC code itself, which leaves
`scratch` scrubbed (`encrypt_free`, with 24 bytes of stack); otherwise a call
of it, then of `vg_zeroize` on the first `v.encWritten` bytes
(`encrypt_scrubbed`: `Verified.callWipeTail'`, with the side conditions of
`Proof/AesCbc/Wipe.lean`), with 72 bytes of stack (the CBC code's 24, the
frame and the return address). `encrypt_verified` and `decrypt_verified`
are those weakened to the contracts of `Spec/Cbc/`, which do not state it
yet.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86.Wiped

open VG VG.X86 VG.Proof.Aes.X86 VG.Proof.AesCbc.Wipe

private theorem zeroize_noSp : NoSp Impl.Zeroize.X86.zeroize := NoSp.of_all (by lit_decide)

private theorem zeroize_stack : stackUse Impl.Zeroize.X86.zeroize ≤ 0 := by lit_decide

private theorem zeroize_spSafe : Impl.Zeroize.X86.zeroize.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

/-- The CBC code around `b` writes `esp` only in its frames, if `b`'s code does. -/
theorem encrypt_noSp (b : Impl.Aes.X86.Blocks) (h : NoSp b.code) : NoSp (Impl.AesCbc.X86.encryptZ b) :=
  fun i hi => by
    by_cases hc : i ∈ instrs b.code
    · exact h i hc
    · simp only [Impl.AesCbc.X86.encryptZ, Impl.AesCbc.X86.wholeZ, Impl.AesCbc.X86.encBody,
        Impl.AesCbc.X86.blkCall, instrs, List.mem_append, List.mem_cons, hc, false_or, or_false,
        List.not_mem_nil] at hi
      rcases hi with hi | (hi | (rfl | rfl) | hi) | hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.setup, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.encPre, Taint.clobbers i .esp = false) i hi
      · rfl
      · rfl
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.encPost, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.restore 5 ++ Impl.AesCbc.X86.zeroSaved,
          Taint.clobbers i .esp = false) i (List.mem_append.mpr hi)

theorem decrypt_noSp (b : Impl.Aes.X86.Blocks) (h : NoSp b.code) : NoSp (Impl.AesCbc.X86.decryptZ b) :=
  fun i hi => by
    by_cases hc : i ∈ instrs b.code
    · exact h i hc
    · simp only [Impl.AesCbc.X86.decryptZ, Impl.AesCbc.X86.wholeZ, Impl.AesCbc.X86.decBody,
        Impl.AesCbc.X86.blkCall, instrs, List.mem_append, List.mem_cons, hc, false_or, or_false,
        List.not_mem_nil] at hi
      rcases hi with hi | (hi | (rfl | rfl) | hi) | hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.setup, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.decPre, Taint.clobbers i .esp = false) i hi
      · rfl
      · rfl
      · exact (by decide : ∀ i ∈ Impl.AesCbc.X86.decPost, Taint.clobbers i .esp = false) i hi
      · exact (by decide : ∀ i ∈ Impl.CmacAes.X86.restore 5 ++ Impl.AesCbc.X86.zeroSaved,
          Taint.clobbers i .esp = false) i (List.mem_append.mpr hi)

theorem encrypt_stack (b : Impl.Aes.X86.Blocks) (h : stackUse b.code = 0) :
    stackUse (Impl.AesCbc.X86.encryptZ b) ≤ 24 := by
  simp only [Impl.AesCbc.X86.encryptZ, Impl.AesCbc.X86.wholeZ, Impl.AesCbc.X86.encBody,
    Impl.AesCbc.X86.blkCall, stackUse, h]
  decide

theorem decrypt_stack (b : Impl.Aes.X86.Blocks) (h : stackUse b.code = 0) :
    stackUse (Impl.AesCbc.X86.decryptZ b) ≤ 24 := by
  simp only [Impl.AesCbc.X86.decryptZ, Impl.AesCbc.X86.wholeZ, Impl.AesCbc.X86.decBody,
    Impl.AesCbc.X86.blkCall, stackUse, h]
  decide

/-- A state satisfying the wrapped contracts' precondition, for any postcondition. -/
theorem sat (P : Spec.Cbc.aesSig.Post 32) :
    ∃ s, (Spec.Cbc.aesSig.contract X86.abi (pre 32) P false 72 none).pre s := by
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

theorem args_length : ∀ s vals,
    X86.abi.args ((Spec.Cbc.aesSig.words X86.abi.ptrBits).map (·.bits X86.abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Cbc.aesSig.words X86.abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : X86.abi.args _ = some (stackArgs Spec.Cbc.aesSig)))
  exact stackArgs_length Spec.Cbc.aesSig s

/-- The bytes of `scratch` a run leaves unchanged or zero, as the calling
convention gives its address. -/
theorem tail_of {s s' : State} {w : Nat}
    (h : ∀ i, w ≤ i → i < 2176 →
      s'.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) ∨
        s'.mem ((arg s 5).setWidth 64 + BitVec.ofNat 64 i) = 0) :
    ∀ vals, X86.abi.args ((Spec.Cbc.aesSig.words X86.abi.ptrBits).map (·.bits X86.abi.ptrBits)) = some vals →
      ∀ i, w ≤ i → i < 2176 →
        X86.abi.mem s' ((vals s).getD 5 0 + BitVec.ofNat 64 i) = X86.abi.mem s ((vals s).getD 5 0 + BitVec.ofNat 64 i) ∨
          X86.abi.mem s' ((vals s).getD 5 0 + BitVec.ofNat 64 i) = 0 := by
  intro vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : X86.abi.args _ = some (stackArgs Spec.Cbc.aesSig)))
  simp [stackArgs, widths, Spec.Cbc.aesSig, Sig.words, Param.words, ArgWord.bits, IntTy.bits, X86.argSlots,
    X86.argVal, X86.abi]
  exact h

theorem encrypt_tail (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.encryptZ v.enc)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (tailPost 32 (encPost 32) v.encWritten) false 24 none) :=
  Verified.tail_of (Proof.AesCbc.encrypt_keyed (Proof.AesCbc.X86.encryptZ_verified v))
    (fun s t s' hs he => tail_of (Proof.AesCbc.X86.encryptZ_tail v s (Proof.AesCbc.X86.enc_implies.pre s hs) t s' he))
    args_length

theorem decrypt_tail (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.decryptZ v.dec)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (tailPost 32 (decPost 32) v.decWritten) false 24 none) :=
  Verified.tail_of (Proof.AesCbc.decrypt_keyed (Proof.AesCbc.X86.decryptZ_verified v))
    (fun s t s' hs he => tail_of (Proof.AesCbc.X86.decryptZ_tail v s (Proof.AesCbc.X86.dec_implies.pre s hs) t s' he))
    args_length

/-- `vg_aes_cbc_encrypt` for a `v` whose encryption writes nothing in
`scratch`: the CBC code, which leaves `scratch` scrubbed. -/
theorem encrypt_free (v : BlocksImpl) (h : v.encWritten = 0) :
    Verified X86.target (Impl.AesCbc.X86.encryptZ v.enc) (Spec.Cbc.aesEncryptContract X86.abi 24) :=
  Verified.of_scrubbed ((h ▸ encrypt_tail v).post_mono (tailPost_zero 32 _))

theorem decrypt_free (v : BlocksImpl) (h : v.decWritten = 0) :
    Verified X86.target (Impl.AesCbc.X86.decryptZ v.dec) (Spec.Cbc.aesDecryptContract X86.abi 24) :=
  Verified.of_scrubbed ((h ▸ decrypt_tail v).post_mono (tailPost_zero 32 _))

theorem encrypt_scrubbed (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix v.encWritten)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (scrubbedPost 32 (encPost 32)) false 72 none) :=
  Verified.callWipeTail' (sig := Spec.Cbc.aesSig) (stack := 24) (zst := 0)
    (pre := pre 32) (post := tailPost 32 (encPost 32) v.encWritten)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5) (j := 5)
    (encrypt_tail v) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (Nat.le_trans v.encWrittenLe (by decide)) (by have := v.encWrittenLe; omega)
    (by decide) (encrypt_noSp _ v.encNosp) (encrypt_stack _ v.encStack) zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (tailPost_local 32 _ (encPost_local 32))
    (tailPost_out 32 (Nat.le_trans v.encWrittenLe (by decide)) (encPost_out 32)) (wipedTail 32 _ _) (sat _)

theorem decrypt_scrubbed (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix v.decWritten)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (scrubbedPost 32 (decPost 32)) false 72 none) :=
  Verified.callWipeTail' (sig := Spec.Cbc.aesSig) (stack := 24) (zst := 0)
    (pre := pre 32) (post := tailPost 32 (decPost 32) v.decWritten)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5) (j := 5)
    (decrypt_tail v) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (Nat.le_trans v.decWrittenLe (by decide)) (by have := v.decWrittenLe; omega)
    (by decide) (decrypt_noSp _ v.decNosp) (decrypt_stack _ v.decStack) zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (tailPost_local 32 _ (decPost_local 32))
    (tailPost_out 32 (Nat.le_trans v.decWrittenLe (by decide)) (decPost_out 32)) (wipedTail 32 _ _) (sat _)

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix v.encWritten)
      (Spec.Cbc.aesEncryptContract X86.abi 72) :=
  Verified.of_scrubbed (encrypt_scrubbed v)

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix v.decWritten)
      (Spec.Cbc.aesDecryptContract X86.abi 72) :=
  Verified.of_scrubbed (decrypt_scrubbed v)

/-- The wrapped code writes `esp` only in its frame and calls, if the CBC code does. -/
theorem wiped_spSafe {name : String} {body : Prog isa} {n : Nat} (h : body.all (fun i => !isa.writesSp i) = true) :
    (Impl.AesCbc.X86.Wiped.wiped name body n).all (fun i => !isa.writesSp i) = true := by
  have hz := zeroize_spSafe
  simp only [isa] at h hz
  simp only [Impl.AesCbc.X86.Wiped.wiped, Impl.CallWipe.X86.callWipe, Code.all, isa, h, hz, Bool.true_and]
  simp [Impl.CallWipe.X86.zeroArgs, Instr.dst]
  decide

theorem encryptZ_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.encryptZ v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.AesCbc.X86.encryptZ, Impl.AesCbc.X86.wholeZ, Impl.AesCbc.X86.encBody, Impl.AesCbc.X86.blkCall,
    Code.all, v.encSpSafe]
  decide

theorem decryptZ_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.decryptZ v.dec).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.AesCbc.X86.decryptZ, Impl.AesCbc.X86.wholeZ, Impl.AesCbc.X86.decBody, Impl.AesCbc.X86.blkCall,
    Code.all, v.decSpSafe]
  decide

theorem encrypt_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Wiped.encrypt v.enc v.suffix v.encWritten).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (encryptZ_spSafe v)

theorem decrypt_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Wiped.decrypt v.dec v.suffix v.decWritten).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (decryptZ_spSafe v)

end VG.Proof.AesCbc.X86.Wiped
