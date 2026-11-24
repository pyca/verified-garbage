module

public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.X86.Verified
public import VerifiedGarbage.Proof.AesCbc.X86.Groups
public import VerifiedGarbage.Impl.AesCbc.X86.Decrypt
import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
public import VerifiedGarbage.Impl.AesCbc.X86.Wiped
public import VerifiedGarbage.Proof.Framework.X86.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCbc.Wipe
meta import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Proof.AesCbc.X86.Groups
meta import VerifiedGarbage.Impl.AesCbc.X86.Decrypt
meta import VerifiedGarbage.Proof.AesCbc.X86.Decrypt
meta import VerifiedGarbage.Impl.AesCbc.X86.Wiped
meta import VerifiedGarbage.Proof.Framework.X86.CallWipe
meta import VerifiedGarbage.Proof.Zeroize.X86
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CBC on x86, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` (`Impl/AesCbc/X86/Wiped.lean`),
for each implementation `v` of the blocks functions (`BlocksImpl`): the CBC
code around it, which zeroes what it saves in `scratch` and so leaves each
byte of `scratch` from offset `v.encWritten` (`v.decWritten`) on unchanged
or zero (`tailZPost`); where that is 0, the CBC code itself, which leaves
`scratch` scrubbed (`encrypt_free`, with 24 bytes of stack); otherwise a call
of it, then of `vg_zeroize` on the first `v.encWritten` bytes
(`encrypt_scrubbed`: `Verified.callWipeTail'`, with the side conditions of
`Proof/AesCbc/Wipe.lean`), with 72 bytes of stack (the CBC code's 24, the
frame and the return address); in decryption, whose CBC code around a block
function has a buffer on the stack too, with 48 bytes more than that code
(`decStack`). `encrypt_verified` and `decrypt_verified`
state them as the contracts of `Spec/Cbc/`. Which is emitted for `v`: the
first where it writes nothing, the second otherwise
(`Proof/AesCbc/X86/Scrub.lean`, with its cleanup).

Decryption's CBC code for `v` is `decryptCode v`: for AES-NI (`hardware`),
the code that deciphers six blocks at a time with no call
(`Impl/AesCbc/X86/Decrypt.lean`, `Proof/AesCbc/X86/Decrypt.lean`), which
writes only the first 240 bytes of `scratch` (`decWritten`); for any other
implementation, 64 blocks a call of its `vg_aes_decrypt_blocks`
(`Impl/AesCbc/X86/Groups.lean`, `Proof/AesCbc/X86/Groups.lean`). Encryption's
is `encryptCode v`: for an implementation with a chain (`Chain.of`: AES-NI and
SSSE3), the code that keeps the chaining value in a register with no call
(`Impl.AesCbc.X86.encryptChain`, `Proof.AesCbc.X86.Encrypt`), which leaves
`scratch` but what the chain writes unchanged or zero (`encWritten`: nothing,
with AES-NI); for any other implementation, `encryptZ` around its
`vg_aes_encrypt_blocks`.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86.Wiped

open VG VG.X86 VG.Proof.Aes.X86 VG.Proof.AesCbc.Wipe
open VG.Impl.Aes.X86 (Chain)

private theorem zeroize_noSp : NoSp Impl.Zeroize.X86.zeroize := NoSp.of_all (by lit_decide)

private theorem zeroize_stack : stackUse Impl.Zeroize.X86.zeroize ≤ 0 := by lit_decide

private theorem zeroize_spSafe : Impl.Zeroize.X86.zeroize.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_spTest (by lit_decide)

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

theorem encrypt_stack (b : Impl.Aes.X86.Blocks) (h : stackUse b.code = 0) :
    stackUse (Impl.AesCbc.X86.encryptZ b) ≤ 24 := by
  simp only [Impl.AesCbc.X86.encryptZ, Impl.AesCbc.X86.wholeZ, Impl.AesCbc.X86.encBody,
    Impl.AesCbc.X86.blkCall, stackUse, h]
  decide

/-! ## The CBC code -/

/-- `v` is AES-NI, whose CBC code deciphers the blocks itself. -/
def hardware (v : BlocksImpl) : Bool := v.dec.name == "vg_aes_decrypt_blocks_aesni"

/-- The CBC encryption code for `v`: around the chain of `v`'s
`vg_aes_encrypt_blocks` if it has one (`Chain.of`), which keeps the chaining
value in a register; otherwise around the function. -/
def encryptCode (v : BlocksImpl) : Prog isa :=
  Chain.choose v.enc.name Impl.AesCbc.X86.encryptChain (Impl.AesCbc.X86.encryptZ v.enc)

/-- `encryptCode v` writes no byte of `scratch` at offset `encWritten v` or
beyond, but zeros. -/
def encWritten (v : BlocksImpl) : Nat :=
  match Chain.of v.enc.name with
  | some c => c.written
  | none => v.encWritten

theorem encryptCode_some {v : BlocksImpl} {c : Chain} (h : Chain.of v.enc.name = some c) :
    encryptCode v = Impl.AesCbc.X86.encryptChain c := Proof.Aes.X86.Chain.choose_some h _ _

theorem encryptCode_none {v : BlocksImpl} (h : Chain.of v.enc.name = none) :
    encryptCode v = Impl.AesCbc.X86.encryptZ v.enc := Proof.Aes.X86.Chain.choose_none h _ _

theorem encryptCode_cases (v : BlocksImpl) :
    (∃ c, Chain.of v.enc.name = some c ∧ encryptCode v = Impl.AesCbc.X86.encryptChain c) ∨
      encryptCode v = Impl.AesCbc.X86.encryptZ v.enc := Proof.Aes.X86.Chain.choose_cases _ _ _

theorem encWritten_some {v : BlocksImpl} {c : Chain} (h : Chain.of v.enc.name = some c) :
    encWritten v = c.written := by rw [encWritten, h]

theorem encWritten_none {v : BlocksImpl} (h : Chain.of v.enc.name = none) : encWritten v = v.encWritten := by
  rw [encWritten, h]

theorem encWritten_le (v : BlocksImpl) : encWritten v ≤ 2048 := by
  unfold encWritten
  split
  · next h => exact (Proof.Aes.X86.Chain.of_ok h).le
  · exact v.encWrittenLe

theorem encryptCode_noSp (v : BlocksImpl) : NoSp (encryptCode v) := by
  rcases encryptCode_cases v with ⟨c, h, e⟩ | e <;> rw [e]
  · exact Encrypt.noSp h
  · exact encrypt_noSp _ v.encNosp

theorem encryptCode_stack (v : BlocksImpl) : stackUse (encryptCode v) ≤ 24 := by
  rcases encryptCode_cases v with ⟨c, h, e⟩ | e <;> rw [e]
  · rw [Encrypt.stack h]; exact Nat.zero_le _
  · exact encrypt_stack _ v.encStack

/-- The CBC decryption code for `v`: with AES-NI, the code that deciphers six
blocks at a time; otherwise the code around `v`'s `vg_aes_decrypt_blocks`. -/
def decryptCode (v : BlocksImpl) : Prog isa :=
  if hardware v then Impl.AesCbc.X86.Decrypt.decrypt else Impl.AesCbc.X86.Groups.framed v.dec true

/-- The stack `decryptCode v`'s contract gives it. -/
def decStack (v : BlocksImpl) : Nat := if hardware v then 24 else 1108

theorem decStack_le (v : BlocksImpl) : decStack v = 24 ∨ decStack v = 1108 := by
  unfold decStack
  split
  · exact .inl rfl
  · exact .inr rfl

/-- `decryptCode v` writes no byte of `scratch` at offset `decWritten v` or
beyond, but zeros. -/
def decWritten (v : BlocksImpl) : Nat := if hardware v then 240 else v.decWritten

theorem decWritten_le (v : BlocksImpl) : decWritten v ≤ 2048 := by
  unfold decWritten
  split
  · decide
  · exact v.decWrittenLe

theorem decryptCode_noSp (v : BlocksImpl) : NoSp (decryptCode v) := by
  unfold decryptCode
  split
  · exact Decrypt.noSp
  · exact Groups.framed_noSp _ _ v.decNosp

theorem decryptCode_stack (v : BlocksImpl) : stackUse (decryptCode v) ≤ decStack v := by
  unfold decryptCode decStack
  split
  · rw [Decrypt.stack]; exact Nat.zero_le _
  · exact Groups.framed_stack _ _ v.decStack

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

/-- The same, with the stack of decryption's code around a block function. -/
theorem satL (P : Spec.Cbc.aesSig.Post 32) :
    ∃ s, (Spec.Cbc.aesSig.contract X86.abi (pre 32) P false 1156 none).pre s := by
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
    Verified X86.target (encryptCode v)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (tailZPost 32 (encPost 32) (encWritten v)) false 24 none) := by
  cases h : Chain.of v.enc.name with
  | some c =>
    rw [encryptCode_some h, encWritten_some h]
    exact Verified.tailZ_of (Proof.AesCbc.encrypt_keyed (Encrypt.verified h))
      (fun s t s' hs he => tail_of (Encrypt.tail h s (Proof.AesCbc.X86.enc_implies.pre s hs) t s' he))
      args_length
  | none =>
    rw [encryptCode_none h, encWritten_none h]
    exact Verified.tailZ_of (Proof.AesCbc.encrypt_keyed (Proof.AesCbc.X86.encryptZ_verified v))
      (fun s t s' hs he => tail_of (Proof.AesCbc.X86.encryptZ_tail v s (Proof.AesCbc.X86.enc_implies.pre s hs) t s' he))
      args_length

theorem decrypt_tail (v : BlocksImpl) :
    Verified X86.target (decryptCode v)
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (tailZPost 32 (decPost 32) (decWritten v)) false (decStack v)
        none) := by
  by_cases h : hardware v = true
  · rw [decryptCode, decWritten, decStack, ite_eq_left h, ite_eq_left h, ite_eq_left h]
    exact Verified.tailZ_of (Proof.AesCbc.decrypt_keyed Decrypt.verified)
      (fun s t s' hs he => tail_of fun i h1 h2 =>
        .inl (Decrypt.unwritten s (Proof.AesCbc.X86.dec_implies.pre s hs) t s' he i h1 h2))
      args_length
  · rw [decryptCode, decWritten, decStack, ite_eq_right h, ite_eq_right h, ite_eq_right h]
    exact Groups.cbc_keyed (Groups.framed_verified Groups.par_cbc (Groups.fn_dec v))

/-- `vg_aes_cbc_encrypt` for a `v` whose encryption writes nothing in
`scratch`: the CBC code, which leaves `scratch` scrubbed. -/
theorem encrypt_free (v : BlocksImpl) (h : encWritten v = 0) :
    Verified X86.target (encryptCode v) (Spec.Cbc.aesEncryptContract X86.abi 24) :=
  (h ▸ encrypt_tail v).post_mono (tailZPost_zero 32 _)

theorem decrypt_free (v : BlocksImpl) (h : decWritten v = 0) :
    Verified X86.target (decryptCode v) (Spec.Cbc.aesDecryptContract X86.abi (decStack v)) :=
  (h ▸ decrypt_tail v).post_mono (tailZPost_zero 32 _)

theorem encrypt_scrubbed (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.encrypt (encryptCode v) v.suffix (encWritten v))
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (scrubbedPost 32 (encPost 32)) false 72 none) :=
  Verified.callWipeTail' (sig := Spec.Cbc.aesSig) (stack := 24) (zst := 0)
    (pre := pre 32) (post := tailZPost 32 (encPost 32) (encWritten v))
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5) (j := 5)
    (encrypt_tail v) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (Nat.le_trans (encWritten_le v) (by decide))
    (by have := encWritten_le v; omega_using [this])
    (by decide) (encryptCode_noSp v) (encryptCode_stack v) zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (tailZPost_local 32 _ (encPost_local 32))
    (tailZPost_out 32 (Nat.le_trans (encWritten_le v) (by decide)) (encPost_out 32)) (wipedTailZ 32 _ _) (sat _)

theorem decrypt_scrubbed (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.decrypt (decryptCode v) v.suffix (decWritten v))
      (Spec.Cbc.aesSig.contract X86.abi (pre 32) (scrubbedPost 32 (decPost 32)) false (decStack v + 48) none) :=
  Verified.callWipeTail' (sig := Spec.Cbc.aesSig) (stack := decStack v) (zst := 0)
    (pre := pre 32) (post := tailZPost 32 (decPost 32) (decWritten v))
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 5) (j := 5)
    (decrypt_tail v) Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (Nat.le_trans (decWritten_le v) (by decide))
    (by have := decWritten_le v; omega_using [this])
    (by decide) (decryptCode_noSp v) (decryptCode_stack v) zeroize_noSp zeroize_stack (Nat.zero_le _)
    (pre_local 32) (tailZPost_local 32 _ (decPost_local 32))
    (tailZPost_out 32 (Nat.le_trans (decWritten_le v) (by decide)) (decPost_out 32)) (wipedTailZ 32 _ _)
    (by rcases decStack_le v with h | h <;> rw [h]; exacts [sat _, satL _])

theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.encrypt (encryptCode v) v.suffix (encWritten v))
      (Spec.Cbc.aesEncryptContract X86.abi 72) :=
  encrypt_scrubbed v

theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesCbc.X86.Wiped.decrypt (decryptCode v) v.suffix (decWritten v))
      (Spec.Cbc.aesDecryptContract X86.abi (decStack v + 48)) :=
  decrypt_scrubbed v

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

theorem encryptCode_spSafe (v : BlocksImpl) : (encryptCode v).all (fun i => !isa.writesSp i) = true := by
  rcases encryptCode_cases v with ⟨c, h, e⟩ | e <;> rw [e]
  · exact Encrypt.spSafe h
  · exact encryptZ_spSafe v

theorem encrypt_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Wiped.encrypt (encryptCode v) v.suffix (encWritten v)).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (encryptCode_spSafe v)

theorem decryptCode_spSafe (v : BlocksImpl) : (decryptCode v).all (fun i => !isa.writesSp i) = true := by
  unfold decryptCode
  split
  · exact Decrypt.spSafe
  · exact Groups.framed_spSafe _ _ v.decSpSafe

theorem decrypt_spSafe (v : BlocksImpl) :
    (Impl.AesCbc.X86.Wiped.decrypt (decryptCode v) v.suffix (decWritten v)).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (decryptCode_spSafe v)

end VG.Proof.AesCbc.X86.Wiped
