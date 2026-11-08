module

public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Impl.AesEcb.X86
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Proof.Framework.X86.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.AesEcb.Wipe
meta import VerifiedGarbage.Impl.AesEcb.X86
meta import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
meta import VerifiedGarbage.Proof.Framework.X86.CallWipe
meta import VerifiedGarbage.Proof.Zeroize.X86
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-ECB on x86

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` (`Impl/AesEcb/X86.lean`), for
each implementation `v` of the blocks functions (`BlocksImpl`): where it
writes nothing in `scratch` (`v.encWritten = 0`), its code
(`encrypt_free`, `Verified.ecb_of_unwritten`); otherwise a call of it, then
of `vg_zeroize` on the first `v.encWritten` bytes of `scratch`, the only
ones it writes (`encrypt_verified`: `Verified.callWipeTail'`, with the side
conditions of `Proof/AesEcb/Wipe.lean`, with 32 bytes of stack, the frame
and the return address). Likewise for decryption.
-/

@[expose] public section

namespace VG.Proof.AesEcb.X86

open VG VG.X86 VG.Proof.Aes.X86

theorem zeroize_noSp : NoSp Impl.Zeroize.X86.zeroize := NoSp.of_all (by lit_decide)

theorem zeroize_stack : stackUse Impl.Zeroize.X86.zeroize ≤ 0 := by lit_decide

theorem enc_implies :
    (Proof.Aes.blocksX86 Spec.Aes.cipher).Implies (Proof.Aes.encryptBlocksRoundsContract X86.abi) := by
  have a0 : arg blocksSat 0 = 0x1000 := by decide
  have a1 : arg blocksSat 1 = 10 := by decide
  have a2 : arg blocksSat 2 = 0x3000 := by decide
  have a3 : arg blocksSat 3 = 0 := by decide
  have a4 : arg blocksSat 4 = 0x4000 := by decide
  have e : argAddr blocksSat 0 = 0x8004 := by decide
  have esp : blocksSat.gpr .esp = 0x8000 := rfl
  sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat

theorem dec_implies :
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).Implies (Proof.Aes.decryptBlocksRoundsContract X86.abi) := by
  have a0 : arg blocksSat 0 = 0x1000 := by decide
  have a1 : arg blocksSat 1 = 10 := by decide
  have a2 : arg blocksSat 2 = 0x3000 := by decide
  have a3 : arg blocksSat 3 = 0 := by decide
  have a4 : arg blocksSat 4 = 0x4000 := by decide
  have e : argAddr blocksSat 0 = 0x8004 := by decide
  have esp : blocksSat.gpr .esp = 0x8000 := rfl
  sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat

theorem enc_verified (v : BlocksImpl) :
    Verified X86.target v.enc.code (Proof.Aes.encryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct v.encOk v.encCt enc_implies

theorem dec_verified (v : BlocksImpl) :
    Verified X86.target v.dec.code (Proof.Aes.decryptBlocksRoundsContract X86.abi) :=
  Verified.of_correct v.decOk v.decCt dec_implies

theorem args_length : ∀ s vals,
    X86.abi.args ((Spec.Aes.blocksSig.words X86.abi.ptrBits).map (·.bits X86.abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Aes.blocksSig.words X86.abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : X86.abi.args _ = some (stackArgs Spec.Aes.blocksSig)))
  exact stackArgs_length Spec.Aes.blocksSig s

/-- What a run writes of `scratch`, from the variant's bound. -/
theorem written_of {s s' : State} {w : Nat}
    (h : ∀ i, w ≤ i → i < 2048 →
      s'.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i) = s.mem ((arg s 4).setWidth 64 + BitVec.ofNat 64 i)) :
    Sig.writtenWithin X86.abi Spec.Aes.blocksSig [("scratch", w)] s s' := by
  simp [Sig.writtenWithin, X86.abi, Spec.Aes.blocksSig, Sig.words, Param.words, ArgWord.bits, IntTy.bits,
    X86.argSlots, Sig.arrays, X86.argVal, Elem.size]
  exact h

theorem enc_written (v : BlocksImpl) : ∀ s t s',
    (Spec.Aes.blocksSig.contract X86.abi (pre 32) (post 32 enc) false 0 none).pre s →
      Exec isa v.enc.code s t s' → Sig.writtenWithin X86.abi Spec.Aes.blocksSig [("scratch", v.encWritten)] s s' :=
  fun s t s' hs he => written_of (v.encWrittenOk s (enc_implies.pre s hs) t s' he)

theorem dec_written (v : BlocksImpl) : ∀ s t s',
    (Spec.Aes.blocksSig.contract X86.abi (pre 32) (post 32 dec) false 0 none).pre s →
      Exec isa v.dec.code s t s' → Sig.writtenWithin X86.abi Spec.Aes.blocksSig [("scratch", v.decWritten)] s s' :=
  fun s t s' hs he => written_of (v.decWrittenOk s (dec_implies.pre s hs) t s' he)

/-- A state satisfying the ECB contracts' precondition. -/
theorem sat : ∃ s, (Spec.Aes.blocksSig.contract X86.abi (pre 32) (ecbPost 32 enc) false 32).pre s := by
  have a0 : arg blocksSat 0 = 0x1000 := by decide
  have a1 : arg blocksSat 1 = 10 := by decide
  have a2 : arg blocksSat 2 = 0x3000 := by decide
  have a3 : arg blocksSat 3 = 0 := by decide
  have a4 : arg blocksSat 4 = 0x4000 := by decide
  have e : argAddr blocksSat 0 = 0x8004 := by decide
  have esp : blocksSat.gpr .esp = 0x8000 := rfl
  implies_sat [Spec.Aes.blocksSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, pre]
    [a0, a1, a2, a3, a4, e, esp] using blocksSat

/-- The ECB contracts' precondition does not depend on the postcondition. -/
theorem sat' (post : Spec.Aes.blocksSig.Post 32) :
    ∃ s, (Spec.Aes.blocksSig.contract X86.abi (pre 32) post false 32).pre s := sat

/-- `vg_aes_ecb_encrypt` for `v`, where its blocks function writes nothing in
`scratch`: that function's code. -/
theorem encrypt_free (v : BlocksImpl) (h : v.encWritten = 0) :
    Verified X86.target v.enc.code (Spec.AesEcb.encryptContract X86.abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.encryptBlocks_keyed (enc_verified v)) (h ▸ enc_written v) args_length

/-- `vg_aes_ecb_decrypt` for `v`, where its blocks function writes nothing in
`scratch`. -/
theorem decrypt_free (v : BlocksImpl) (h : v.decWritten = 0) :
    Verified X86.target v.dec.code (Spec.AesEcb.decryptContract X86.abi 0) :=
  Verified.ecb_of_unwritten (Proof.Aes.decryptBlocks_keyed (dec_verified v)) (h ▸ dec_written v) args_length

/-- `vg_aes_ecb_encrypt` for `v`: its blocks function, then the zeroize
function on the bytes of `scratch` it writes. -/
theorem encrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesEcb.X86.wiped v.enc v.encWritten) (Spec.AesEcb.encryptContract X86.abi 32) :=
  Verified.callWipeTail' (sig := Spec.Aes.blocksSig) (stack := 0) (zst := 0)
    (pre := pre 32) (post := postTail 32 enc v.encWritten) (post' := ecbPost 32 enc)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 4) (j := 4)
    (Verified.tail_of_written (Proof.Aes.encryptBlocks_keyed (enc_verified v)) (enc_written v) args_length)
    Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (Nat.le_trans v.encWrittenLe (by decide)) (by have := v.encWrittenLe; omega)
    (by decide) v.encNosp (by rw [v.encStack]) zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (postTail_local 32 _ _) (postTail_out 32 _ v.encWrittenLe) (wipedTail 32 _ _) (sat' _)

/-- `vg_aes_ecb_decrypt` for `v`. -/
theorem decrypt_verified (v : BlocksImpl) :
    Verified X86.target (Impl.AesEcb.X86.wiped v.dec v.decWritten) (Spec.AesEcb.decryptContract X86.abi 32) :=
  Verified.callWipeTail' (sig := Spec.Aes.blocksSig) (stack := 0) (zst := 0)
    (pre := pre 32) (post := postTail 32 dec v.decWritten) (post' := ecbPost 32 dec)
    (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (i := 4) (j := 4)
    (Verified.tail_of_written (Proof.Aes.decryptBlocks_keyed (dec_verified v)) (dec_written v) args_length)
    Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (Nat.le_trans v.decWrittenLe (by decide)) (by have := v.decWrittenLe; omega)
    (by decide) v.decNosp (by rw [v.decStack]) zeroize_noSp zeroize_stack (by decide)
    (pre_local 32) (postTail_local 32 _ _) (postTail_out 32 _ v.decWrittenLe) (wipedTail 32 _ _) (sat' _)

theorem zeroize_spSafe : Impl.Zeroize.X86.zeroize.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)

/-- `wiped b` writes `esp` only in its frame and calls, if `b`'s code does
only in its frames. -/
theorem wiped_spSafe {b : Impl.Aes.X86.Blocks} {n : Nat} (h : b.code.all (fun i => !isa.writesSp i) = true) :
    (Impl.AesEcb.X86.wiped b n).all (fun i => !isa.writesSp i) = true := by
  have hz := zeroize_spSafe
  simp only [isa] at h hz
  simp only [Impl.AesEcb.X86.wiped, Impl.CallWipe.X86.callWipe, Code.all, isa, h, hz, Bool.true_and]
  simp [Impl.CallWipe.X86.zeroArgs, Instr.dst]
  decide

theorem encrypt_spSafe (v : BlocksImpl) :
    (Impl.AesEcb.X86.wiped v.enc v.encWritten).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.encSpSafe

theorem decrypt_spSafe (v : BlocksImpl) :
    (Impl.AesEcb.X86.wiped v.dec v.decWritten).all (fun i => !isa.writesSp i) = true := wiped_spSafe v.decSpSafe

end VG.Proof.AesEcb.X86
