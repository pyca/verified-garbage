module

public import VerifiedGarbage.Impl.AesOfb.X86.Final
public import VerifiedGarbage.Proof.AesOfb.Final
public import VerifiedGarbage.Proof.AesOfb.X86.Verified
public import VerifiedGarbage.Proof.AesCfb.X86.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.AesOfb.X86.Body
public import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Proof.AesCbc.X86.Verified

/-!
# AES-OFB of a message's last piece on x86 (32-bit)

`cryptFinal_framed`: `vg_aes_ofb_final` (`Impl/AesOfb/X86/Final.lean`), for any
implementation `v` of the block functions (`BlocksImpl`), meets
`Proof.AesOfb.finalRoundsContract`, from which the shared contract follows
(`Proof.AesOfb.final_keyed`).

Its code is AES-CFB's final function around a call of the whole-block
AES-OFB function, so its proof is AES-CFB's (`Proof/AesCfb/X86/Final.lean`),
for OFB as a `Mode` (`ofbMode`): `final_wp` runs it, for any mode, to what it
leaves before restoring the registers (`Done`); `final_ct` gives its
constant time. `ofbFinalX86` is AES-CFB's code contract with OFB's
postcondition, which `final_post` gives from `Done` by
`Proof.AesOfb.cryptFinal_of`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCfb.X86 (finalX86 FPre Done fW fR fIv fD fL fN final_wp final_ct finalSat all_of_noSp
  framed_spSafe)
open VG.Proof.AesCbc.X86 (modeX86)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesOfb.X86
open VG.Impl.AesCfb.X86 (final finalTail wholeCall)

/-- The code's contract, with the arguments on the stack `(schedule, rounds,
iv, data, len, scratch, save)`: AES-CFB's final functions' (`finalX86`),
with the data and the block at `iv` as `Spec.Ofb.CryptFinal` says, by AES
with the key schedule it is given. -/
def ofbFinalX86 : Contract isa :=
  { finalX86 true with
    post := fun s s' => Spec.Ofb.CryptFinal (ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) 16 s.mem
      s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) (arg s 4).toNat }

/-- The contract the frame needs: the shared one, with `save`, 16 bytes, as
a seventh argument, and 52 bytes of stack (the whole-block function's
arguments, its return address and its own 24 bytes). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract X86.abi Spec.Ofb.aesFinalSig "save" .u64 2 (finalPre X86.abi.ptrBits)
    (finalPost X86.abi.ptrBits) false 52

theorem final_implies : ofbFinalX86.Implies finalScratchContract := by
  have a0 : arg finalSat 0 = 0x1000 := by decide
  have a1 : arg finalSat 1 = 10 := by decide
  have a2 : arg finalSat 2 = 0x2000 := by decide
  have a3 : arg finalSat 3 = 0x3000 := by decide
  have a4 : arg finalSat 4 = 0 := by decide
  have a5 : arg finalSat 5 = 0x4000 := by decide
  have a6 : arg finalSat 6 = 0x5000 := by decide
  have e : argAddr finalSat 0 = 0x8004 := by decide
  have esp : finalSat.gpr .esp = 0x8000 := rfl
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ofb.aesFinalSig, finalPre, finalPost, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ofbFinalX86, finalX86] [a0, a1, a2, a3, a4, a5, a6, e, esp] using finalSat

/-- `Spec.Ofb.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done ofbMode s₀ s₁) (hm : s'.mem = s₁.mem) :
    ofbFinalX86.post s₀ s' := by
  show Spec.Ofb.CryptFinal (ciphAt s₀.mem ((fW s₀).setWidth 64) (fR s₀)) 16 s₀.mem s'.mem
    ((fIv s₀).setWidth 64) ((fD s₀).setWidth 64) (fL s₀)
  have e := AesCbc.length_blocksAt s₀.mem ((fD s₀).setWidth 64) (fN s₀)
  have hb := h.blocks
  have ht := h.tail
  have hi := h.iv
  rw [ofbMode_out] at hb
  rw [ofbMode_chain, e] at ht hi
  exact cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact hb) (fun q hq => by rw [hm]; exact ht q hq)
    (by rw [hm]; exact hi)

theorem final_correct (v : BlocksImpl) (hsp : NoSp (crypt v.enc)) (hst : stackUse (crypt v.enc) = 24)
    (s : State) (hs : ofbFinalX86.pre s) :
    ∃ t s', Exec isa (cryptFinal v.enc v.suffix) s t s' ∧ abiPreserved s s' ∧ ofbFinalX86.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ :=
    final_wp (M := ofbMode) (fun _ hs => AesCbc.X86.whole_wp (body_ok v) hs) hsp hst v (FPre.of (enc := true) hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩

/-! ## The code's properties -/

theorem crypt_noSp (v : BlocksImpl) : NoSp (crypt v.enc) :=
  NoSp.of_all (by
    simp only [crypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, Code.allInstrs,
      all_of_noSp v.encNosp]
    decide +kernel)

theorem crypt_stack (v : BlocksImpl) : stackUse (crypt v.enc) = 24 := by
  simp only [crypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, stackUse, v.encStack]
  decide

theorem cryptFinal_noSp (v : BlocksImpl) :
    (cryptFinal v.enc v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [cryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, Code.allInstrs,
    all_of_noSp (crypt_noSp v), all_of_noSp v.encNosp]
  decide +kernel

theorem cryptFinal_stack (v : BlocksImpl) : stackUse (cryptFinal v.enc v.suffix) ≤ 52 := by
  simp only [cryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, stackUse, crypt_stack v,
    v.encStack]
  decide

theorem cryptFinal_spSafe (v : BlocksImpl) :
    (cryptFinal v.enc v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [cryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, Code.all, crypt_spSafe v,
    v.encSpSafe]
  decide +kernel

/-! ## Verified -/

theorem cryptFinal_verified (v : BlocksImpl) :
    Verified X86.target (cryptFinal v.enc v.suffix) finalScratchContract :=
  Verified.of_correct (final_correct v (crypt_noSp v) (crypt_stack v))
    (final_ct (enc := true) (fun _ hs => AesCbc.X86.whole_wp (body_ok v) hs)
      (AesCbc.X86.whole_ct (body_ok v) (body_ct v)) (crypt_noSp v) (crypt_stack v) v)
    final_implies

/-! ## With `save` on the stack

As AES-CFB's final functions, the code runs in a frame of 48 bytes
(`withStackScratchWiped 48 6 4`): the word standing for the return address,
a copy of the six arguments, `save`'s address, and `save`'s 16 bytes, which
it zeroes before returning. The code's calls use 52 bytes below it, so 100
in all. -/

theorem frameSat_pre : ∃ s, (Spec.Ofb.aesFinalSig.contract X86.abi (pre := finalPre X86.abi.ptrBits)
    (post := finalPost X86.abi.ptrBits) (stack := 100)).pre s := by
  have a0 : arg AesCbc.X86.sat 0 = 0x1000 := by decide
  have a1 : arg AesCbc.X86.sat 1 = 10 := by decide
  have a2 : arg AesCbc.X86.sat 2 = 0x2000 := by decide
  have a3 : arg AesCbc.X86.sat 3 = 0x3000 := by decide
  have a4 : arg AesCbc.X86.sat 4 = 0 := by decide
  have a5 : arg AesCbc.X86.sat 5 = 0x4000 := by decide
  have e : argAddr AesCbc.X86.sat 0 = 0x8004 := by decide
  have esp : AesCbc.X86.sat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Spec.Ofb.aesFinalSig, finalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp] using AesCbc.X86.sat

theorem cryptFinal_framed (v : BlocksImpl) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (cryptFinal v.enc v.suffix))
      (finalRoundsContract X86.abi 100) :=
  X86.Verified.stackScratchWiped (sig := Spec.Ofb.aesFinalSig) (nm := "save") (e := .u64) (n := 2)
    (pre := finalPre X86.abi.ptrBits) (post := finalPost X86.abi.ptrBits) (wa := false) (stack := 52)
    (bytes := 48) (words := 4) (cryptFinal_verified v) (by decide) (cryptFinal_noSp v) (cryptFinal_stack v)
    (by decide) (finalPre_local _) (finalPost_local _) (finalPost_localOut _) frameSat_pre

theorem cryptFinal_framed_spSafe (v : BlocksImpl) :
    (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (cryptFinal v.enc v.suffix)).all
      (fun i => !isa.writesSp i) = true :=
  framed_spSafe (cryptFinal_spSafe v)

end VG.Proof.AesOfb.X86
