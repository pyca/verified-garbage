module

public import VerifiedGarbage.Impl.AesOfb.Arm.Final
public import VerifiedGarbage.Proof.AesOfb.Final
public import VerifiedGarbage.Proof.AesCfb.Arm.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.AesOfb.Arm.Body
public import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Spec

/-!
# AES-OFB of a message's last piece on ARMv7

`cryptFinal_framed`: `vg_aes_ofb_final` (`Impl/AesOfb/Arm/Final.lean`) meets
`Proof.AesOfb.finalRoundsContract`, from which the shared contract follows
(`Proof.AesOfb.final_keyed`).

Its code is AES-CFB's final function around a call of the whole-block
AES-OFB function, so its proof is AES-CFB's (`Proof/AesCfb/Arm/Final.lean`),
for OFB as a `Mode` (`ofbMode`): `final_wp` runs it, for any mode, to what it
leaves before restoring the registers (`Done`); `final_ct` gives its
constant time. `ofbFinalArm` is AES-CFB's code contract with OFB's
postcondition, which `final_post` gives from `Done` by
`Proof.AesOfb.cryptFinal_of`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCfb.Arm (finalArm FPre Done fW fR fIv fD fL fN final_wp final_ct finalSat finalFrameSat
  encBlocks_stack)
open VG.Proof.AesCbc.Arm (modeArm)
open VG.Impl.AesOfb.Arm

/-- The code's contract, with the arguments `(schedule = r0, rounds = r1,
iv = r2, data = r3, len = [sp], scratch = [sp + 4], save = [sp + 8])`:
AES-CFB's final functions' (`finalArm`), with the data and the block at `iv`
as `Spec.Ofb.CryptFinal` says, by AES with the key schedule it is given. -/
def ofbFinalArm : Contract isa :=
  { finalArm true with
    post := fun s s' => Spec.Ofb.CryptFinal (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 16 s.mem
      s'.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) (stackArg s 0).toNat }

/-- The contract the frame needs: the shared one, with `save`, 40 bytes, as
a seventh argument, and 16 bytes of stack (the whole-block function's frame
and the one it pushes around its calls). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract Arm.abi Spec.Ofb.aesFinalSig "save" .u64 5 (finalPre Arm.abi.ptrBits)
    (finalPost Arm.abi.ptrBits) false 16

theorem final_implies : ofbFinalArm.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ofb.aesFinalSig, finalPre, finalPost, ofbFinalArm, finalArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finalSat

/-- `Spec.Ofb.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done ofbMode s₀ s₁) (hm : s'.mem = s₁.mem) :
    ofbFinalArm.post s₀ s' := by
  show Spec.Ofb.CryptFinal (ciphAt s₀.mem (State.addr (fW s₀)) (fR s₀)) 16 s₀.mem s'.mem
    (State.addr (fIv s₀)) (State.addr (fD s₀)) (fL s₀)
  have e := AesCbc.length_blocksAt s₀.mem (State.addr (fD s₀)) (fN s₀)
  have hb := h.blocks
  have ht := h.tail
  have hi := h.iv
  rw [ofbMode_out] at hb
  rw [ofbMode_chain, e] at ht hi
  exact cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact hb) (fun q hq => by rw [hm]; exact ht q hq)
    (by rw [hm]; exact hi)

/-- The whole-block function's frame: 8 bytes around each call of the
block function. -/
theorem crypt_stack : VG.Arm.FrameStack.armStack crypt = 8 := by
  simp only [crypt, Impl.AesCbc.Arm.whole, body, Impl.AesCbc.Arm.encFrame, VG.Arm.FrameStack.armStack,
    encBlocks_stack]
  decide

theorem final_correct (s : State) (hs : ofbFinalArm.pre s) :
    ∃ t s', Exec isa cryptFinal s t s' ∧ abiPreserved s s' ∧ ofbFinalArm.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ :=
    final_wp (M := ofbMode) (name := "vg_aes_ofb") (fun _ hs => AesCbc.Arm.whole_wp body_ok hs) crypt_stack
      (FPre.of (enc := true) hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩

theorem cryptFinal_verified : Verified Arm.target cryptFinal finalScratchContract :=
  Verified.of_correct final_correct
    (final_ct (enc := true) (fun _ hs => AesCbc.Arm.whole_wp body_ok hs) (AesCbc.Arm.whole_ct body_ok body_ct)
      crypt_stack)
    final_implies

/-! ## With `save` on the stack

As AES-CFB's final functions, the code runs in a frame of 56 bytes
(`withStackScratchWiped`): the copies of the two stack arguments, `save`'s
address, the word holding `lr`, and `save`'s 40 bytes, which it zeroes before
returning. Its calls use 16 bytes below it, so 72 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract Arm.abi 72).pre s := by
  implies_sat [finalRoundsContract, Spec.Ofb.aesFinalSig, finalPre, finalPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [finalFrameSat, finalSat] using finalFrameSat

/-- `cryptFinal`, with `save` on the stack (zeroed on return). -/
theorem cryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 cryptFinal)
      (finalRoundsContract Arm.abi 72) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Ofb.aesFinalSig) (nm := "save") (e := .u64) (n := 5)
    (pre := finalPre Arm.abi.ptrBits) (post := finalPost Arm.abi.ptrBits) (wa := false) (stack := 16)
    (m := 2) (bytes := 56) cryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (finalPre_local _) (finalPost_local _) (finalPost_localOut _) frameSat_pre

end VG.Proof.AesOfb.Arm
