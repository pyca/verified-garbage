module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPre
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallRegions
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves

/-! The shared key-attempt result is exactly the controller's current
attempt status and key pair, independent of its temporary call frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem KeyLive.call_inputs {p : KeyPublic sampling} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (mem : u.mem = callMem p used s.mem (callSp p)) :
    Spec.Rsa.bytesAt u.mem (State.addr p.dp) p.dlen = p.dom ∧
      Spec.Rsa.bytesAt u.mem (State.addr (p.rp + BitVec.ofNat 32 used)) p.len =
        ((keyRand p original).drop used).take p.len := by
  have frame := h.argument_frame mem
  refine ⟨(h.input.call_domain_frame frame).trans h.domain, ?_⟩
  have slice : ((Spec.Rsa.bytesAt u.mem (State.addr p.rp) p.randLen).drop used).take p.len =
      Spec.Rsa.bytesAt u.mem (off (State.addr p.rp) used) p.len :=
    VG.Proof.MlKem.bytesAt_slice u.mem (State.addr p.rp) room
  rw [h.input.tape_addr room, ← slice, h.input.call_random_frame frame, h.random]
  rfl

theorem call_post {p : KeyPublic sampling} {original s u t : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (args : ArgumentContext p used keys scalars u) (sp : u.sp = callSp p)
    (mem : u.mem = callMem p used s.mem (callSp p))
    (post : (GenerationPolicy.attemptContract sampling abi 176).post (callState p used u)
      (t.withRegions (callRd p used) (callWr p))) : AttemptPost p original used t := by
  have facts := h.input.callFacts room
  have a0 := call_stackArg (j := 0) facts sp mem (by cases sampling <;> decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by cases sampling <;> decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by cases sampling <;> decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by cases sampling <;> decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by cases sampling <;> decide)
  simp only [callValue] at a0 a1 a2 a3 a4
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have bytes := h.call_inputs room mem
  cases sampling <;>
    sig_post [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract,
      cachedGenerateKeyContract, cachedGenerateKeySig, generateKeySig, abi, argRegs,
      reduceClassify, Loc.val, State.addr] at post
  all_goals
    rw [BitVec.setWidth_append_eq_right] at post
    simp only [args.x, args.y, a0, a1, a2, a3, a4, nativeLen, domainLen] at post
    simp only [State.addr] at bytes
    rw [bytes.1, bytes.2] at post
    first
    | exact ⟨(post h.input.bounds.domainValid).1, (post h.input.bounds.domainValid).2⟩
    | exact ⟨post.1, post.2⟩

end VG.Proof.Ffdh.Arm.KeySearch
