module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPost
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords

/-! At equal public search positions, the selected attempt sees equal
public arguments, domain bytes, and its disclosed attempt status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

theorem call_public_plain {p : KeyPublic sampling} {used keys scalars : Nat} {s₁ s₂ original₁ original₂ u₁ u₂ : State}
    (live₁ : KeyLive p original₁ used keys scalars s₁) (live₂ : KeyLive p original₂ used keys scalars s₂)
    (room : used + p.len ≤ p.randLen)
    (args₁ : ArgumentContext p used keys scalars u₁) (args₂ : ArgumentContext p used keys scalars u₂)
    (sp₁ : u₁.sp = callSp p) (sp₂ : u₂.sp = callSp p)
    (mem₁ : u₁.mem = callMem p used s₁.mem (callSp p)) (mem₂ : u₂.mem = callMem p used s₂.mem (callSp p))
    (status : currentStatus p original₁ used = currentStatus p original₂ used) :
    (GenerationPolicy.attemptContract sampling abi 176).pub (callState p used u₁) (callState p used u₂) := by
  have facts := live₁.input.callFacts room
  have a0₁ := call_stackArg (j := 0) facts sp₁ mem₁ (by decide)
  have a1₁ := call_stackArg (j := 1) facts sp₁ mem₁ (by decide)
  have a2₁ := call_stackArg (j := 2) facts sp₁ mem₁ (by decide)
  have a3₁ := call_stackArg (j := 3) facts sp₁ mem₁ (by decide)
  have a4₁ := call_stackArg (j := 4) facts sp₁ mem₁ (by decide)
  have a5₁ := call_stackArg (j := 5) facts sp₁ mem₁ (by decide)
  have a6₁ := call_stackArg (j := 6) facts sp₁ mem₁ (by decide)
  have a0₂ := call_stackArg (j := 0) facts sp₂ mem₂ (by decide)
  have a1₂ := call_stackArg (j := 1) facts sp₂ mem₂ (by decide)
  have a2₂ := call_stackArg (j := 2) facts sp₂ mem₂ (by decide)
  have a3₂ := call_stackArg (j := 3) facts sp₂ mem₂ (by decide)
  have a4₂ := call_stackArg (j := 4) facts sp₂ mem₂ (by decide)
  have a5₂ := call_stackArg (j := 5) facts sp₂ mem₂ (by decide)
  have a6₂ := call_stackArg (j := 6) facts sp₂ mem₂ (by decide)
  simp only [callValue] at a0₁ a1₁ a2₁ a3₁ a4₁ a5₁ a6₁ a0₂ a1₂ a2₂ a3₂ a4₂ a5₂ a6₂
  have len : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have dlen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have inputs₁ := live₁.call_inputs room mem₁
  have inputs₂ := live₂.call_inputs room mem₂
  simp only [State.addr] at inputs₁ inputs₂
  sig_pub [GenerationPolicy.attemptContract, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [args₁.x, args₁.xlen, args₁.y, args₁.ylen, args₂.x, args₂.xlen, args₂.y, args₂.ylen,
    a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, a6₁, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, a6₂, sp₁, sp₂, len, dlen]
  rw [inputs₁.1, inputs₁.2, inputs₂.1, inputs₂.2]
  change True ∧ (p.dom.map BitVec.toNat ++ [currentStatus p original₁ used] =
    p.dom.map BitVec.toNat ++ [currentStatus p original₂ used]) ∧ _
  rw [status]
  simp only [true_and]

theorem call_public {p : KeyPublic sampling} {used keys scalars : Nat}
    {s₁ s₂ original₁ original₂ u₁ u₂ : State}
    (live₁ : KeyLive p original₁ used keys scalars s₁) (live₂ : KeyLive p original₂ used keys scalars s₂)
    (room : used + p.len ≤ p.randLen)
    (args₁ : ArgumentContext p used keys scalars u₁) (args₂ : ArgumentContext p used keys scalars u₂)
    (sp₁ : u₁.sp = callSp p) (sp₂ : u₂.sp = callSp p)
    (mem₁ : u₁.mem = callMem p used s₁.mem (callSp p)) (mem₂ : u₂.mem = callMem p used s₂.mem (callSp p))
    (syms₁ : u₁.syms = s₁.syms) (syms₂ : u₂.syms = s₂.syms)
    (status : currentStatus p original₁ used = currentStatus p original₂ used) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pub
      (callState p used u₁) (callState p used u₂) := by
  apply selected_attempt_pub.mpr
  refine ⟨call_public_plain live₁ live₂ room args₁ args₂ sp₁ sp₂ mem₁ mem₂ status, ?_⟩
  have ptr₁ := (KeyConstants.tablePtr_of_syms (sampling := sampling) syms₁).trans live₁.tablePtr
  have ptr₂ := (KeyConstants.tablePtr_of_syms (sampling := sampling) syms₂).trans live₂.tablePtr
  change KeyConstants.tablePtr sampling u₁ = KeyConstants.tablePtr sampling u₂
  exact ptr₁.trans ptr₂.symm


end VG.Proof.Ffdh.Arm.KeySearch
