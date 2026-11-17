module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTArguments
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttemptState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated

/-! ### `Ffdh.Arm.KeySearch.CallPublic`, which only this module used -/

section

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
  have a0₁ := call_stackArg (j := 0) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a1₁ := call_stackArg (j := 1) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a2₁ := call_stackArg (j := 2) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a3₁ := call_stackArg (j := 3) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a4₁ := call_stackArg (j := 4) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a5₁ := call_stackArg (j := 5) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a6₁ := call_stackArg (j := 6) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a0₂ := call_stackArg (j := 0) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a1₂ := call_stackArg (j := 1) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a2₂ := call_stackArg (j := 2) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a3₂ := call_stackArg (j := 3) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a4₂ := call_stackArg (j := 4) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a5₂ := call_stackArg (j := 5) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a6₂ := call_stackArg (j := 6) facts sp₂ mem₂ (by cases sampling <;> decide)
  simp only [callValue] at a0₁ a1₁ a2₁ a3₁ a4₁ a5₁ a6₁ a0₂ a1₂ a2₂ a3₂ a4₂ a5₂ a6₂
  have len : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have dlen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have inputs₁ := live₁.call_inputs room mem₁
  have inputs₂ := live₂.call_inputs room mem₂
  simp only [State.addr] at inputs₁ inputs₂
  cases sampling with
  | full =>
    sig_pub [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract, Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [args₁.x, args₁.xlen, args₁.y, args₁.ylen, args₂.x, args₂.xlen, args₂.y, args₂.ylen,
      a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, a6₁, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, a6₂, sp₁, sp₂, len, dlen]
    rw [inputs₁.1, inputs₁.2, inputs₂.1, inputs₂.2]
    change True ∧ (p.dom.map BitVec.toNat ++ [currentStatus p original₁ used] =
      p.dom.map BitVec.toNat ++ [currentStatus p original₂ used]) ∧ _
    rw [status]
    simp only [true_and]
  | vetted =>
    sig_pub [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract, Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [args₁.x, args₁.xlen, args₁.y, args₁.ylen, args₂.x, args₂.xlen, args₂.y, args₂.ylen,
      a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, a6₁, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, a6₂, sp₁, sp₂, len, dlen]
    rw [inputs₁.1, inputs₁.2, inputs₂.1, inputs₂.2]
    change True ∧ (p.dom.map BitVec.toNat ++ [currentStatus p original₁ used] =
      p.dom.map BitVec.toNat ++ [currentStatus p original₂ used]) ∧ _
    rw [status]
    simp only [true_and]
  | cached =>
    have a7₁ := call_stackArg (j := 7) facts sp₁ mem₁ (by decide)
    have a7₂ := call_stackArg (j := 7) facts sp₂ mem₂ (by decide)
    have a8₁ := call_stackArg (j := 8) facts sp₁ mem₁ (by decide)
    have a8₂ := call_stackArg (j := 8) facts sp₂ mem₂ (by decide)
    simp only [callValue] at a7₁ a8₁ a7₂ a8₂
    sig_pub [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract, Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [args₁.x, args₁.xlen, args₁.y, args₁.ylen, args₂.x, args₂.xlen, args₂.y, args₂.ylen,
      a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, a6₁, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, a6₂, a7₁, a8₁, a7₂, a8₂, sp₁, sp₂, len, dlen]
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

end

end


/-! A native key attempt leaks only its public domain and the disclosed
status at the current search point, for every arithmetic backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

private theorem call_ready {q : KeyPoint sampling} {u : State} (h : KeyCallCT q u) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧ Covers (callWr q.inputs) u.wr := by
  obtain ⟨_, s, live, _, _, _, room, args, mem, rest, syms⟩ := h
  have sp := rest.sp.trans live.call_sp
  exact ⟨call_pre live room args sp mem syms,
    live.covers_reads room rest.rd rest.wr, live.covers_writes rest.wr⟩

private theorem call_pub {q : KeyPoint sampling} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨_, _, live₁, statuses₁, keys₁, scalars₁, room₁, args₁, mem₁, rest₁, syms₁⟩ := h₁
  obtain ⟨_, _, live₂, statuses₂, keys₂, scalars₂, room₂, args₂, mem₂, rest₂, syms₂⟩ := h₂
  exact call_public live₁ live₂ room₁ args₁ args₂ (rest₁.sp.trans live₁.call_sp) (rest₂.sp.trans live₂.call_sp)
    mem₁ mem₂ syms₁ syms₂ ((attempt_status live₁ statuses₁ keys₁ scalars₁ room₁).trans
      (attempt_status live₂ statuses₂ keys₂ scalars₂ room₂).symm)

theorem attempt_call_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    RelCT isa (Two (KeyCallCT (sampling := sampling))) (.call backend.keyName backend.generateKey) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v ⟨q, h₁, h₂, _⟩ e₁ e₂
  have ct : RelCT isa (fun s t => KeyCallCT q s ∧ KeyCallCT q t)
      (.call backend.keyName backend.generateKey) (fun _ _ => True) := by
    refine VG.Arm.RelCT.call backend.generateKey_verified.1 backend.generateKey_verified.2.1
      (callRd q.inputs q.used) (callWr q.inputs) ?_
    intro a b ⟨ha, hb⟩
    obtain ⟨pre₁, reads₁, writes₁⟩ := call_ready ha
    obtain ⟨pre₂, reads₂, writes₂⟩ := call_ready hb
    exact ⟨pre₁, pre₂, call_pub ha hb, reads₁, writes₁, reads₂, writes₂⟩
  exact ct _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

theorem attempt_run_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    RelCT isa (Two (KeyReady (sampling := sampling)))
      ((VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor
  apply alloc_ct
  refine (RelCT.seq (two_post arguments_ct arguments_ready) (attempt_call_ct backend)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, sp⟩, rfl, rfl⟩
  refine ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, ?_⟩
  change s.sp - BitVec.ofNat 32 (GenerationPolicy.argumentBytes sampling) = t.sp - BitVec.ofNat 32 (GenerationPolicy.argumentBytes sampling)
  rw [sp]

theorem attempt_ready (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (q : KeyPoint sampling) (s : State) (h : KeyReady q s) :
    WP isa ((VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) s (KeyAttempted q) := by
  obtain ⟨⟨original, live, statuses⟩, keys, scalars, room⟩ := h
  exact WP.mono (attemptRun_ok backend q.inputs original s q.used q.keys q.scalars live room)
    fun _ ⟨ready, post⟩ => ⟨original, ready, statuses, keys, scalars, room, post⟩

end VG.Proof.Ffdh.Arm.KeySearch
