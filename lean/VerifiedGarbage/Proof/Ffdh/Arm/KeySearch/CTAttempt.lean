module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTArguments
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPublic
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttemptState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallConsts
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallRegions

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
      (VG.Impl.Ffdh.Arm.KeySearch.attemptRun (.call backend.keyName backend.generateKey)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptRun
  apply alloc_ct
  refine (RelCT.seq (two_post arguments_ct arguments_ready) (attempt_call_ct backend)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, sp⟩, rfl, rfl⟩
  refine ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, ?_⟩
  change s.sp - 32#32 = t.sp - 32#32
  rw [sp]

end VG.Proof.Ffdh.Arm.KeySearch
