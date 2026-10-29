module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySaved
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Safety
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFramed
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.WriteOutputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Derive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputStage
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBody
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextWorkspace
import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
import VerifiedGarbage.Proof.Mont.X86.Words
/-! # Callable native key assembly restores all cdecl registers and the return address -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Frame.lean`, which only this module imported.
section

/-! # The established input adapters preserve the runtime argument records -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Ws.afterFrame {s t : State} {B : Addr} {Z n N : Nat} {rs : List Reg}
    (h : Ws s B Z n N) (K : Keeps rs s t) (F : Frame [⟨B, Z⟩] s.mem t.mem)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Ws t B Z n N := by
  have frame : Frame [⟨off B 0, Z⟩] s.mem t.mem := by
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using F
  exact h.keep K (VG.Proof.RsaKeyGen.frame_outside frame
    (by have := h.old.workspace.nowrap; omega)) edi esp

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/IOFront.lean`, which only this module imported.
section

/-! # Small verified I/O adapters surround the shared arithmetic core -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input CoreOutcome WrittenCore)

theorem loadInputs_front {E : Environment} {p : BitVec 32} {s : State} (h : Input E s)
    (H : Ws s E.base E.size E.n 32) (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument s) :
    WP isa loadInputs s fun t => Loaded E s.mem t ∧ Ws t E.base E.size E.n 32 ∧
      Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  loadInputs_ok h H C

theorem writeCore_front {E : Environment} {sp : BitVec 32} {s : State} {e p q : Nat} (h : Input E s)
    (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size sp E.argument s)
    (apart : ∀ i < 7, (VG.Proof.RsaKeyGen.X86.KeyArgs.argsRegion sp).Disjoint (E.outputRegion i))
    (result : CoreOutcome E.base E.n e p q s.mem) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ WrittenCore E.outputs e p q t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  writeCore_ok h.outputs ⟨h.valid, C, fun i hi => by rw [h.valid.outputRegion hi]; exact apart i hi⟩ result

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Front.lean`, which only this module imported.
section

/-! # Shared arithmetic composes with the established input and output contracts -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input BodyOutcome stage_scratch_frame
  deriveArrays prepareArrays keyPartArrays)

theorem front_ok {E : Environment} {p : BitVec 32} {s : State} (h : Input E s) (H : Ws s E.base E.size E.n 32)
    (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument s)
    (apart : ∀ i < 7, (VG.Proof.RsaKeyGen.X86.KeyArgs.argsRegion p).Disjoint (E.outputRegion i)) :
    WP isa front s fun t => VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame (E.outputs.writes ++ [below p 52]) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  unfold front
  refine WP.seq (WP.mono (loadInputs_front h H C) fun u ⟨L, Hu, Fu, Ku⟩ => ?_)
  refine WP.seq (WP.mono (deriveLoaded_ok Hu widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 L.pBound L.qBound L.zero L.one L.loaded)
    fun v ⟨Hv, Ov, result, Kv⟩ => ?_)
  rw [L.eValue, L.pValue, L.qValue] at result
  have Iv := input_afterStage L.input Hu Hv.old Kv Ov
  have Cu := C.keep Ku Fu
  have spU : u.gpr .esp = p := Cu.sp
  have Fv : Frame ([⟨E.base, E.size⟩] ++ [below p 52]) u.mem v.mem := by
    rw [← spU]
    exact Ov.toFrame fun _ _ O =>
      stage_scratch_frame L.input.ws (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) O
  have Cv := Cu.keepBelow Kv Fv
  refine WP.mono (writeCore_front Iv Cv apart result) fun t ⟨ht, written, Ft, Kt⟩ => ?_
  refine ⟨ht, written, ?_, Ku.trans (Kv.trans Kt)⟩
  have wsIn : E.workspaceRegion ∈ E.outputs.writes ++ [below p 52] :=
    List.mem_append_left _ List.mem_cons_self
  have prefixFrame : Frame (E.outputs.writes ++ [below p 52]) s.mem v.mem :=
    (Fu.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact wsIn)).trans (Fv.mono (by
      intro r hr
      simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact wsIn
      · exact List.mem_append_right _ (List.mem_singleton_self _)))
  exact prefixFrame.trans (Ft.mono fun r hr => List.mem_append_left _ hr)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Body.lean`, which only this module imported.
section

/-! # Native cdecl argument entry composes with the complete key body -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment EntryInput Input BodyOutcome bodyClob outs_scratch_frame)


theorem enter_input_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.enter s fun t =>
      Input E t ∧ Ws t E.base E.size E.n 32 ∧ Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .edi] s t ∧
      VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument t := by
  refine WP.mono (KeyArgs.enter_ok I.arguments) fun t ⟨C, header, O, K⟩ => ?_
  have dimensions := v.widths
  have ws : VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 :=
    ⟨C.scratch, v.bankFit, by omega, by omega⟩
  have input : Input E t := by
    refine ⟨v, ws, header, ?_, ?_⟩
    · intro i hi
      rw [K.2.2]
      exact I.outWrite i hi
    · rw [K.2.1, K.2.2]
      exact I.exponentRead
  have frame : Frame [E.workspaceRegion] s.mem t.mem :=
    outs_scratch_frame (by have := C.scratch.nowrap; omega)
      (Outs.of_outside (rs := [(0, 72)]) O (List.mem_singleton_self _))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; change 0 + 72 ≤ E.size; exact I.arguments.header)
  exact ⟨input, context_workspace v C ws, frame, K, C⟩

theorem body_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.body s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame (E.outputs.writes ++ [below p 52]) s.mem t.mem ∧ Keeps bodyClob s t := by
  unfold VG.Impl.RsaKeyGen.X86.KeyRuntime.body
  refine WP.seq (WP.mono (enter_input_ok v I) fun a ⟨Ia, Ha, F, K, Ca⟩ => ?_)
  refine WP.mono (front_ok Ia Ha Ca I.argsOutput) fun t ⟨ht, result, Ft, Kt⟩ => ?_
  unfold BodyOutcome at result
  rw [Ia.exponent_preserved F, Ia.output_preserved (by decide : 2 < 7) F,
    Ia.output_preserved (by decide : 3 < 7) F] at result
  refine ⟨ht, result, ?_, (K.mono (by unfold bodyClob; decide)).trans (Kt.mono (by unfold bodyClob; decide))⟩
  exact (F.mono (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact List.mem_append_left _ List.mem_cons_self)).trans Ft

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86
open VG.Proof.RsaKeyGen.X86.Key (contract call_layout entry_input call_valid callSp bodyClob
  BodyOutcome callEnvironment writes_reserved writes_return)

/-- The registers the frame saves lie above the stack a call of the inverse uses. -/
theorem saved_below {s : State} (h : contract.pre s) :
    (⟨(callSp s).setWidth 64, 20⟩ : Region).Disjoint (below (callSp s) 52) := by
  have A := call_layout h
  have low : 52 ≤ (callSp s).toNat := by rw [A.privateNat]; have := A.low; omega
  unfold below
  rw [Taint.sub_setWidth low]
  exact Offset.base_disjoint_below _ (by decide)

/-- `Key.saved_read`, when the body also writes the stack a call uses. -/
theorem saved_read {s t : State} (h : contract.pre s)
    (F : Frame ((callEnvironment s).outputs.writes ++ [below (callSp s) 52]) (Compact.entered s).mem t.mem)
    {i : Nat} (hi : i < 4) :
    t.mem.readW (addr (callSp s) (4 * i)) 32 =
      s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have A := call_layout h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have pFit : (callSp s).toNat + 16 ≤ 2 ^ 32 := by
    rw [A.privateNat]
    have := (s.gpr .esp).isLt
    omega
  have same := F.readW (r := (⟨(callSp s).setWidth 64, 16⟩ : Region))
    (a := addr (callSp s) (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ((writes_reserved h r hr).sub_right A.savedSub).symm
      · obtain rfl := List.mem_singleton.mp hr
        exact (saved_below h).sub_left (Region.sub_prefix (by decide))) (by decide)
  have word := pushed_word (rs := Compact.savedRegisters) (s := s) (by decide) fit hi
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [Compact.entered, pushed_esp] at word
  exact same.trans word

/-- `Key.return_read`, when the body also writes the stack a call uses. -/
theorem return_read {s t : State} (h : contract.pre s)
    (F : Frame ((callEnvironment s).outputs.writes ++ [below (callSp s) 52]) (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have A := call_layout h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have ret : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Sub ⟨(callSp s).setWidth 64, 20⟩ := by
    have e : (s.gpr .esp).setWidth 64 = (callSp s).setWidth 64 + BitVec.ofNat 64 16 := by
      unfold callSp
      rw [Taint.sub_setWidth fit, BitVec.sub_add_cancel]
    rw [e]
    exact Offset.sub_base _ (by decide)
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4)
    (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact writes_return h r hr
      · obtain rfl := List.mem_singleton.mp hr
        exact (saved_below h).sub_left ret) (by decide)
  have pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  exact same.trans (pushed.readW (w := 32) (Region.contains_self _ _)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide))

theorem framed_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s fun t =>
      abiPreserved s t ∧ BodyOutcome (callEnvironment s) (Compact.entered s).mem t := by
  have A := call_layout h
  have I := entry_input h
  have savedFit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have inner : NoSp (.seq VG.Impl.RsaKeyGen.X86.KeyRuntime.body (.block Compact.restoreRegs)) :=
    VG.Proof.RsaKeyGen.X86.KeyNoSp.sequence body_noSp (NoSp.of_all (by rfl))
  unfold VG.Impl.RsaKeyGen.X86.KeyRuntime.code
  refine WP.frame (rs := VG.Proof.Mont.X86.Compact.savedRegisters) (by decide) (by decide) (by decide) savedFit inner ?_
  refine WP.seq (WP.mono (body_ok (call_valid h) I) fun t ⟨_, R, F, K⟩ => ?_)
  have sp : t.gpr .esp = callSp s := (K.1 .esp (by unfold bodyClob; decide)).trans I.arguments.sp
  have pFit : (callSp s).toNat + 16 ≤ 2 ^ 32 := by
    rw [A.privateNat]
    have := (s.gpr .esp).isLt
    omega
  have read (i : Nat) (hi : i < 4) : readSrc t (.mem (at_ .esp (4 * i))) = some
      (s.gpr (VG.Proof.Mont.X86.Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (addr (callSp s) (4 * i)) 4
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      change (⟨(callSp s).setWidth 64, 16⟩ : Region).Contains (addr (callSp s) (4 * i)) 4
      rw [addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, saved_read h F hi]
  refine WP.mono (VG.Proof.Mont.X86.Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, memory, keep⟩
  have sp' : u.gpr .esp = callSp s := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show VG.Proof.Mont.X86.Compact.savedRegisters.length = 4 from rfl,
        VG.Proof.Mont.X86.Compact.popped_four_value, sp', memory]
      exact saved_read h F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact ebp
    · rw [popped_esp, sp']
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, memory]
    exact return_read h F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, memory]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
