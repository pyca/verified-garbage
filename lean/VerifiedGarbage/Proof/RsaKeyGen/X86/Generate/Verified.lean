module

public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Verified
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFrameResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Safety
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ReadonlyTrace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.WriteOutputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBody
import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
import VerifiedGarbage.Proof.Mont.X86.Words
import Mathlib.Algebra.Group.Nat.Defs
import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBodyTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputReady
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OutputPublic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
import Init.Core
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Correct
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.KeyRun
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Framework.RelSplit
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Loop
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Correct
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.KeyRun
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Loop

/-! ### `RsaKeyGen.X86.KeyRuntime.Verified`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeySatisfiable`, which only this module used -/

section

/-! # A disjoint native caller satisfies the complete key-generation precondition -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 64
  | 2 => 0x2000
  | 3 => 64
  | 4 => 0x3000
  | 5 => 32
  | 6 => 0x4000
  | 7 => 32
  | 8 => 0x5000
  | 9 => 32
  | 10 => 0x6000
  | 11 => 32
  | 12 => 0x7000
  | 13 => 32
  | 14 => 0x8000
  | 15 => 1
  | 16 => 0x10000
  | _ => 1056

def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 72 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else 0

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x8000, 1⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩,
    ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 32⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 72⟩]

theorem sat_arguments (i : Nat) (hi : i < 18) : arg satState i = satArgument i := by
  interval_cases i <;> decide +kernel

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, keyStack, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide),
    sat_arguments 9 (by decide), sat_arguments 10 (by decide), sat_arguments 11 (by decide),
    sat_arguments 12 (by decide), sat_arguments 13 (by decide), sat_arguments 14 (by decide),
    sat_arguments 15 (by decide), sat_arguments 16 (by decide), sat_arguments 17 (by decide)]
  sig_and_intros
  all_goals first
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.RsaKeyGen.primeLenValid; decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.Framed`, which only this module used -/

section

/-! # Callable native key assembly restores all cdecl registers and the return address -/

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
  obtain Iv := input_afterStage L.input Hu Hv.old Kv Ov
  obtain Cu := C.keep Ku Fu
  have spU : u.gpr .esp = p := Cu.sp
  obtain Fv : Frame ([⟨E.base, E.size⟩] ++ [below p 52]) u.mem v.mem := by
    rw [← spU]
    exact Ov.toFrame fun _ _ O =>
      stage_scratch_frame L.input.ws (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) O
  obtain Cv := Cu.keepBelow Kv Fv
  refine WP.mono (writeCore_front Iv Cv apart result) fun t ⟨ht, written, Ft, Kt⟩ => ?_
  refine ⟨ht, written, ?_, Ku.trans (Kv.trans Kt)⟩
  obtain wsIn : E.workspaceRegion ∈ E.outputs.writes ++ [below p 52] :=
    List.mem_append_left _ List.mem_cons_self
  obtain prefixFrame : Frame (E.outputs.writes ++ [below p 52]) s.mem v.mem :=
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
  obtain ws : VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 :=
    ⟨C.scratch, v.bankFit, by omega, by omega⟩
  obtain input : Input E t := by
    refine ⟨v, ws, header, ?_, ?_⟩
    · intro i hi
      rw [K.2.2]
      exact I.outWrite i hi
    · rw [K.2.1, K.2.2]
      exact I.exponentRead
  obtain frame : Frame [E.workspaceRegion] s.mem t.mem :=
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
  obtain A := call_layout h
  obtain low : 52 ≤ (callSp s).toNat := by rw [A.privateNat]; have := A.low; omega
  unfold below
  rw [Taint.sub_setWidth low]
  exact Offset.base_disjoint_below _ (by decide)

/-- The saved registers' words, when the body also writes the stack a call uses. -/
theorem saved_read {s t : State} (h : contract.pre s)
    (F : Frame ((callEnvironment s).outputs.writes ++ [below (callSp s) 52]) (Compact.entered s).mem t.mem)
    {i : Nat} (hi : i < 4) :
    t.mem.readW (addr (callSp s) (4 * i)) 32 =
      s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  obtain A := call_layout h
  obtain fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  obtain pFit : (callSp s).toNat + 16 ≤ 2 ^ 32 := by
    rw [A.privateNat]
    have := (s.gpr .esp).isLt
    omega
  obtain same := F.readW (r := (⟨(callSp s).setWidth 64, 16⟩ : Region))
    (a := addr (callSp s) (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ((writes_reserved h r hr).sub_right A.savedSub).symm
      · obtain rfl := List.mem_singleton.mp hr
        exact (saved_below h).sub_left (Region.sub_prefix (by decide))) (by decide)
  obtain word := pushed_word (rs := Compact.savedRegisters) (s := s) (by decide) fit hi
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [Compact.entered, pushed_esp] at word
  exact same.trans word

/-- The return address's word, when the body also writes the stack a call uses. -/
theorem return_read {s t : State} (h : contract.pre s)
    (F : Frame ((callEnvironment s).outputs.writes ++ [below (callSp s) 52]) (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  obtain A := call_layout h
  obtain fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  obtain ret : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Sub ⟨(callSp s).setWidth 64, 20⟩ := by
    obtain e : (s.gpr .esp).setWidth 64 = (callSp s).setWidth 64 + BitVec.ofNat 64 16 := by
      unfold callSp
      rw [Taint.sub_setWidth fit, BitVec.sub_add_cancel]
    rw [e]
    exact Offset.sub_base _ (by decide)
  obtain same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4)
    (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact writes_return h r hr
      · obtain rfl := List.mem_singleton.mp hr
        exact (saved_below h).sub_left ret) (by decide)
  obtain pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  obtain separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  exact same.trans (pushed.readW (w := 32) (Region.contains_self _ _)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide))

theorem framed_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s fun t =>
      abiPreserved s t ∧ BodyOutcome (callEnvironment s) (Compact.entered s).mem t := by
  obtain A := call_layout h
  obtain I := entry_input h
  obtain savedFit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  obtain inner : NoSp (.seq VG.Impl.RsaKeyGen.X86.KeyRuntime.body (.block Compact.restoreRegs)) :=
    VG.Proof.RsaKeyGen.X86.KeyNoSp.sequence body_noSp (NoSp.of_all (by rfl))
  unfold VG.Impl.RsaKeyGen.X86.KeyRuntime.code
  refine WP.frame (rs := VG.Proof.Mont.X86.Compact.savedRegisters) (by decide) (by decide) (by decide) savedFit inner ?_
  refine WP.seq (WP.mono (body_ok (call_valid h) I) fun t ⟨_, R, F, K⟩ => ?_)
  obtain sp : t.gpr .esp = callSp s := (K.1 .esp (by unfold bodyClob; decide)).trans I.arguments.sp
  obtain pFit : (callSp s).toNat + 16 ≤ 2 ^ 32 := by
    rw [A.privateNat]
    have := (s.gpr .esp).isLt
    omega
  have read (i : Nat) (hi : i < 4) : readSrc t (.mem (at_ .esp (4 * i))) = some
      (s.gpr (VG.Proof.Mont.X86.Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    obtain access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
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
  obtain sp' : u.gpr .esp = callSp s := (keep.1 .esp (by decide)).trans sp
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

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.OutputTiming`, which only this module used -/

section

/-! # The outputs' trace depends only on the arguments and the declared retry bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kOk kStatus outputIndex)
open VG.Proof.Mont.X86.Dynamic (workspaceTaint)
open VG.Proof.RsaKeyGen.X86.Key (Environment Input ExportState OutputPair outputIndex_bound outputIndex_zero)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

theorem zero_runs {E : Environment} {sp : BitVec 32} {s : State} (A : OutputArgs E sp s)
    (h : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32) :
    WP isa (zero .modulus (arr aZero)) (readonly s E.base E.size) fun _ => True := by
  obtain fits := h.arr_fit (j := aZero) (by decide)
  exact WP.mono (zero_ok (context_workspace A.valid A.context h).readonly .modulus (arr aZero)
    (by change arr E.n aZero + _ ≤ E.size; exact fits)) fun _ _ => trivial

theorem setup_runs {E : Environment} {sp : BitVec 32} {s : State} {j pointer length : Nat}
    (A : OutputArgs E sp s) (h : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32)
    (hj : j < 32) (nonzero : j ≠ aZero) (hp : pointer < 18) (hl : length < 18)
    (bit : slot s.mem E.base kOk ≤ 1) :
    WP isa (arraySetup j pointer length) (readonly s E.base E.size) fun _ => True := by
  obtain H := (context_workspace A.valid A.context h).readonly
  obtain C := context_readonly A.context
  obtain fits := h.arr_fit hj
  obtain fit64 := h.fit64 hj
  have head := h.hdr_le
  have nowrap := h.workspace.nowrap
  unfold S at fits fit64
  unfold arraySetup
  refine WP.seq (WP.mono (sel_ok H hj (by decide) hj (by decide) bit (Or.inl nonzero))
    fun u ⟨Hu, Ou, _, Ku⟩ => ?_)
  obtain raw : Outside E.base (arr E.n j) (S E.n) (readonly s E.base E.size).mem u.mem := by
    intro a ha
    apply Ou a
    intro r hr
    change r ∈ [(arr E.n j, S E.n)] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact ha
  obtain ownFrame := VG.Proof.Bignum.outside_frame raw (by unfold S; exact fit64)
  obtain Cu := C.keepFar Ku ownFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.context.separate.sub_right (Offset.sub_base E.base (by unfold S; exact fits)))
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (context_argument Cu (i := pointer) hp).readSrc fun a Aa _ => ?_
  refine wp_movS ((context_argument Cu (i := length) hl).keep Aa.keeps (by decide)
    (by rw [Aa.mem]; exact Outside.refl _ _ _ _)).readSrc fun b Bb _ => ?_
  obtain Hb := Hu.keep ((Aa.keeps.mono (rs' := [.ebx, .ecx]) (by decide)).trans (Bb.keeps.mono (by decide)))
    (by rw [Bb.mem, Aa.mem]; exact Outside.refl _ _ _ _)
  refine Hb.ptr_ok (arr j) (r := .esi) (t := .edx) (by decide) (by decide)
    (by change arr E.n j < _; omega_using [fits, nowrap]) fun c _ _ _ => ?_
  exact wp_addS rfl fun d _ _ => wp_subS rfl fun e _ _ => WP.block_nil trivial

/-- One run's state between outputs. -/
structure RtExport (E : Environment) (sp : BitVec 32) (s : State) : Prop where
  state : ExportState E s
  args : OutputArgs E sp s

theorem zeroExport_ok {E : Environment} {sp : BitVec 32} {s : State} (h : Input E s)
    (bit : slot s.mem E.base kOk ≤ 1) (A : OutputArgs E sp s) :
    WP isa (zero .modulus (arr aZero)) s fun t => RtExport E sp t ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  obtain H := context_workspace A.valid A.context h.ws
  obtain fits := h.ws.arr_fit (j := aZero) (by decide)
  obtain fit64 := h.ws.fit64 (j := aZero) (by decide)
  refine WP.mono (zero_ok H .modulus (arr aZero) (by change arr E.n aZero + _ ≤ E.size; exact fits))
    fun t ⟨Ht, O, zero, K⟩ => ?_
  change Outside E.base (arr E.n aZero) (S E.n) s.mem t.mem at O
  change val32 t.mem E.base (arr E.n aZero) (E.n + 2) = 0 at zero
  obtain clear : Keep E.base E.n [aZero] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O) (by unfold S; omega_using []) (by simp)
  obtain header : ∀ d, d + 4 ≤ hdr → slot t.mem E.base d = slot s.mem E.base d :=
    fun d hd => clear.slot hd (by simp)
  obtain input : Input E t := h.keep Ht.old K (by
    intro d hd
    apply BitVec.eq_of_toNat_eq
    exact header d (by unfold hdr; omega_using [hd]))
  obtain lowZero : num t.mem E.base E.n aZero = 0 := by
    obtain Z := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := E.n) (by omega_using [])
    simpa only [Nat.mul_zero, Nat.add_zero] using Z
  obtain ownFrame := VG.Proof.Bignum.outside_frame O fit64
  refine ⟨⟨⟨input, lowZero, by rw [header kOk (by decide)]; exact bit⟩,
    ⟨A.valid, A.context.keepFar K ownFrame ?_, A.apart⟩⟩, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact A.context.separate.sub_right (Offset.sub_base E.base fits)

theorem RtExport.port_ok {E : Environment} {sp : BitVec 32} {s : State} (h : RtExport E sp s)
    {i : Nat} (hi : i < 7) :
    WP isa (writePort i) s fun t => RtExport E sp t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let accept := decide (slot s.mem E.base kOk = 1)
  obtain mask : slot s.mem E.base kOk = if accept then 1 else 0 := by
    unfold accept
    split <;> have := h.state.bit <;> simp_all <;> omega_arith
  have g := h.state.input.outputs
  refine WP.mono (writeArray_ok (p := E.outputs.pointer i) (len := E.outputs.length i) h.args.valid
    h.state.input.ws h.args.context (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi)) (by omega_using [hi]) (by omega_using [hi])
    rfl
    (by simp only [VG.Proof.RsaKeyGen.X86.Key.OutputGeometry.length, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)
    (g.valid.lengthPositive i hi) (g.valid.lengthBound i hi) (g.valid.fit i hi)
    (g.writable i hi) (g.valid.scratchApart i hi) (h.args.apart i hi) h.state.zero accept mask)
    fun t ⟨ht, Ct, _, _, header, other, K⟩ => ?_
  obtain input : Input E t := h.state.input.keep ht K (by
    intro d hd
    apply BitVec.eq_of_toNat_eq
    exact header d (by unfold hdr; omega_using [hd]))
  refine ⟨⟨⟨input, (other aZero (by decide) (outputIndex_zero hi)).trans h.state.zero, ?_⟩,
    ⟨h.args.valid, Ct, h.args.apart⟩⟩, K⟩
  rw [header kOk (by decide)]
  exact h.state.bit

structure RtExportPair (E : Environment) (sp : BitVec 32) (s t : State) : Prop where
  left : RtExport E sp s
  right : RtExport E sp t
  stack : s.gpr .esp = t.gpr .esp
  source : s.gpr .esi = t.gpr .esi

def OutputStart (E : Environment) (sp : BitVec 32) (s t : State) : Prop :=
  OutputPair E s t ∧ OutputArgs E sp s ∧ OutputArgs E sp t

theorem zeroOutputs_trace (E : Environment) (sp : BitVec 32) :
    RelCT isa (OutputStart E sp) (zero .modulus (arr aZero)) (RtExportPair E sp) := by
  intro s t tr ur u v P A C
  obtain ⟨⟨inputs, agree, leftBit, rightBit⟩, leftArgs, rightArgs⟩ := P
  obtain trace := (readonly_trace zeroOutputs_public
    (context_workspace leftArgs.valid leftArgs.context inputs.left.ws)
    (context_workspace rightArgs.valid rightArgs.context inputs.right.ws) leftArgs.context rightArgs.context
    (zero_runs leftArgs inputs.left.ws) (zero_runs rightArgs inputs.right.ws) A C).1
  obtain ⟨left, KS⟩ := wp_result (zeroExport_ok inputs.left leftBit leftArgs) A
  obtain ⟨right, KT⟩ := wp_result (zeroExport_ok inputs.right rightBit rightArgs) C
  refine ⟨trace, left, right, ?_, ?_⟩
  · rw [KS.1 .esp (by decide), KT.1 .esp (by decide)]
    exact inputs.stack
  · rw [KS.1 .esi (by decide), KT.1 .esi (by decide)]
    exact agree.reg (by rfl : VG.X86.Taint.pub (workspaceTaint true) .esi = true)

theorem setup_checked {i : Nat} (hi : i < 7) :
    FromInputs (arraySetup (outputIndex i) (2 * i) (2 * i + 1)) portTaint := by
  obtain _ | _ | _ | _ | _ | _ | _ | i := i
  · exact setup0_public
  · exact setup1_public
  · exact setup2_public
  · exact setup3_public
  · exact setup4_public
  · exact setup5_public
  · exact setup6_public
  · omega

theorem port_trace (E : Environment) (sp : BitVec 32) {i : Nat} (hi : i < 7) :
    RelCT isa (RtExportPair E sp) (writePort i) (RtExportPair E sp) := by
  intro s t tr ur u v P A C
  obtain ⟨left, KS⟩ := wp_result (P.left.port_ok hi) A
  obtain ⟨right, KT⟩ := wp_result (P.right.port_ok hi) C
  obtain stack : u.gpr .esp = v.gpr .esp := by
    rw [KS.1 .esp (by decide), KT.1 .esp (by decide)]
    exact P.stack
  unfold writePort writeArray at A C
  cases A with
  | seq A1 A2 =>
  cases C with
  | seq C1 C2 =>
  obtain ⟨setupTrace, regs⟩ := readonly_trace (setup_checked hi)
    (context_workspace P.left.args.valid P.left.args.context P.left.state.input.ws)
    (context_workspace P.right.args.valid P.right.args.context P.right.state.input.ws)
    P.left.args.context P.right.args.context
    (setup_runs (pointer := 2 * i) (length := 2 * i + 1) P.left.args P.left.state.input.ws (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi))
      (by omega_using [hi]) (by omega_using [hi]) P.left.state.bit)
    (setup_runs (pointer := 2 * i) (length := 2 * i + 1) P.right.args P.right.state.input.ws (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi))
      (by omega_using [hi]) (by omega_using [hi]) P.right.state.bit) A1 C1
  obtain start : VG.X86.Taint.Agree (τr [.edi, .esp, .ebx, .ecx, .esi]) _ _ := agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact regs _ rfl)
  obtain ⟨hint, out, checked, lower⟩ := reverse_public
  obtain ⟨copyTrace, copied⟩ := VG.Taint.check_sound checked start A2 C2
  obtain final := sseTaint.le_sound lower copied
  refine ⟨by rw [setupTrace, copyTrace], left, right, stack, final.reg (by rfl)⟩

theorem ports_trace (E : Environment) (sp : BitVec 32) (i count : Nat) (bound : i + count ≤ 7) :
    RelCT isa (RtExportPair E sp) (writePorts i count) (RtExportPair E sp) := by
  induction count generalizing i with
  | zero => exact RelCT.block_nil (fun _ _ P => P)
  | succ count ih =>
    exact RelCT.seq (port_trace E sp (by omega_using [bound])) (ih (i + 1) (by omega_using [bound]))

theorem status_trace (E : Environment) (sp : BitVec 32) :
    RelCT isa (RtExportPair E sp) (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kStatus))])
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  obtain checked : VG.Proof.Rsa.X86.Keys.KeyPublic (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kStatus))]) :=
    ⟨.block [], workspaceTaint true, rfl, rfl⟩
  refine (VG.Proof.RsaKeyGen.X86.Key.key_public_trace checked).mono (fun s t P => ?_) (fun _ _ P => P)
  change VG.X86.Taint.Agree (τr [.edi, .esi]) s t
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact BitVec.eq_of_toNat_eq (P.left.state.input.ws.workspace.edi_toNat.trans
      P.right.state.input.ws.workspace.edi_toNat.symm)
  · exact P.source

theorem writeOutputs_trace (E : Environment) (sp : BitVec 32) :
    RelCT isa (OutputStart E sp) writeOutputs (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold writeOutputs seqs
  exact RelCT.seq (zeroOutputs_trace E sp) (RelCT.seq (ports_trace E sp 0 7 (by decide)) (status_trace E sp))

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyFrameTiming`, which only this module used -/

section

/-! # The outer native key frame preserves trace equivalence -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def FramedPair (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop :=
  BodyPair E sp e p q p' q' (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyPublicLeak`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.KeyPublic`, which only this module used -/

section

/-! # The shared key contract publishes its arguments, exponent bytes and result status -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def callEBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (callEnvironment s).exponentRegion.base (callEnvironment s).exponentRegion.len
def callKeyStatus (s : State) : Nat := Proof.RsaKeyGen.keyStatus (encodedOperation (callEnvironment s) s.mem)

structure PublicInputs (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  arguments : ∀ i < 18, arg s i = arg t i
  observations : (callEBytes s).map (·.toNat) ++ [callKeyStatus s] =
    (callEBytes t).map (·.toNat) ++ [callKeyStatus t]

theorem public_inputs {s t : State} (H : contract.pub s t) : PublicInputs s t := by
  sig_pub [contract, keyStack, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> with_reducible assumption
  · dsimp only [callEBytes, callKeyStatus, encodedOperation, callEnvironment,
      Environment.exponentRegion, Environment.outputRegion, Environment.outputLength]
    simp only [Nat.reduceMul, Nat.reduceLT, ite_true, ite_false]
    with_reducible assumption

theorem PublicInputs.environment {s t : State} (P : PublicInputs s t) : callEnvironment s = callEnvironment t := by
  simp only [callEnvironment, P.arguments 16 (by decide), P.arguments 17 (by decide),
    P.arguments 5 (by decide), P.arguments 14 (by decide), P.arguments 15 (by decide)]
  congr 1
  funext i
  by_cases hi : i < 7
  · simp only [hi, ite_true]
    exact P.arguments (2 * i) (by omega_using [hi])
  · simp only [hi, ite_false]

theorem PublicInputs.exponent {s t : State} (P : PublicInputs s t) : callEBytes s = callEBytes t := by
  obtain lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    simp only [List.length_map, callEBytes, VG.Proof.Bignum.bytesAt_length, P.environment]
  exact VG.Proof.RsaKeyGen.map_toNat_inj (List.append_inj P.observations lengths).1

theorem PublicInputs.status {s t : State} (P : PublicInputs s t) : callKeyStatus s = callKeyStatus t := by
  obtain lengths : ((callEBytes s).map (·.toNat)).length = ((callEBytes t).map (·.toNat)).length := by
    rw [P.exponent]
  exact List.singleton_inj.mp (List.append_inj P.observations lengths).2

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Equal shared observations give the exponent and retry equality used by native timing -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyStatusRetry.lean`, which only this module imported.
section

/-! # The shared encoded status releases exactly the numeric retry branch -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG

theorem status_retry_iff {E : Environment} (v : E.Valid) (m : Mem) :
    Proof.RsaKeyGen.keyStatus (encodedOperation E m) = 2 ↔
      Spec.RsaKeyGen.keyFromPrimes (32 * E.n) (inputExponent E m) (inputPrime E m 2) (inputPrime E m 3) = .inr () := by
  have widths := v.widths
  obtain bits : 16 * E.primeLength = 32 * E.n := by omega
  unfold encodedOperation Proof.RsaKeyGen.keyOp inputExponent inputPrime
  rw [bits]
  generalize result : Spec.RsaKeyGen.keyFromPrimes (32 * E.n)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) = value
  cases value with
  | inl answer => cases answer <;> simp [Proof.RsaKeyGen.keyStatus]
  | inr u => cases u; simp [Proof.RsaKeyGen.keyStatus]

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem PublicInputs.exponentValue {s t : State} (P : PublicInputs s t) :
    inputExponent (callEnvironment s) s.mem = inputExponent (callEnvironment s) t.mem := by
  have H := P.exponent
  unfold callEBytes at H
  rw [← P.environment] at H
  exact congrArg Spec.Rsa.os2ip H

theorem PublicInputs.release {s t : State} (P : PublicInputs s t) (h : contract.pre s) :
    (Spec.RsaKeyGen.keyFromPrimes (32 * (callEnvironment s).n)
      (inputExponent (callEnvironment s) s.mem) (inputPrime (callEnvironment s) s.mem 2)
      (inputPrime (callEnvironment s) s.mem 3) = .inr ()) ↔
    (Spec.RsaKeyGen.keyFromPrimes (32 * (callEnvironment s).n)
      (inputExponent (callEnvironment s) s.mem) (inputPrime (callEnvironment s) t.mem 2)
      (inputPrime (callEnvironment s) t.mem 3) = .inr ()) := by
  obtain v := call_valid h
  have status := P.status
  unfold callKeyStatus at status
  rw [← P.environment] at status
  obtain right := status_retry_iff v t.mem
  rw [← P.exponentValue] at right
  obtain same : (Proof.RsaKeyGen.keyStatus (encodedOperation (callEnvironment s) s.mem) = 2) ↔
      (Proof.RsaKeyGen.keyStatus (encodedOperation (callEnvironment s) t.mem) = 2) := by rw [status]
  exact (status_retry_iff v s.mem).symm.trans (same.trans right)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyCallSamples`, which only this module used -/

section

/-! # The native saved-register push preserves the original prime and exponent snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86

theorem entered_exponent {s : State} (h : contract.pre s) :
    inputExponent (callEnvironment s) (Compact.entered s).mem = inputExponent (callEnvironment s) s.mem := by
  obtain D := call_separation h
  unfold inputExponent
  congr 1
  exact pushed_bytes h D.stackExponent (by change (arg s 15).toNat < 2 ^ 64; have := (arg s 15).isLt; omega_using [])

theorem entered_prime {s : State} (h : contract.pre s) {i : Nat} (hi : i < 7) :
    inputPrime (callEnvironment s) (Compact.entered s).mem i = inputPrime (callEnvironment s) s.mem i := by
  obtain Z := call_sizes h
  obtain D := call_separation h
  unfold inputPrime
  rw [Z.outputRegion hi]
  congr 1
  exact pushed_bytes h (D.stackOutput i hi)
    (by change (arg s (2 * i + 1)).toNat < 2 ^ 64; have := (arg s (2 * i + 1)).isLt; omega_using [])

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Shared native key generation satisfies the existing API and timing contracts -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FrameResult.lean`, which only this module imported.
section

/-! # The callable key operation uses the caller's original encoded inputs -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Key (contract call_layout call_valid call_separation call_sizes
  callEnvironment EncodedResult BodyOutcome reservedRegion pushed_bytes)

theorem framed_result_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s fun t =>
      abiPreserved s t ∧ EncodedResult (callEnvironment s) s.mem t := by
  obtain v := call_valid h
  obtain A := call_layout h
  obtain D := call_separation h
  obtain Z := call_sizes h
  obtain eBytes : Spec.Rsa.bytesAt (Compact.entered s).mem (callEnvironment s).exponentRegion.base
      (callEnvironment s).exponentRegion.len =
      Spec.Rsa.bytesAt s.mem (callEnvironment s).exponentRegion.base (callEnvironment s).exponentRegion.len :=
    pushed_bytes h D.stackExponent (by change (arg s 15).toNat < 2 ^ 64; have := (arg s 15).isLt; omega)
  have primeBytes (i : Nat) (hi : i < 7) :
      Spec.Rsa.bytesAt (Compact.entered s).mem ((callEnvironment s).outputRegion i).base ((callEnvironment s).outputRegion i).len =
        Spec.Rsa.bytesAt s.mem ((callEnvironment s).outputRegion i).base ((callEnvironment s).outputRegion i).len := by
    rw [Z.outputRegion hi]
    apply pushed_bytes h (D.stackOutput i hi)
    change (arg s (2 * i + 1)).toNat < 2 ^ 64
    have := (arg s (2 * i + 1)).isLt
    omega
  refine WP.mono (framed_ok h) fun t ⟨preserved, R⟩ => ?_
  unfold BodyOutcome at R
  rw [eBytes, primeBytes 2 (by decide), primeBytes 3 (by decide)] at R
  exact ⟨preserved, BodyOutcome.encoded v R⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Correct.lean`, which only this module imported.
section

/-! # Complete native key generation satisfies the shared encoded cdecl contract -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.Key (contract call_sizes keyStack EncodedResult encodedOperation
  callEnvironment Environment)

theorem correct (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa VG.Impl.RsaKeyGen.X86.KeyRuntime.code s trace t ∧
      abiPreserved s t ∧ contract.post s t := by
  obtain Z := call_sizes h
  obtain ⟨trace, t, run, preserved, R⟩ := framed_result_ok h
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, keyStack, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold EncodedResult encodedOperation at R
  simp only [callEnvironment, Environment.exponentRegion, Environment.outputRegion, Environment.outputLength,
    List.range_succ, List.range_zero, List.map_nil, List.map_cons, List.nil_append, List.cons_append,
    Nat.reduceMul, Nat.reduceLT, ite_true, ite_false] at R
  rw [← Z.modulus] at R
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at R
  generalize result : Proof.RsaKeyGen.keyOp (arg s 5).toNat
    (Spec.Rsa.bytesAt s.mem ((arg s 14).setWidth 64) (arg s 15).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 5).toNat) = value at R ⊢
  cases value with
  | inl answer => cases answer <;> exact R
  | inr u => cases u; exact R

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FrontTiming.lean`, which only this module imported.
section

/-! # Shared derivation and the outputs publish only the specified retry bit -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment stage_scratch_frame deriveArrays prepareArrays keyPartArrays)
open VG.Proof.RsaKeyGen.X86.KeyArgs (argsRegion)

theorem deriveArgs_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputRegion i))
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeImported E sp e p q p' q') deriveLoaded (OutputStart E sp) := by
  intro s t tr ur u v P A C
  obtain ⟨trace, out⟩ := deriveOutput_trace E sp e p q p' q' release _ _ _ _ _ _ P A C
  have valid := P.imported.inputs.left.valid
  have widths := valid.widths
  obtain apart' : ∀ i < 7, (argsRegion sp).Disjoint (E.outputs.region i) := fun i hi => by
    rw [valid.outputRegion hi]
    exact apart i hi
  have frame {a b : State} {tr' : List Leak} (H : Ws a E.base E.size E.n 32)
      (L : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q a ∨
        VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p' q' a)
      (X : Exec isa deriveLoaded a tr' b) :
      ∃ rs : List Reg, Keeps rs a b ∧ .edi ∉ rs ∧ .esp ∉ rs ∧
        Frame [E.workspaceRegion, below (a.gpr .esp) 52] a.mem b.mem := by
    have go {e₁ p₁ q₁ : Nat} (L : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e₁ p₁ q₁ a) :
        ∃ rs : List Reg, Keeps rs a b ∧ .edi ∉ rs ∧ .esp ∉ rs ∧
          Frame [E.workspaceRegion, below (a.gpr .esp) 52] a.mem b.mem := by
      obtain ⟨_, O, _, K⟩ := wp_result (deriveLoaded_ok H widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
        widths.1 widths.2.1 L.pBound L.qBound L.zero L.one (L.loaded.trans L.exponent.symm)) X
      exact ⟨_, K, by decide, by decide, O.toFrame fun _ _ O =>
        stage_scratch_frame H.old (by simp [deriveArrays, prepareArrays, keyPartArrays]; decide) O⟩
    rcases L with L | L <;> exact go L
  obtain ⟨rs, KS, ediS, espS, FS⟩ := frame P.left (Or.inl P.imported.left) A
  obtain ⟨rt, KT, ediT, espT, FT⟩ := frame P.right (Or.inr P.imported.right) C
  rw [P.leftArgs.sp] at FS
  rw [P.rightArgs.sp] at FT
  exact ⟨trace, out, ⟨valid, P.leftArgs.keepBelow KS FS ediS espS, apart'⟩,
    ⟨valid, P.rightArgs.keepBelow KT FT ediT espT, apart'⟩⟩

theorem front_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputRegion i))
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeStart E sp e p q p' q') front
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true)) := by
  unfold front
  exact RelCT.seq (runtime_input_trace E sp e p q p' q')
    (RelCT.seq (deriveArgs_trace E sp e p q p' q' apart release) (writeOutputs_trace E sp))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/BodyTiming.lean`, which only this module imported.
section

/-! # The shared body retains exactly the declared exponent and retry observations -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment BodyPair)

theorem enterInput_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.enter
      (RuntimeStart E sp e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, start⟩ := VG.Proof.RsaKeyGen.X86.Key.enterInput_trace E valid sp e p q p' q'
    _ _ _ _ _ _ P A C
  obtain ⟨CS, _, _, _⟩ := wp_result (VG.Proof.RsaKeyGen.X86.KeyArgs.enter_ok P.left.arguments) A
  obtain ⟨CT, _, _, _⟩ := wp_result (VG.Proof.RsaKeyGen.X86.KeyArgs.enter_ok P.right.arguments) C
  exact ⟨trace, start, context_workspace valid CS start.inputs.left.ws,
    context_workspace valid CT start.inputs.right.ws, CS, CT⟩

theorem body_trace (E : Environment) (valid : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.KeyRuntime.body
      (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u v P A C
  obtain raw := RelCT.seq (enterInput_trace E valid sp e p q p' q')
    (front_trace E sp e p q p' q' P.left.argsOutput release)
  refine ⟨(raw _ _ _ _ _ _ P A C).1, agree_regs ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [Exec.gpr body_noSp A, Exec.gpr body_noSp C]
  exact P.left.arguments.sp.trans P.right.arguments.sp.symm

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/FrameTiming.lean`, which only this module imported.
section

/-! # The outer native key frame preserves trace equivalence -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment FramedPair)

theorem framed_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (FramedPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.KeyRuntime.code (fun _ _ => True) := by
  obtain restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.RsaKeyGen.X86.KeyRuntime.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace E v sp e p q p' q' release) restore).mono
    (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/ConstantTime.lean`, which only this module imported.
section

/-! # Native key assembly is constant time under exactly the shared API's declared observations -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86
open VG.Proof.RsaKeyGen.X86.Key (contract public_inputs entry_input callSp entered_exponent entered_prime
  callEnvironment inputExponent inputPrime call_valid)

theorem constantTime : ConstantTime isa contract.pre contract.pub VG.Impl.RsaKeyGen.X86.KeyRuntime.code := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  obtain P := public_inputs HP
  obtain I := entry_input HS
  obtain J := entry_input HT
  obtain stack : callSp s = callSp t := by unfold callSp; rw [P.stack]
  rw [← P.environment, ← stack] at J
  obtain rightExponent := entered_exponent HT
  obtain rightP := entered_prime HT (by decide : 2 < 7)
  obtain rightQ := entered_prime HT (by decide : 3 < 7)
  rw [← P.environment] at rightExponent rightP rightQ
  exact framed_trace (callEnvironment s) (call_valid HS) (callSp s)
    (inputExponent (callEnvironment s) s.mem)
    (inputPrime (callEnvironment s) s.mem 2) (inputPrime (callEnvironment s) s.mem 3)
    (inputPrime (callEnvironment s) t.mem 2) (inputPrime (callEnvironment s) t.mem 3)
    (P.release HS) _ _ _ _ _ _
    ⟨⟨I, J, entered_exponent HS, rightExponent.trans P.exponentValue.symm,
      entered_prime HS (by decide : 2 < 7), entered_prime HS (by decide : 3 < 7), rightP, rightQ⟩, P.stack⟩ A B

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86

theorem verified : Verified target VG.Impl.RsaKeyGen.X86.KeyRuntime.code VG.Proof.RsaKeyGen.X86.Key.contract :=
  ⟨correct, constantTime, VG.Proof.RsaKeyGen.X86.Key.satisfiable⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end


/-! # The controller's timing, and the verified key search (i686)

Two runs of the loop at one point, the calls' and the blocks' timing, the
whole controller's, and `Verified`.
-/

@[expose] public section

/-! ## Where two runs of the loop are (i686)

Two runs at the same point (`GenPoint`) agree on the public descriptor, the
octets consumed, the progress' public words (the generations left, the
phase's word and the counted candidates left), the state's request word and
the trace still to come, which each run's own key search from there gives.
The trace's first entry is the prime search's status, consumption, octets
left and trace, and, after `q`'s, the key's status: what each step does
follows from it (`gen_ct_step`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

structure GenPoint where
  inputs : GenPublic
  used : Nat
  left : Nat
  ph : Nat
  remaining : Nat
  req : BitVec 64
  trace : List Nat

/-- A run's progress `st` from `original`, at the point. -/
def AtPoint (q : GenPoint) (original : State) (st : KeyProgress) : Prop :=
  st.left = q.left ∧ phaseWord st.phase = q.ph ∧ st.remaining = q.remaining ∧
    (tailOf q.inputs original q.used st).trace = q.trace

/-- A loop state at the point. -/
def GenCTL (q : GenPoint) (s : State) : Prop :=
  ∃ original st, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req

/-! ## The first step, from the trace -/

abbrev GenPoint.status (q : GenPoint) : Nat := traceStatus q.trace
abbrev GenPoint.cand (q : GenPoint) : Nat := traceUsed q.trace
abbrev GenPoint.key (q : GenPoint) : Nat := traceKey q.trace

/-- Whether the key search goes on past the point's step. -/
def GenPoint.continues (q : GenPoint) : Prop :=
  (q.status = 3 ∧ ¬q.left < 2) ∨ (q.status = 1 ∧ q.cand ≠ 0 ∧ (q.ph = 0 ∨ q.key = 2))

/-- The point past the step, when the key search goes on. -/
def GenPoint.next (q : GenPoint) : GenPoint :=
  ⟨q.inputs, q.used + q.cand, if q.status = 3 then q.left - 1 else q.left,
    if q.status = 1 ∧ q.ph = 0 then 1 else 0, limitOf q.inputs.L q.inputs.eB, BitVec.ofNat 64 0,
    q.trace.drop (traceEntry q.trace + if q.status = 1 ∧ q.ph ≠ 0 then 2 else 0)⟩

section

variable {q : GenPoint} {original s : State} {st : KeyProgress}

theorem AtPoint.entry (h : AtPoint q original st) :
    ∃ rest, q.trace = primeEntry (rOf q.inputs original q.used st) ++ rest := by
  obtain ⟨rest, hr⟩ := keySearch_trace (L := q.inputs.L) (eB := q.inputs.eB) st ((genRand original).drop q.used)
  exact ⟨rest, h.2.2.2.symm.trans hr⟩

theorem AtPoint.status (h : AtPoint q original st) : (rOf q.inputs original q.used st).status = q.status := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.status, hr, (primeEntry_facts _ rest).1]

theorem AtPoint.cand (h : AtPoint q original st) : (rOf q.inputs original q.used st).used = q.cand := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.cand, hr, (primeEntry_facts _ rest).2.1]

theorem AtPoint.available (h : AtPoint q original st) :
    (rOf q.inputs original q.used st).available = traceAvailable q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.1]

theorem AtPoint.prime (h : AtPoint q original st) : (rOf q.inputs original q.used st).trace = tracePrime q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.1]

theorem AtPoint.entryLen (h : AtPoint q original st) :
    (primeEntry (rOf q.inputs original q.used st)).length = traceEntry q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.2]

/-- After `q`'s search accepted a prime, the key's status. -/
theorem AtPoint.keyStatus (h : AtPoint q original st)
    (hle : q.used + (rOf q.inputs original q.used st).used ≤ q.inputs.randLen)
    (hrl : (genRand original).length = q.inputs.randLen) {c : Nat}
    {pB : List Byte} (ho : (rOf q.inputs original q.used st).outcome = .accepted c)
    (hpos : 0 < (rOf q.inputs original q.used st).used) (hph : st.phase = .q pB) :
    keyResultStatus (keyFromPrimes (16 * q.inputs.L) (Spec.Rsa.os2ip q.inputs.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c q.inputs.L))) = q.key := by
  obtain hrest : (rOf q.inputs original q.used st).used ≤ ((genRand original).drop q.used).length := by
    rw [List.length_drop, hrl]; omega_using [hle]
  obtain ⟨rest, hr⟩ := keySearch_trace_key (L := q.inputs.L) (eB := q.inputs.eB) ho (drop_lt hpos hrest) hph
  rw [GenPoint.key, ← h.2.2.2, tailOf, hr, primeEntry_key]

theorem keyResultStatus_two (k : Except Failure Key ⊕ Unit) : keyResultStatus k = 2 ↔ k = .inr () := by
  rcases k with (k | k) | ⟨⟩ <;> simp [keyResultStatus]

theorem continues_iff (h : AtPoint q original st) (hl : GenFrame q.inputs original q.used st s) :
    ContSpec q.inputs original q.used st ↔ q.continues := by
  have hs := h.status
  have hc := h.cand
  have hleft := h.1
  have hph := h.2.1
  unfold ContSpec GenPoint.continues
  rw [← hs, ← hc, ← hleft, ← hph]
  cases ho : (rOf q.inputs original q.used st).outcome with
  | entropy k a => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | exhausted => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | accepted c =>
    obtain hs1 : (rOf q.inputs original q.used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs1]
    by_cases h0 : (rOf q.inputs original q.used st).used = 0
    · simp [h0]
    · cases hp : st.phase with
      | p => simp [h0, phaseWord]
      | q pB =>
        obtain hk := h.keyStatus (rOf_used_le hl) (genRand_length hl) ho (by omega_using [h0]) hp
        rw [← hk]
        simp [h0, phaseWord, keyResultStatus_two]

end

/-! ## A step -/

/-- After an iteration: the next point and the loop's condition, or its end. -/
def GenCTStep (q : GenPoint) (t : State) : Prop :=
  (q.continues ∧ eval .e t = some true ∧ GenCTL q.next t) ∨ (¬q.continues ∧ eval .e t = some false)

theorem next_point {q : GenPoint} {original t : State} {st : KeyProgress} {final : KeySearchResult}
    (h : AtPoint q original st) (hc : Cont q.inputs original final q.used st t) : GenCTL q.next t := by
  obtain ⟨hreq, ⟨st', e, hlive, -, htail, hrem, hnext⟩, -⟩ := hc
  have hs := h.status
  have hcd := h.cand
  obtain ⟨hleft, hph, -, htr⟩ := h
  refine ⟨original, st', ⟨?_, ?_, ?_, ?_⟩, by rw [GenPoint.next, ← hcd]; exact hlive, hreq⟩
  all_goals simp only [GenPoint.next]
  · rcases hnext with ⟨ho, hl, -, -⟩ | ⟨c, ho, -, hl, -, -⟩ | ⟨c, pB, ho, -, hl, -, -⟩ <;>
      rw [← hs, rOf_status, ho] <;> simp [hl, hleft, Spec.Entropy.Outcome.status]
  · rcases hnext with ⟨ho, -, hp, -⟩ | ⟨c, ho, hp, -, hp', -⟩ | ⟨c, pB, ho, hp, -, hp', -⟩
    · rw [← hs, rOf_status, ho, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, hp', ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, hp', ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
  · exact hrem
  · rw [← hcd, ← htr, htail]
    simp only [Spec.Entropy.Result.consume, List.drop_append]
    rcases hnext with ⟨ho, -, -, rfl⟩ | ⟨c, ho, hp, -, -, rfl⟩ | ⟨c, pB, ho, hp, -, -, rfl⟩
    · rw [← hs, rOf_status, ho]; simp [Spec.Entropy.Outcome.status]
    · rw [← hs, rOf_status, ho, ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord, List.length_append]

theorem gen_ct_step (srch : Srch) (key : KeyImpl) (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (iteration srch.call key.call) s (GenCTStep q) := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  obtain hi : GenIter q.inputs o ((tailOf q.inputs o q.used st).consume q.used []) q.used st s := ⟨hl, [], rfl⟩
  unfold iteration
  refine WP.seq (WP.mono (search_run srch hl) fun t hs => ?_)
  refine WP.seq (WP.mono (classify_ok key hi hs) fun u hc => ?_)
  rcases hc with ⟨hcs, hct⟩ | ⟨hcs, hd⟩
  · obtain ⟨o', st', ha', hl', hr'⟩ := next_point ha hct
    refine WP.mono (cmp_ok (r := .ebx) rfl 4) fun x ⟨⟨hx, hmem⟩, k, sy⟩ =>
      .inl ⟨(continues_iff ha hl.toGenFrame).mp hcs, ?_, o', st', ha', hl'.same k sy hmem, by rw [hmem]; exact hr'⟩
    rw [hx, hl'.ebx]; rfl
  · have hlt := keyStatus_lt ((tailOf q.inputs o q.used st).consume q.used [])
    refine WP.mono (cmp_ok (r := .ebx) rfl 4) fun x ⟨⟨hx, _⟩, _⟩ =>
      .inr ⟨fun h => hcs ((continues_iff ha hl.toGenFrame).mpr h), ?_⟩
    rw [hx, hd.2.1, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      beq_nat (BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega_using [hlt])) (by decide)]
    simp only [Option.some.injEq, decide_eq_false_iff_not]
    omega_using [hlt]

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## Pieces of two runs (i686)

A block whose first part loads a pointer from the stack: the taint analysis
checks the first part with the registers the state pins, and the rest with
those and the pointer, which correctness gives (`two_split`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- Two postconditions of a block, which runs one way. -/
theorem WP.block_and {M : ISA} {is : List M.Instr} {s : M.State} {Q₁ Q₂ : M.State → Prop}
    (h₁ : WP M (.block is) s Q₁) (h₂ : WP M (.block is) s Q₂) : WP M (.block is) s fun t => Q₁ t ∧ Q₂ t := by
  induction is generalizing s with
  | nil => exact WP.block_nil_iff.mpr ⟨WP.block_nil_iff.mp h₁, WP.block_nil_iff.mp h₂⟩
  | cons i is ih =>
    obtain ⟨a, ea, ha⟩ := WP.block_cons_iff.mp h₁
    obtain ⟨b, eb, hb⟩ := WP.block_cons_iff.mp h₂
    rw [ea] at eb
    cases eb
    exact WP.block_cons_iff.mpr ⟨a, ea, ih ha hb⟩

/-- A block of two parts: the first checked with the registers `rs₁` the
state pins, the rest with the registers `rs₂` correctness pins after the
first. -/
theorem two_split {α : Type} {Φ Ψ F : α → State → Prop} (l₁ l₂ : List Instr) (rs₁ rs₂ : List Reg)
    (hpin₁ : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.X86.Taint.T} (h₁ : (taint.check (τr rs₁) (.block l₁) hc₁).isSome = true)
    (hF : ∀ a s, Φ a s → WP isa (.block l₁) s (F a)) (hpin₂ : Pins F rs₂)
    {hc₂ : VG.Taint.Hint VG.X86.Taint.T} (h₂ : (taint.check (τr rs₂) (.block l₂) hc₂).isSome = true)
    (hW : ∀ a s, Φ a s → WP isa (.block (l₁ ++ l₂)) s (Ψ a)) :
    RelCT isa (Two Φ) (.block (l₁ ++ l₂)) (Two Ψ) := by
  refine two_post (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun a t => F a t ∧ WP isa (.block l₂) t (Ψ a))
    rs₁ hpin₁ h₁ fun a s h => WP.block_and (hF a s h) (WP.block_append_iff.mp (hW a s h)))
    (two_taint rs₂ (fun a s₁ s₂ h₁ h₂ => hpin₂ a s₁ s₂ h₁.1 h₂.1) h₂))) hW

/-- The same, leaking alike only. -/
theorem two_split0 {α : Type} {Φ F : α → State → Prop} (l₁ l₂ : List Instr) (rs₁ rs₂ : List Reg)
    (hpin₁ : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.X86.Taint.T} (h₁ : (taint.check (τr rs₁) (.block l₁) hc₁).isSome = true)
    (hF : ∀ a s, Φ a s → WP isa (.block l₁) s (F a)) (hpin₂ : Pins F rs₂)
    {hc₂ : VG.Taint.Hint VG.X86.Taint.T} (h₂ : (taint.check (τr rs₂) (.block l₂) hc₂).isSome = true) :
    RelCT isa (Two Φ) (.block (l₁ ++ l₂)) fun _ _ => True :=
  RelCT.block_append (RelCT.seq (two_piece rs₁ hpin₁ h₁ hF) (two_taint rs₂ hpin₂ h₂))

theorem no_pins {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

theorem ev_false {c : Cond} {s : State} {b : Prop} [Decidable b] (he : eval c s = some (decide b))
    (hf : isa.eval c s = some false) : ¬b := fun h => by
  obtain hx : some (decide b) = some false := he.symm.trans hf
  simp [h] at hx

theorem ev_true {c : Cond} {s : State} {b : Prop} [Decidable b] (he : eval c s = some (decide b))
    (ht : isa.eval c s = some true) : b := by
  obtain hx : some (decide b) = some true := he.symm.trans ht
  simpa using hx

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## Two runs of the prime search (i686)

Two runs at the same point pass `vg_rsa_prime_search` the same arguments, at
the same stack pointer, and the same public data: `e`, the state's words and
the search's status, consumption, octets left and trace, which the point's
trace fixes (`search_pub`); so their calls leak the same (`search_call_ct`),
and so do their frames of arguments (`search_run_ct`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- In the search's frame, with its arguments, at the point. -/
def CallS (q : GenPoint) (t : State) : Prop :=
  ∃ o st s, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧ word s.mem q.inputs.stp 24 = q.req ∧
    Fr q.inputs o s 48 t ∧ SArgs q.inputs o q.used (phaseWord st.phase) t.mem ∧
    Frame [fR o 48] s.mem t.mem

/-- `e` and the state's words, on the search's entry. -/
theorem entry_state {p : GenPublic} {o s₀ t : State} {used : Nat} {st : KeyProgress} (F : Fr p o s₀ 48 t)
    (hst : StateOk p st t.mem) (ph : Nat) (v : BitVec 32) :
    Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 216) v)
        (BitVec.setWidth 64 (searchArg p used ph 3)) (searchArg p used ph 4).toNat = p.eB ∧
      Spec.Rsa.wordsAt (t.mem.writeW (low o + BitVec.ofNat 64 216) v) (BitVec.setWidth 64 (searchArg p used ph 11)) 4 =
        [BitVec.ofNat 64 st.remaining, BitVec.ofNat 64 p.L, BitVec.ofNat 64 (primeEntropy p.L), word t.mem p.stp 24] := by
  have hi := F.input
  have A := hi.abi
  obtain sT : Region.Sub ⟨low o + BitVec.ofNat 64 216, 4⟩ (lowR o) := low_sub (by decide)
  obtain fe : Frame [⟨low o + BitVec.ofNat 64 216, 4⟩] t.mem (t.mem.writeW (low o + BitVec.ofNat 64 216) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain sS : (lowR o).Disjoint ⟨p.stp.setWidth 64, 56⟩ := by rw [← hi.sR_eq]; exact A.lowS
  have far {R : Region} (hR : Region.Sub R ⟨p.stp.setWidth 64, 56⟩) :
      ∀ r ∈ [(⟨low o + BitVec.ofNat 64 216, 4⟩ : Region)], R.Disjoint r := fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact ((sS.sub_right hR).sub_left sT).symm
  refine ⟨?_, ?_⟩
  · rw [sb3 hi, show (searchArg p used ph 4).toNat = 8 from rfl, ← hst.e]
    exact bytes_keep (R := ⟨p.stp.setWidth 64 + 48, 8⟩) fe (far (Offset.sub_base _ (d := 48) (n := 8) (by decide)))
      (show 8 ≤ 2 ^ 64 by decide)
  · have wd (d : Nat) (hd : d + 8 ≤ 56) :
        (t.mem.writeW (low o + BitVec.ofNat 64 216) v).readW (p.stp.setWidth 64 + BitVec.ofNat 64 d) 64 =
          word t.mem p.stp d := word_keep fe (far (Offset.sub_base _ hd))
    simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil,
      Nat.reduceMul, show searchArg p used ph 11 = p.stp from rfl]
    rw [wd 0 (by decide), wd 8 (by decide), wd 16 (by decide), wd 24 (by decide), hst.remaining, hst.len, hst.cap]

theorem search_pub {q : GenPoint} {t₁ t₂ : State} (h₁ : CallS q t₁) (h₂ : CallS q t₂) (rd wr : List Region) :
    VG.Proof.RsaKeyGen.X86.Search.contract.pub (t₁.callEntry.withRegions rd wr)
      (t₂.callEntry.withRegions rd wr) := by
  obtain ⟨o₁, st₁, s₁, a₁, L₁, w₁, F₁, g₁, m₁⟩ := h₁
  obtain ⟨o₂, st₂, s₂, a₂, L₂, w₂, F₂, g₂, m₂⟩ := h₂
  have i₁ := F₁.input
  have i₂ := F₂.input
  obtain S₁ : StateOk q.inputs st₁ t₁.mem := L₁.state.frame (R := fR o₁ 48)
    (by rw [← i₁.sR_eq]; exact i₁.abi.lowS.sub_left (low_sub (by decide))) m₁
  obtain S₂ : StateOk q.inputs st₂ t₂.mem := L₂.state.frame (R := fR o₂ 48)
    (by rw [← i₂.sR_eq]; exact i₂.abi.lowS.sub_left (low_sub (by decide))) m₂
  obtain K₁ : KeyOk q.inputs st₁ t₁.mem := L₁.key.frame i₁.kBound'
    (by rw [← i₁.kR_eq]; exact i₁.abi.lowK.sub_left (low_sub (by decide))) m₁
  obtain K₂ : KeyOk q.inputs st₂ t₂.mem := L₂.key.frame i₂.kBound'
    (by rw [← i₂.kR_eq]; exact i₂.abi.lowK.sub_left (low_sub (by decide))) m₂
  obtain r24₁ : word t₁.mem q.inputs.stp 24 = q.req := by
    rw [← w₁]; exact word_keep m₁ fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (i₁.abi.lowS.sub_left (low_sub (by decide))).symm.sub_left (by rw [i₁.sR_eq]; exact Offset.sub_base _ (by decide))
  obtain r24₂ : word t₂.mem q.inputs.stp 24 = q.req := by
    rw [← w₂]; exact word_keep m₂ fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (i₂.abi.lowS.sub_left (low_sub (by decide))).symm.sub_left (by rw [i₂.sR_eq]; exact Offset.sub_base _ (by decide))
  sig_pub [VG.Proof.RsaKeyGen.X86.Search.contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  simp only [ce_arg F₁ g₁ rd wr (show 0 < 12 by decide), ce_arg F₁ g₁ rd wr (show 1 < 12 by decide), ce_arg F₁ g₁ rd wr (show 2 < 12 by decide), ce_arg F₁ g₁ rd wr (show 3 < 12 by decide), ce_arg F₁ g₁ rd wr (show 4 < 12 by decide), ce_arg F₁ g₁ rd wr (show 5 < 12 by decide), ce_arg F₁ g₁ rd wr (show 6 < 12 by decide), ce_arg F₁ g₁ rd wr (show 7 < 12 by decide), ce_arg F₁ g₁ rd wr (show 8 < 12 by decide), ce_arg F₁ g₁ rd wr (show 9 < 12 by decide), ce_arg F₁ g₁ rd wr (show 10 < 12 by decide), ce_arg F₁ g₁ rd wr (show 11 < 12 by decide), ce_arg F₂ g₂ rd wr (show 0 < 12 by decide), ce_arg F₂ g₂ rd wr (show 1 < 12 by decide), ce_arg F₂ g₂ rd wr (show 2 < 12 by decide), ce_arg F₂ g₂ rd wr (show 3 < 12 by decide), ce_arg F₂ g₂ rd wr (show 4 < 12 by decide), ce_arg F₂ g₂ rd wr (show 5 < 12 by decide), ce_arg F₂ g₂ rd wr (show 6 < 12 by decide), ce_arg F₂ g₂ rd wr (show 7 < 12 by decide), ce_arg F₂ g₂ rd wr (show 8 < 12 by decide), ce_arg F₂ g₂ rd wr (show 9 < 12 by decide), ce_arg F₂ g₂ rd wr (show 10 < 12 by decide), ce_arg F₂ g₂ rd wr (show 11 < 12 by decide), ret_eq F₁, ret_eq F₂]
  rw [entry_result F₁ L₁.used_le S₁ K₁, entry_result F₂ L₂.used_le S₂ K₂]
  simp only [(entry_state F₁ S₁ _ _).1,
    (entry_state F₁ S₁ _ _).2, (entry_state F₂ S₂ _ _).1, (entry_state F₂ S₂ _ _).2, r24₁, r24₂,
    a₁.status, a₂.status, a₁.cand, a₂.cand, a₁.available, a₂.available, a₁.prime, a₂.prime,
    a₁.2.1, a₂.2.1, a₁.2.2.1, a₂.2.2.1]
  have tb (o : State) (h : GenInput q.inputs o) : o.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = q.inputs.tab := by
    rw [← h.2]; rfl
  refine ⟨by rw [F₁.esp, F₂.esp], by rw [F₁.syms, F₂.syms, tb o₁ i₁, tb o₂ i₂], ?_⟩
  simp only [and_self]

/-- What the search reads and writes, from the point. -/
abbrev sRdK (q : GenPoint) : List Region :=
  [cE q.inputs q.used q.ph, cP q.inputs q.used q.ph, cW q.inputs q.used q.ph, ⟨q.inputs.tab.setWidth 64, 8192⟩]
abbrev sWrK (q : GenPoint) : List Region :=
  [cO q.inputs q.used q.ph, cU q.inputs q.used q.ph, cB q.inputs q.used q.ph, cS q.inputs q.used q.ph,
    ⟨q.inputs.sp.setWidth 64 - 284#64 + BitVec.ofNat 64 (268 - 48), 48⟩]

theorem sRd_eq {q : GenPoint} {o : State} {st : KeyProgress} (h : GenInput q.inputs o) (a : AtPoint q o st) :
    sRd q.inputs q.used (phaseWord st.phase) o = sRdK q := by
  rw [a.2.1]
  show [_, _, _, (⟨(o.syms _).setWidth 64, 8192⟩ : Region)] = _
  rw [show o.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = q.inputs.tab by rw [← h.2]; rfl]

theorem sWr_eq {q : GenPoint} {o : State} {st : KeyProgress} (h : GenInput q.inputs o) (a : AtPoint q o st) :
    sWr q.inputs q.used (phaseWord st.phase) o = sWrK q := by
  rw [a.2.1]
  show [_, _, _, _, (⟨(o.gpr .esp).setWidth 64 - 284#64 + _, 48⟩ : Region)] = _
  rw [← h.sp_eq]

theorem search_call_ct (srch : Srch) (q : GenPoint) :
    RelCT isa (fun t₁ t₂ => CallS q t₁ ∧ CallS q t₂) srch.call fun _ _ => True := by
  refine RelCT.call srch.verified.1 srch.verified.2.1 (sRdK q) (sWrK q) fun t₁ t₂ ⟨h₁, h₂⟩ => ?_
  obtain pub := search_pub h₁ h₂ (sRdK q) (sWrK q)
  have side {t : State} (h : CallS q t) :
      VG.Proof.RsaKeyGen.X86.Search.contract.pre (t.callEntry.withRegions (sRdK q) (sWrK q)) ∧
        Covers (sRdK q ++ sWrK q) (t.rd ++ t.wr) ∧ Covers (sWrK q) t.wr := by
    obtain ⟨o, st, s, a, L, -, F, g, m⟩ := h
    have i := F.input
    obtain hst : StateOk q.inputs st t.mem := L.state.frame (R := fR o 48)
      (by rw [← i.sR_eq]; exact i.abi.lowS.sub_left (low_sub (by decide))) m
    rw [← sRd_eq i a, ← sWr_eq i a]
    exact ⟨search_pre F g hst L.used_le, search_covers _ F L.used_le⟩
  obtain ⟨p₁, c₁, w₁⟩ := side h₁
  obtain ⟨p₂, c₂, w₂⟩ := side h₂
  obtain ⟨_, _, _, _, _, _, F₁, _, _⟩ := h₁
  obtain ⟨_, _, _, _, _, _, F₂, _, _⟩ := h₂
  exact ⟨p₁, p₂, pub, c₁, w₁, c₂, w₂, by rw [F₁.esp, F₂.esp]⟩

/-- In the search's frame, before its arguments. -/
def FrS (q : GenPoint) (f : State) : Prop := ∃ s, GenCTL q s ∧ f = allocFrame 48 s

/-- With the state's pointer in `eax`. -/
def FrS1 (q : GenPoint) (f : State) : Prop := f.gpr .eax = q.inputs.stp ∧ f.gpr .esp = q.inputs.S1 - BitVec.ofNat 32 48

theorem two_of {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s₁ s₂ => Φ a s₁ ∧ Φ a s₂) c Q) : RelCT isa (Two Φ) c Q :=
  fun _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂ => h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

theorem search_run_ct (srch : Srch) : RelCT isa (Two GenCTL) (searchRun srch.call) fun _ _ => True := by
  unfold searchRun
  rw [show 4 * searchWords = 48 from rfl]
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  refine (RelCT.seq (P := Two FrS) (R := Two CallS) ?_ (two_of (search_call_ct srch))).mono ?_ (fun _ _ h => h)
  swap
  · rintro a b ⟨s₁, s₂, ⟨q, h₁, h₂⟩, e₁, e₂⟩; exact ⟨q, ⟨s₁, h₁, e₁⟩, ⟨s₂, h₂, e₂⟩⟩
  rw [show searchArgs = [.mov .eax (.mem (param searchWords 7))] ++ searchArgs.drop 1 from rfl]
  refine two_split (Φ := FrS) (F := FrS1) _ _ [.esp] [.eax, .esp] ?_ (by taint_decide) ?_ ?_ (by taint_decide) ?_
  · rintro q f₁ f₂ ⟨s₁, ⟨_, _, _, L₁, _⟩, rfl⟩ ⟨s₂, ⟨_, _, _, L₂, _⟩, rfl⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [allocFrame_esp, allocFrame_esp, L₁.sp, L₂.sp]
  · rintro q f ⟨s, ⟨o, st, a, L, w⟩, rfl⟩
    obtain F0 := L.toGenBase.alloc (n := 48) (by decide)
    have hst : q.inputs.stp = arg o 7 := F0.input.stp_eq
    show WP isa _ _ fun f => f.gpr .eax = q.inputs.stp ∧ f.gpr .esp = q.inputs.S1 - BitVec.ofNat 32 48
    simp only [param_eq, pushWords, searchWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, F0.arg_ea (w := 12) (i := 7) (d := 96) rfl, F0.arg_in (i := 7) (by decide),
      F0.arg_val (i := 7) (by decide), hst]
    exact F0.esp
  · rintro q f₁ f₂ ⟨e₁, s₁⟩ ⟨e₂, s₂⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [e₁, e₂]
    · rw [s₁, s₂]
  · rintro q f ⟨s, ⟨o, st, a, L, w⟩, rfl⟩
    obtain F0 := L.toGenBase.alloc (n := 48) (by decide)
    obtain hph1 : phaseWord st.phase ≤ 1 := by unfold phaseWord; split <;> omega_using []
    obtain hph : (allocFrame 48 s).mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 32 =
        BitVec.ofNat 32 (phaseWord st.phase) := by
      show s.mem.readW _ 32 = _
      rw [← F0.input.stp_eq]; exact low_half L.state.phase
    rw [show [.mov .eax (.mem (param searchWords 7))] ++ searchArgs.drop 1 = searchArgs from rfl]
    exact WP.of_syms (WP.mono (searchArgs_ok F0 (by rw [allocFrame_gpr _ _ (by decide)]; exact L.ebp)
      (by rw [allocFrame_gpr _ _ (by decide)]; exact L.esi) hph hph1 L.used_le) fun u ⟨⟨ha, hfr⟩, k⟩ sy =>
        ⟨o, st, s, a, L, w, F0.stores (by decide) k sy hfr, ha, hfr⟩)

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The controller's blocks in two runs (i686)

Each block that loads a pointer from the stack and then goes through it is
checked in two parts (`two_split`): the load, with the stack pointer the
frame pins, and the rest, with the pointer correctness gives. The key's
buffer cleared, the stores that start the next prime's search or end the key
search, and one generation fewer.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- A state in the frame, of the public data `q.inputs`. -/
def AnyFrame (q : GenPoint) (s : State) : Prop := ∃ o used st, GenFrame q.inputs o used st s

theorem anyFrame_pins : Pins AnyFrame [.esp, .ebp] := by
  rintro q s₁ s₂ ⟨_, _, _, g₁⟩ ⟨_, _, _, g₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [g₁.sp, g₂.sp]
  · rw [g₁.ebp, g₂.ebp]

/-- A state in the frame with `r` loaded with argument `i`. -/
def Loaded (r : Reg) (i : Nat) (q : GenPoint) (t : State) : Prop :=
  (∃ o, GenInput q.inputs o ∧ t.gpr r = arg o i) ∧ t.gpr .esp = q.inputs.S1 ∧
    t.gpr .ebp = BitVec.ofNat 32 q.inputs.L

theorem arg_pub {q : GenPoint} {o₁ o₂ : State} (h₁ : GenInput q.inputs o₁) (h₂ : GenInput q.inputs o₂) {i : Nat}
    (hi : i = 0 ∨ i = 2 ∨ i = 7) : arg o₁ i = arg o₂ i := by
  rcases hi with rfl | rfl | rfl
  · rw [← h₁.kp_eq, ← h₂.kp_eq]
  · rw [← h₁.up_eq, ← h₂.up_eq]
  · rw [← h₁.stp_eq, ← h₂.stp_eq]

theorem loaded_pins (r : Reg) {i : Nat} (hi : i = 0 ∨ i = 2 ∨ i = 7) : Pins (Loaded r i) [r, .esp, .ebp] := by
  rintro q s₁ s₂ ⟨⟨o₁, i₁, e₁⟩, sp₁, bp₁⟩ ⟨⟨o₂, i₂, e₂⟩, sp₂, bp₂⟩ x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · rw [e₁, e₂, arg_pub i₁ i₂ hi]
  · rw [sp₁, sp₂]
  · rw [bp₁, bp₂]

/-- An argument loaded from the stack. -/
theorem load_ok {q : GenPoint} {s : State} (h : AnyFrame q s) (r : Reg) (hr : r ≠ .esp ∧ r ≠ .ebp) {i : Nat}
    (hi : i < 8) : WP isa (.block [.mov r (.mem (param 0 i))]) s (Loaded r i q) := by
  obtain ⟨o, used, st, g⟩ := h
  have hb := g.toGenBase
  refine WP.mono (WP.blockKeep [r] (Q := fun t => t.gpr r = arg o i) ?_ (by cases r <;> rfl))
    fun t ⟨e, k, _⟩ => ⟨⟨o, hb.input, e⟩, (k.gpr (by simp [hr.1.symm])).trans hb.sp,
      (k.gpr (by simp [hr.2.symm])).trans g.ebp⟩
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.add_zero]
  xrun [State.ea, at_, hb.arg_ea (i := i) (d := 4 + 4 * i + 16) (by omega_using []), hb.arg_in hi, hb.arg_val hi]

theorem anyFrame_load (r : Reg) (hr : r ≠ .esp ∧ r ≠ .ebp) {i : Nat} (hi : i < 8) :
    ∀ q s, AnyFrame q s → WP isa (.block [.mov r (.mem (param 0 i))]) s (Loaded r i q) :=
  fun _ _ h => load_ok h r hr hi

theorem finishWith1_ct : RelCT isa (Two AnyFrame) (.block (finishWith 1)) fun _ _ => True := by
  rw [show finishWith 1 = [.mov .eax (.mem (param 0 7))] ++ (finishWith 1).drop 1 from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.eax, .esp, .ebp] anyFrame_pins (by taint_decide)
    (anyFrame_load .eax (by decide) (by decide)) (loaded_pins .eax (by decide)) (by taint_decide)

theorem finishWith2_ct : RelCT isa (Two AnyFrame) (.block (finishWith 2)) fun _ _ => True := by
  rw [show finishWith 2 = [.mov .eax (.mem (param 0 7))] ++ (finishWith 2).drop 1 from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.eax, .esp, .ebp] anyFrame_pins (by taint_decide)
    (anyFrame_load .eax (by decide) (by decide)) (loaded_pins .eax (by decide)) (by taint_decide)

theorem finishWith3_ct : RelCT isa (Two AnyFrame) (.block (finishWith 3)) fun _ _ => True := by
  rw [show finishWith 3 = [.mov .eax (.mem (param 0 7))] ++ (finishWith 3).drop 1 from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.eax, .esp, .ebp] anyFrame_pins (by taint_decide)
    (anyFrame_load .eax (by decide) (by decide)) (loaded_pins .eax (by decide)) (by taint_decide)

theorem nextPrime0_ct : RelCT isa (Two AnyFrame) (.block (nextPrime 0)) fun _ _ => True := by
  rw [show nextPrime 0 = [.mov .eax (.mem (param 0 7))] ++ (nextPrime 0).drop 1 from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.eax, .esp, .ebp] anyFrame_pins (by taint_decide)
    (anyFrame_load .eax (by decide) (by decide)) (loaded_pins .eax (by decide)) (by taint_decide)

theorem nextPrime1_ct : RelCT isa (Two AnyFrame) (.block (nextPrime 1)) fun _ _ => True := by
  rw [show nextPrime 1 = [.mov .eax (.mem (param 0 7))] ++ (nextPrime 1).drop 1 from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.eax, .esp, .ebp] anyFrame_pins (by taint_decide)
    (anyFrame_load .eax (by decide) (by decide)) (loaded_pins .eax (by decide)) (by taint_decide)

/-- The key's buffer's pointer and length in `edx` and `ecx`. -/
def ClearAt (q : GenPoint) (v : State) : Prop :=
  v.gpr .edx = q.inputs.kp ∧ v.gpr .ecx = BitVec.ofNat 32 (9 * q.inputs.L) ∧ v.gpr .esp = q.inputs.S1

theorem clearB_ok {q : GenPoint} {s : State} (h : AnyFrame q s) :
    WP isa (.block (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++ ([.alu .add .ecx (.reg .ecx),
      .alu .add .ecx (.reg .ebp), .mov .eax (.imm 0)] : List Instr))) s (ClearAt q) := by
  obtain ⟨o, used, st, hf⟩ := h
  have hi := hf.input
  have hv := hi.len_valid
  refine WP.mono (WP.blockKeep [.eax, .ecx, .edx] (Q := fun v =>
      v.gpr .edx = arg o 0 ∧ v.gpr .ecx = BitVec.ofNat 32 (9 * q.inputs.L)) ?_ (by rfl))
    fun v ⟨⟨hd, hc⟩, k, _⟩ => ⟨by rw [hd, hi.kp_eq], hc, (k.gpr (by decide)).trans hf.sp⟩
  simp only [four, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]
  xrun [State.ea, at_, hf.arg_ea (i := 0) (d := 20) rfl, hf.arg_in (i := 0) (by decide),
    hf.arg_val (i := 0) (by decide), hf.ebp, four_val]
  simp only [← BitVec.ofNat_add]; congr 1; omega_using []

theorem clearAt_pins : Pins ClearAt [.edx, .ecx, .esp] := by
  rintro q s₁ s₂ ⟨d₁, c₁, p₁⟩ ⟨d₂, c₂, p₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [d₁, d₂]
  · rw [c₁, c₂]
  · rw [p₁, p₂]

theorem clearAll_ct : RelCT isa (Two AnyFrame) clearAll fun _ _ => True := by
  unfold clearAll
  refine RelCT.seq (two_post (Ψ := ClearAt) ?_ fun q s h => clearB_ok h) (two_taint _ clearAt_pins (by taint_decide))
  rw [show ([.mov .edx (.mem (param 0 0))] ++ four ++ [.alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ebp),
    .mov .eax (.imm 0)] : List Instr) = [.mov .edx (.mem (param 0 0))] ++ (four ++ [.alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .ebp), .mov .eax (.imm 0)]) from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.edx, .esp, .ebp] anyFrame_pins (by taint_decide)
    (anyFrame_load .edx (by decide) (by decide)) (loaded_pins .edx (by decide)) (by taint_decide)

theorem fail2_ct : RelCT isa (Two AnyFrame) (fail 2) fun _ _ => True := by
  unfold fail
  refine RelCT.seq (two_post (Ψ := AnyFrame) clearAll_ct fun q s ⟨o, used, st, g⟩ =>
    WP.mono (clearAll_ok g) fun t h => ⟨o, used, st, h.1⟩) finishWith2_ct

theorem fail3_ct : RelCT isa (Two AnyFrame) (fail 3) fun _ _ => True := by
  unfold fail
  refine RelCT.seq (two_post (Ψ := AnyFrame) clearAll_ct fun q s ⟨o, used, st, g⟩ =>
    WP.mono (clearAll_ok g) fun t h => ⟨o, used, st, h.1⟩) finishWith3_ct

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## Two runs of the key (i686)

Two runs at the same point pass `vg_rsa_keygen_key` the same arguments, at
the same stack pointer, and the same `e` and the same primes' status, which
the point's trace fixes: so their calls leak the same (`key_run_ct`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem keyStatus_keyOp (L : Nat) (eB pB qB : List Byte) :
    keyStatus (keyOp L eB pB qB) = keyResultStatus (keyFromPrimes (16 * L) (Spec.Rsa.os2ip eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB)) := by
  unfold keyOp
  split <;> rename_i h <;> rw [h] <;> rfl

/-- After `q`'s search accepted a prime, at the point: the key's state. -/
def KeyCT (q : GenPoint) (w : State) : Prop :=
  ∃ o st final c pB u, AtPoint q o st ∧ Mid q.inputs o final q.used st u ∧
    (rOf q.inputs o q.used st).outcome = .accepted c ∧ 0 < (rOf q.inputs o q.used st).used ∧
    st.phase = .q pB ∧
    GenFrame q.inputs o (q.used + (rOf q.inputs o q.used st).used)
      ⟨st.left, st.phase, (rOf q.inputs o q.used st).remaining⟩ w ∧ w.mem = u.mem

theorem KeyCT.status {q : GenPoint} {w : State} (h : KeyCT q w) : keyStatus (keyOf q.inputs w.mem) = q.key := by
  obtain ⟨o, st, final, c, pB, u, ha, hm, ho, hpos, hph, -, hmem⟩ := h
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  simp only [keyOf, hmem, hs4, hs5, keyStatus_keyOp]
  exact ha.keyStatus hm.frame.used_le (genRand_length hm.frame) ho hpos hph

/-- In the key's frame, with its arguments, of a state with the point's key. -/
def CallK (q : GenPoint) (t : State) : Prop :=
  ∃ o used st s, GenFrame q.inputs o used st s ∧ keyStatus (keyOf q.inputs s.mem) = q.key ∧
    Fr q.inputs o s 72 t ∧ KArgs q.inputs o t.mem ∧ Frame [fR o 72] s.mem t.mem

/-- What the key reads and writes, from the point. -/
abbrev kWrK (q : GenPoint) : List Region :=
  [kG q.inputs 0 1, kG q.inputs 2 3, kG q.inputs 4 5, kG q.inputs 6 7, kG q.inputs 8 9, kG q.inputs 10 11,
    kG q.inputs 12 13, kB q.inputs, ⟨q.inputs.sp.setWidth 64 - 284#64 + BitVec.ofNat 64 (268 - 72), 72⟩]

theorem kWr_eq {q : GenPoint} {o : State} (h : GenInput q.inputs o) : kWr q.inputs o = kWrK q := by
  show [_, _, _, _, _, _, _, _, (⟨(o.gpr .esp).setWidth 64 - 284#64 + _, 72⟩ : Region)] = _
  rw [← h.sp_eq]

/-- `e` and the primes, on the key's entry. -/
theorem key_inputs {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress} (g : GenFrame p o used st s)
    (F : Fr p o s 72 t) (hfr : Frame [fR o 72] s.mem t.mem) (v : BitVec 32) :
    Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 192) v) ((keyArg p 14).setWidth 64) (keyArg p 15).toNat =
        p.eB ∧
      keyOp (keyArg p 5).toNat
        (Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 192) v) ((keyArg p 14).setWidth 64) (keyArg p 15).toNat)
        (Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 192) v) ((keyArg p 4).setWidth 64) (keyArg p 5).toNat)
        (Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 192) v) ((keyArg p 6).setWidth 64) (keyArg p 5).toNat) =
        keyOf p s.mem := by
  have hi := F.input
  have A := hi.abi
  have hv := hi.len_valid
  obtain l5 : (keyArg p 5).toNat = p.L := by rw [show keyArg p 5 = BitVec.ofNat 32 p.L from rfl, kL1 hi]; omega_using []
  obtain b4 : (keyArg p 4).setWidth 64 = p.slot 4 := congrArg Region.base (kE2 hi)
  obtain b6 : (keyArg p 6).setWidth 64 = p.slot 5 := congrArg Region.base (kE3 hi)
  obtain b14 : (keyArg p 14).setWidth 64 = p.stp.setWidth 64 + 48 := by
    have := hi.sBound'
    exact VG.Proof.MlKem.X86.ea_off (x := p.stp) (d := 48) (by omega_using [this])
  obtain Fs : Region.Sub (fR o 72) (lowR o) := low_sub (by decide)
  obtain sT : Region.Sub ⟨low o + BitVec.ofNat 64 192, 4⟩ (lowR o) := low_sub (by decide)
  obtain sK : (lowR o).Disjoint ⟨p.kp.setWidth 64, 9 * p.L⟩ := by rw [← hi.kR_eq]; exact A.lowK
  obtain sS : (lowR o).Disjoint ⟨p.stp.setWidth 64, 56⟩ := by rw [← hi.sR_eq]; exact A.lowS
  obtain hst : StateOk p st t.mem := g.state.frame (R := fR o 72) (sS.sub_left Fs) hfr
  obtain fe : Frame [⟨low o + BitVec.ofNat 64 192, 4⟩] t.mem (t.mem.writeW (low o + BitVec.ofNat 64 192) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have slotIn (j : Nat) (hj : j + 1 ≤ 9) :
      Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 192) v) (p.slot j) p.L =
        Spec.Rsa.bytesAt s.mem (p.slot j) p.L := by
    obtain hsub : Region.Sub ⟨p.slot j, p.L⟩ ⟨p.kp.setWidth 64, 9 * p.L⟩ := Offset.sub_base _ (by
      have := Nat.mul_le_mul_right p.L hj; rw [Nat.add_mul] at this; omega_using [this])
    rw [bytes_keep (R := ⟨p.slot j, p.L⟩) fe (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact (sK.sub_left sT).symm.sub_left hsub) (show p.L ≤ 2 ^ 64 by omega_using [hv])]
    exact bytes_keep (R := ⟨p.slot j, p.L⟩) hfr (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq; exact (sK.sub_left Fs).symm.sub_left hsub) (show p.L ≤ 2 ^ 64 by omega_using [hv])
  obtain eIn : Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 192) v) (p.stp.setWidth 64 + 48) 8 = p.eB := by
    rw [← hst.e]
    exact bytes_keep (R := ⟨p.stp.setWidth 64 + 48, 8⟩) fe (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      exact (sS.sub_left sT).symm.sub_left (Offset.sub_base (d := 48) (n := 8) (k := 56) _ (by decide)))
      (show 8 ≤ 2 ^ 64 by decide)
  rw [l5, b14, show (keyArg p 15).toNat = 8 from rfl, eIn, b4, b6, slotIn 4 (by decide), slotIn 5 (by decide)]
  exact ⟨rfl, rfl⟩

theorem key_pub {q : GenPoint} {t₁ t₂ : State} (h₁ : CallK q t₁) (h₂ : CallK q t₂) (rd wr : List Region) :
    VG.Proof.RsaKeyGen.X86.Key.contract.pub (t₁.callEntry.withRegions rd wr)
      (t₂.callEntry.withRegions rd wr) := by
  obtain ⟨o₁, u₁, st₁, s₁, g₁, k₁, F₁, a₁, m₁⟩ := h₁
  obtain ⟨o₂, u₂, st₂, s₂, g₂, k₂, F₂, a₂, m₂⟩ := h₂
  sig_pub [VG.Proof.RsaKeyGen.X86.Key.contract, Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argSlots,
    argVal, argBytes]
  simp only [ce_key F₁ a₁ rd wr (show 0 < 18 by decide), ce_key F₁ a₁ rd wr (show 1 < 18 by decide), ce_key F₁ a₁ rd wr (show 2 < 18 by decide), ce_key F₁ a₁ rd wr (show 3 < 18 by decide), ce_key F₁ a₁ rd wr (show 4 < 18 by decide), ce_key F₁ a₁ rd wr (show 5 < 18 by decide), ce_key F₁ a₁ rd wr (show 6 < 18 by decide), ce_key F₁ a₁ rd wr (show 7 < 18 by decide), ce_key F₁ a₁ rd wr (show 8 < 18 by decide), ce_key F₁ a₁ rd wr (show 9 < 18 by decide), ce_key F₁ a₁ rd wr (show 10 < 18 by decide), ce_key F₁ a₁ rd wr (show 11 < 18 by decide), ce_key F₁ a₁ rd wr (show 12 < 18 by decide), ce_key F₁ a₁ rd wr (show 13 < 18 by decide), ce_key F₁ a₁ rd wr (show 14 < 18 by decide), ce_key F₁ a₁ rd wr (show 15 < 18 by decide), ce_key F₁ a₁ rd wr (show 16 < 18 by decide), ce_key F₁ a₁ rd wr (show 17 < 18 by decide),
    ce_key F₂ a₂ rd wr (show 0 < 18 by decide), ce_key F₂ a₂ rd wr (show 1 < 18 by decide), ce_key F₂ a₂ rd wr (show 2 < 18 by decide), ce_key F₂ a₂ rd wr (show 3 < 18 by decide), ce_key F₂ a₂ rd wr (show 4 < 18 by decide), ce_key F₂ a₂ rd wr (show 5 < 18 by decide), ce_key F₂ a₂ rd wr (show 6 < 18 by decide), ce_key F₂ a₂ rd wr (show 7 < 18 by decide), ce_key F₂ a₂ rd wr (show 8 < 18 by decide), ce_key F₂ a₂ rd wr (show 9 < 18 by decide), ce_key F₂ a₂ rd wr (show 10 < 18 by decide), ce_key F₂ a₂ rd wr (show 11 < 18 by decide), ce_key F₂ a₂ rd wr (show 12 < 18 by decide), ce_key F₂ a₂ rd wr (show 13 < 18 by decide), ce_key F₂ a₂ rd wr (show 14 < 18 by decide), ce_key F₂ a₂ rd wr (show 15 < 18 by decide), ce_key F₂ a₂ rd wr (show 16 < 18 by decide), ce_key F₂ a₂ rd wr (show 17 < 18 by decide),
    ret_key F₁, ret_key F₂]
  rw [(key_inputs g₁ F₁ m₁ _).2, (key_inputs g₁ F₁ m₁ _).1, (key_inputs g₂ F₂ m₂ _).2, (key_inputs g₂ F₂ m₂ _).1,
    k₁, k₂, F₁.esp, F₂.esp]
  simp only [and_self]

theorem key_call_ct (key : KeyImpl) (q : GenPoint) :
    RelCT isa (fun t₁ t₂ => CallK q t₁ ∧ CallK q t₂) key.call fun _ _ => True := by
  refine RelCT.call key.verified.1 key.verified.2.1 (kRd q.inputs) (kWrK q) fun t₁ t₂ ⟨h₁, h₂⟩ => ?_
  obtain pub := key_pub h₁ h₂ (kRd q.inputs) (kWrK q)
  have side {t : State} (h : CallK q t) :
      VG.Proof.RsaKeyGen.X86.Key.contract.pre (t.callEntry.withRegions (kRd q.inputs) (kWrK q)) ∧
        Covers (kRd q.inputs ++ kWrK q) (t.rd ++ t.wr) ∧ Covers (kWrK q) t.wr := by
    obtain ⟨o, used, st, s, g, -, F, a, -⟩ := h
    rw [← kWr_eq F.input]
    exact ⟨key_pre F a, key_covers F⟩
  obtain ⟨p₁, c₁, w₁⟩ := side h₁
  obtain ⟨p₂, c₂, w₂⟩ := side h₂
  obtain ⟨_, _, _, _, _, _, F₁, _, _⟩ := h₁
  obtain ⟨_, _, _, _, _, _, F₂, _, _⟩ := h₂
  exact ⟨p₁, p₂, pub, c₁, w₁, c₂, w₂, by rw [F₁.esp, F₂.esp]⟩

/-- A state in the frame whose key has the point's status. -/
def KeyIn (q : GenPoint) (s : State) : Prop :=
  ∃ o used st, GenFrame q.inputs o used st s ∧ keyStatus (keyOf q.inputs s.mem) = q.key

/-- In the key's frame, before its arguments. -/
def FrK (q : GenPoint) (f : State) : Prop := ∃ s, KeyIn q s ∧ f = allocFrame 72 s

theorem key_run_ct (key : KeyImpl) : RelCT isa (Two KeyIn) (keyRun key.call) fun _ _ => True := by
  unfold keyRun
  rw [show 4 * keyWords = 72 from rfl]
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  refine (RelCT.seq (P := Two FrK) (R := Two CallK) ?_ (two_of (key_call_ct key))).mono ?_ (fun _ _ h => h)
  swap
  · rintro a b ⟨s₁, s₂, ⟨q, h₁, h₂⟩, e₁, e₂⟩; exact ⟨q, ⟨s₁, h₁, e₁⟩, ⟨s₂, h₂, e₂⟩⟩
  refine two_piece [.esp] ?_ (by taint_decide) ?_
  · rintro q f₁ f₂ ⟨s₁, ⟨_, _, _, g₁, _⟩, rfl⟩ ⟨s₂, ⟨_, _, _, g₂, _⟩, rfl⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [allocFrame_esp, allocFrame_esp, g₁.sp, g₂.sp]
  · rintro q f ⟨s, ⟨o, used, st, g, hk⟩, rfl⟩
    obtain F0 := g.toGenBase.alloc (n := 72) (by decide)
    exact WP.of_syms (WP.mono (keyArgs_ok F0 (by rw [allocFrame_gpr _ _ (by decide)]; exact g.ebp))
      fun u ⟨⟨ha, hfr⟩, k⟩ sy => ⟨o, used, st, s, g, hk, F0.stores (by decide) (k.mono (by decide)) sy hfr, ha, hfr⟩)

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The classification's timing (i686)

After the search, each test the controller branches on is of the point:
the search's status and consumption, the generations left, the phase and
the key's status; every block between them the taint analysis checks from
the registers the frame and the loaded pointers pin.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- A state in the frame with the state's pointer in `eax` and a generation left. -/
def DecAt (q : GenPoint) (s : State) : Prop :=
  ∃ o used st, GenFrame q.inputs o used st s ∧ s.gpr .eax = arg o 7 ∧ 1 ≤ st.left

theorem decAt_pins : Pins DecAt [.eax, .esp, .ebp] := by
  rintro q s₁ s₂ ⟨o₁, _, _, g₁, e₁, _⟩ ⟨o₂, _, _, g₂, e₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [e₁, e₂, arg_pub (i := 7) g₁.input g₂.input (.inr (.inr rfl))]
  · rw [g₁.sp, g₂.sp]
  · rw [g₁.ebp, g₂.ebp]

theorem decNext_ct : RelCT isa (Two DecAt) (.block (([.mov .ecx (.mem (st 40)), .alu .sub .ecx (.imm 1),
    .store (st 40) .ecx, .mov .ecx (.mem (st 44)), .alu .sbb .ecx (.imm 0), .store (st 44) .ecx] : List Instr) ++
      nextPrime 0))
    fun _ _ => True := by
  rw [show ([.mov .ecx (.mem (st 40)), .alu .sub .ecx (.imm 1), .store (st 40) .ecx, .mov .ecx (.mem (st 44)),
      .alu .sbb .ecx (.imm 0), .store (st 44) .ecx] ++ nextPrime 0 : List Instr) =
    ([.mov .ecx (.mem (st 40)), .alu .sub .ecx (.imm 1), .store (st 40) .ecx, .mov .ecx (.mem (st 44)),
      .alu .sbb .ecx (.imm 0), .store (st 44) .ecx] ++ [.mov .eax (.mem (param 0 7))]) ++ (nextPrime 0).drop 1 from rfl]
  refine two_split0 _ _ [.eax, .esp, .ebp] [.eax, .esp, .ebp] decAt_pins (by taint_decide) ?_
    (loaded_pins .eax (i := 7) (by decide)) (by taint_decide)
  rintro q s ⟨o, used, st, g, hax, hl⟩
  exact WP.block_append (WP.mono (dec_ok g hax hl) fun t ⟨g1, _, _⟩ => load_ok ⟨o, used, _, g1⟩ .eax (by decide)
    (by decide))

/-! ## The head -/

/-- After the search, at the point. -/
def AfterCT (q : GenPoint) (t : State) : Prop :=
  ∃ original st s, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req ∧ AfterSearch q.inputs original q.used st s t

theorem AfterCT.any {q : GenPoint} {t : State} (h : AfterCT q t) : AnyFrame q t :=
  let ⟨o, _, _, _, _, _, ha⟩ := h; ⟨o, _, _, ha.frame⟩

/-- After the search and the count of its octets, at the point. -/
def MidCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st, AtPoint q original st ∧
    Mid q.inputs original ((tailOf q.inputs original q.used st).consume q.used []) q.used st u

theorem MidCT.any {q : GenPoint} {u : State} (h : MidCT q u) : AnyFrame q u :=
  let ⟨o, _, _, hm⟩ := h; ⟨o, _, _, hm.frame⟩

theorem status_cases (r : PrimeSearchResult) : r.status = 0 ∨ r.status = 1 ∨ r.status = 3 := by
  rw [rOf_status]; cases r.outcome <;> simp [Spec.Entropy.Outcome.status]

/-- The head's test, at the point. -/
def HeadCT (q : GenPoint) (u : State) : Prop := MidCT q u ∧ eval .e u = some (decide (q.status = 0))

theorem head_ct : RelCT isa (Two AfterCT) (.block [.mov .edx (.mem (param 0 2)), .mov .ecx (.mem (at_ .edx 0)),
    .alu .add .esi (.reg .ecx), .alu .cmp .eax (.imm 0)]) (Two HeadCT) := by
  rw [show ([.mov .edx (.mem (param 0 2)), .mov .ecx (.mem (at_ .edx 0)), .alu .add .esi (.reg .ecx),
      .alu .cmp .eax (.imm 0)] : List Instr) = [.mov .edx (.mem (param 0 2))] ++
    [.mov .ecx (.mem (at_ .edx 0)), .alu .add .esi (.reg .ecx), .alu .cmp .eax (.imm 0)] from rfl]
  refine two_split _ _ [.esp, .ebp] [.edx, .esp, .ebp]
    (fun q s₁ s₂ h₁ h₂ => anyFrame_pins q s₁ s₂ h₁.any h₂.any) (by taint_decide)
    (fun q s h => load_ok h.any .edx (by decide) (by decide)) (loaded_pins .edx (i := 2) (.inr (.inl rfl)))
    (by taint_decide) ?_
  rintro q t ⟨o, st, s, ha, hl, -, haf⟩
  exact WP.mono (head_ok ⟨hl, [], rfl⟩ haf) fun u ⟨hm, hz⟩ =>
    ⟨⟨o, st, ha, hm⟩, by show u.zf = _; rw [hz, ha.status]⟩

/-! ## A generation exhausted -/

/-- The generations' test, at the point. -/
def LeftCT (q : GenPoint) (w : State) : Prop :=
  (∃ o used st, GenFrame q.inputs o used st w ∧ w.gpr .eax = arg o 7 ∧ st.left = q.left) ∧
    eval .ne w = some (decide (q.left < 2))

theorem exhausted_ct : RelCT isa (Two MidCT) exhaustedGen fun _ _ => True := by
  unfold exhaustedGen
  refine RelCT.seq (M := isa) (R := Two LeftCT) ?_ ?_
  · rw [show ([.mov .eax (.mem (param 0 7)), .mov .ecx (.mem (st 44)), .alu .cmp .ecx (.imm 1),
        .alu .sbb .ecx (.reg .ecx), .mov .edx (.mem (st 40)), .alu .cmp .edx (.imm 2), .alu .sbb .edx (.reg .edx),
        .alu .and .ecx (.reg .edx), .alu .test .ecx (.reg .ecx)] : List Instr) = [.mov .eax (.mem (param 0 7))] ++
      [.mov .ecx (.mem (st 44)), .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx), .mov .edx (.mem (st 40)),
        .alu .cmp .edx (.imm 2), .alu .sbb .edx (.reg .edx), .alu .and .ecx (.reg .edx),
        .alu .test .ecx (.reg .ecx)] from rfl]
    refine two_split _ _ [.esp, .ebp] [.eax, .esp, .ebp]
      (fun q s₁ s₂ h₁ h₂ => anyFrame_pins q s₁ s₂ h₁.any h₂.any) (by taint_decide)
      (fun q s h => load_ok h.any .eax (by decide) (by decide)) (loaded_pins .eax (i := 7) (.inr (.inr rfl)))
      (by taint_decide) ?_
    rintro q u ⟨o, st, ha, hm⟩
    exact WP.mono (left_test hm.frame) fun w ⟨⟨he3, hax, hmemw⟩, kw, syw⟩ =>
      ⟨⟨o, _, _, hm.frame.keepRegs kw (by decide) syw hmemw, hax, ha.1⟩, by rw [he3, ha.1]⟩
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_map id (fun _ _ ⟨⟨⟨o, u, st, g, _⟩, _⟩, _⟩ => ⟨o, u, st, g⟩) fail3_ct
  · refine two_map id (fun q w ⟨⟨⟨o, u, st, g, hax, hl⟩, he⟩, hf⟩ => ⟨o, u, st, g, hax, ?_⟩) decNext_ct
    have := ev_false he hf
    omega_using [hl, this]

/-! ## After the key -/

/-- After the key, at the point. -/
def AfterKCT (q : GenPoint) (v : State) : Prop := AnyFrame q v ∧ (v.gpr .eax).toNat = q.key ∧ q.key < 3

theorem keyStatus_lt3 (k : Except Failure (List (List Byte)) ⊕ Unit) : keyStatus k < 3 := by
  unfold keyStatus; split <;> decide

/-- The key's first test, at the point. -/
def Key1CT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q v ∧ (v.gpr .eax).toNat = q.key ∧ q.key < 3 ∧ eval .e v = some (decide (q.key = 1))

/-- The key's second test, at the point. -/
def Key2CT (q : GenPoint) (v : State) : Prop := AnyFrame q v ∧ eval .e v = some (decide (q.key = 2))

theorem after_key_ct : RelCT isa (Two AfterKCT) afterKey fun _ _ => True := by
  unfold afterKey
  refine RelCT.seq (two_post (Ψ := Key1CT) (two_taint [] (no_pins _) (by taint_decide))
    fun q v ⟨⟨o, u, st, g⟩, hs, h3⟩ => WP.mono (cmp_ok (r := .eax) rfl 1) fun w ⟨⟨he, hmem⟩, k, sy⟩ =>
      ⟨⟨o, u, st, g.same k sy hmem⟩, by rw [k.gpr (by decide)]; exact hs, h3,
        by rw [he, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, beq_nat hs (by decide)]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact two_map id (fun _ _ h => h.1.1) finishWith1_ct
  · refine RelCT.seq (two_post (Ψ := Key2CT) (two_taint [] (no_pins _) (by taint_decide))
      fun q v ⟨⟨⟨o, u, st, g⟩, hax, h3, _⟩, _⟩ => WP.mono (cmp_ok (r := .eax) rfl 2)
        fun w ⟨⟨he, hmem⟩, k, sy⟩ => ⟨⟨o, u, st, g.same k sy hmem⟩,
          by rw [he, show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, beq_nat hax (by decide)]⟩) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact two_map id (fun _ _ h => h.1.1) nextPrime0_ct
    · exact two_map id (fun _ _ h => h.1.1) fail2_ct

/-! ## A prime accepted -/

/-- Past the phase's test, at the point, after an accepted prime. -/
def PhCT (q : GenPoint) (x : State) : Prop :=
  (∃ o st u, AtPoint q o st ∧ Mid q.inputs o ((tailOf q.inputs o q.used st).consume q.used []) q.used st u ∧
    q.status = 1 ∧ q.cand ≠ 0 ∧
    GenFrame q.inputs o (q.used + (rOf q.inputs o q.used st).used)
      ⟨st.left, st.phase, (rOf q.inputs o q.used st).remaining⟩ x ∧ x.mem = u.mem) ∧
    eval .e x = some (decide (q.ph = 0))

theorem accepted_ct (key : KeyImpl) :
    RelCT isa (Two fun q u => MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0) (accepted key.call) fun _ _ => True := by
  unfold accepted
  refine RelCT.seq (M := isa) (R := Two PhCT) ?_ ?_
  · rw [show ([.mov .eax (.mem (param 0 7)), .mov .ecx (.mem (st 32)), .alu .cmp .ecx (.imm 0)] : List Instr) =
      [.mov .eax (.mem (param 0 7))] ++ [.mov .ecx (.mem (st 32)), .alu .cmp .ecx (.imm 0)] from rfl]
    refine two_split _ _ [.esp, .ebp] [.eax, .esp, .ebp]
      (fun q s₁ s₂ h₁ h₂ => anyFrame_pins q s₁ s₂ h₁.1.any h₂.1.any) (by taint_decide)
      (fun q s h => load_ok h.1.any .eax (by decide) (by decide)) (loaded_pins .eax (i := 7) (.inr (.inr rfl)))
      (by taint_decide) ?_
    rintro q u ⟨⟨o, st, ha, hm⟩, h1, h0⟩
    exact WP.mono (phase_test hm.frame) fun x ⟨⟨he, hmem⟩, k, sy⟩ =>
      ⟨⟨o, st, u, ha, hm, h1, h0, hm.frame.keepRegs k (by decide) sy hmem, hmem⟩,
        by rw [he]; show some (decide (phaseWord st.phase = 0)) = _; rw [ha.2.1]⟩
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_map id (fun _ _ ⟨⟨⟨o, _, _, _, _, _, _, g, _⟩, _⟩, _⟩ => ⟨o, _, _, g⟩) nextPrime1_ct
  · have hk : ∀ q x, (PhCT q x ∧ eval .e x = some false) → KeyCT q x := by
      rintro q x ⟨⟨⟨o, st, u, ha, hm, h1, h0, g, hmem⟩, he⟩, hf⟩
      obtain hph : q.ph ≠ 0 := ev_false he hf
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p => exact absurd (ha.2.1.symm.trans rfl) hph
      | q pB =>
        cases ho : (rOf q.inputs o q.used ⟨left, .q pB, remaining⟩).outcome with
        | entropy k a => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | exhausted => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | accepted c => exact ⟨o, _, _, c, pB, u, ha, hm, ho, by rw [ha.cand]; omega_using [h0], rfl, g, hmem⟩
    refine RelCT.seq (two_post (Ψ := AfterKCT) (two_map id (fun q x h => ?_) (key_run_ct key)) fun q x h => ?_)
      after_key_ct
    · have hc := hk q x h
      obtain ⟨o, _, _, _, _, _, _, _, _, _, _, g, _⟩ := id hc
      exact ⟨o, _, _, g, hc.status⟩
    · have hc := hk q x h
      obtain ⟨o, _, _, _, _, _, _, _, _, _, _, g, _⟩ := id hc
      exact WP.mono (key_run key g) fun v hak => ⟨⟨o, _, _, hak.frame⟩, by rw [hak.status, hc.status],
        by rw [← hc.status]; exact keyStatus_lt3 _⟩

/-! ## The classification -/

/-- The test of the search's status 3, at the point. -/
def Mid3CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status ≠ 0 ∧ eval .e u = some (decide (q.status = 3))

/-- The test of the octets the search consumed, at the point. -/
def Mid4CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status = 1 ∧ eval .e u = some (decide (q.cand = 0))

theorem classify_ct (key : KeyImpl) : RelCT isa (Two AfterCT) (classify key.call) fun _ _ => True := by
  unfold classify
  refine RelCT.seq head_ct ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_taint [] (no_pins _) (by taint_decide)
  · refine RelCT.seq (two_post (Ψ := Mid3CT) (two_taint [] (no_pins _) (by taint_decide))
      fun q u ⟨⟨⟨o, st, ha, hm⟩, he⟩, hf⟩ => ?_) ?_
    · have h0 : q.status ≠ 0 := ev_false he hf
      exact WP.mono (cmp_ok (r := .eax) rfl 3) fun v ⟨⟨he3, hmem⟩, k, sy⟩ =>
        ⟨⟨o, st, ha, hm.same k sy hmem⟩, h0, by
          rw [he3, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl,
            beq_nat (hm.status.trans ha.status) (by decide)]⟩
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_ ?_
    · exact two_map id (fun _ _ h => h.1.1) exhausted_ct
    · refine RelCT.seq (two_post (Ψ := Mid4CT) (two_taint [] (no_pins _) (by taint_decide))
        fun q u ⟨⟨⟨o, st, ha, hm⟩, h0, he⟩, hf⟩ => ?_) ?_
      · have h3 : q.status ≠ 3 := ev_false he hf
        obtain hs := status_cases (rOf q.inputs o q.used st)
        rw [ha.status] at hs
        obtain hu32 : (rOf q.inputs o q.used st).used < 2 ^ 32 := by
          have := hm.frame.used_le; have := hm.frame.input.randLen_lt; omega_arith
        exact WP.mono (cmp_ok (r := .ecx) rfl 0) fun v ⟨⟨he4, hmem⟩, k, sy⟩ =>
          ⟨⟨o, st, ha, hm.same k sy hmem⟩, by omega_using [h0, h3, hs], by
            rw [he4, hm.ecx, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
              beq_nat (BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt hu32) (by decide), ha.cand]⟩
      refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_ ?_
      · exact two_map id (fun _ _ h => h.1.1.any) fail3_ct
      · exact two_map id (fun _ _ ⟨⟨hm, h1, he⟩, hf⟩ => ⟨hm, h1, ev_false he hf⟩) (accepted_ct key)

end VG.Proof.RsaKeyGen.X86.Generate


/-! ## The controller's timing depends on its public data and its trace (i686)

Two runs that `contract.pub` relates start at the same point
(`initialPoint`): an iteration takes both to the next point or ends both
(`gen_ct_step`), and every block, call and test between is of the point.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## An iteration -/

theorem search_run_post (srch : Srch) : RelCT isa (Two GenCTL) (searchRun srch.call) (Two AfterCT) :=
  two_post (search_run_ct srch) fun _ s ⟨o, st, ha, hl, hw⟩ =>
    WP.mono (search_run srch hl) fun _ h => ⟨o, st, s, ha, hl, hw, h⟩

theorem classify_any (key : KeyImpl) (q : GenPoint) (t : State) (h : AfterCT q t) :
    WP isa (classify key.call) t (AnyFrame q) := by
  obtain ⟨o, st, s, -, hl, -, ha⟩ := h
  refine WP.mono (classify_ok key ⟨hl, [], rfl⟩ ha) fun u hc => ?_
  rcases hc with ⟨-, hct⟩ | ⟨-, hd⟩
  · obtain ⟨st', -, hl', -⟩ := hct.next
    exact ⟨o, _, st', hl'.toGenFrame⟩
  · exact ⟨o, _, _, hd.1⟩

theorem iteration_ct (srch : Srch) (key : KeyImpl) :
    RelCT isa (Two GenCTL) (iteration srch.call key.call) fun _ _ => True := by
  unfold iteration
  exact RelCT.seq (search_run_post srch) (RelCT.seq (two_post (classify_ct key) (classify_any key))
    (two_taint [] (no_pins _) (by taint_decide)))

/-! ## The loop -/

/-- What each step that goes on lowers. -/
def GenPoint.measure (q : GenPoint) : Nat := (q.inputs.randLen - q.used) * 2 ^ 64 + q.left

theorem next_measure {q : GenPoint} {t : State} (hc : q.continues) (h : GenCTL q.next t) :
    q.next.measure < q.measure := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hle := hl.used_le
  have hlt := hl.state.left_lt
  rw [ha.1] at hlt
  unfold GenPoint.measure
  simp only [GenPoint.next] at hle hlt ⊢
  rcases hc with ⟨h3, hl2⟩ | ⟨h1, hc0, -⟩
  · simp only [h3, ↓reduceIte] at hlt ⊢
    obtain hmul : (q.inputs.randLen - (q.used + q.cand)) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega_using [])
    omega_using [hl2]
  · have h3 : ¬q.status = 3 := by omega_using [h1]
    simp only [h3, ↓reduceIte] at hlt ⊢
    obtain hmul : (q.inputs.randLen - (q.used + q.cand) + 1) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega_using [hle, hc0])
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega_using [hle, hc0]

/-- Two loop states at a point of measure `n`. -/
def LoopPair (n : Nat) (s t : State) : Prop := ∃ q : GenPoint, n = q.measure ∧ GenCTL q s ∧ GenCTL q t

theorem iteration_pair (srch : Srch) (key : KeyImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration srch.call key.call) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : GenPoint) (s : State) (h : n = q.measure ∧ GenCTL q s) :
      WP isa (iteration srch.call key.call) s fun t => n = q.measure ∧ GenCTStep q t :=
    WP.mono (gen_ct_step srch key q s h.2) fun _ ht => ⟨h.1, ht⟩
  obtain hc := two_post ((iteration_ct srch key).mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, by rw [hn]; exact next_measure hb c₁, q.next, rfl,
      c₁, c₂⟩⟩
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem loop_ct (srch : Srch) (key : KeyImpl) :
    RelCT isa (Two GenCTL) (.loop (iteration srch.call key.call) .e) fun _ _ => True := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration srch.call key.call) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair srch key) q.measure _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-- A loop's end. -/
def DoneCT (q : GenPoint) (t : State) : Prop := ∃ original final, GenDone q.inputs original final t

theorem loop_done (srch : Srch) (key : KeyImpl) (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (.loop (iteration srch.call key.call) .e) s (DoneCT q) := by
  obtain ⟨o, st, -, hl, -⟩ := h
  exact WP.mono (gen_loop srch key (n := genMeasure q.inputs q.used st)
    (final := (tailOf q.inputs o q.used st).consume q.used []) ⟨q.used, st, rfl, hl, [], rfl⟩)
    fun _ ht => ⟨o, _, ht⟩

theorem finish_ct : RelCT isa (Two DoneCT) (.block finish) fun _ _ => True := by
  rw [show finish = [.mov .edx (.mem (param 0 2))] ++ (results.drop 1 ++ Impl.Mont.X86.Compact.restoreRegs) from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.edx, .esp, .ebp]
    (fun q s₁ s₂ ⟨o₁, _, d₁⟩ ⟨o₂, _, d₂⟩ => anyFrame_pins q s₁ s₂ ⟨o₁, _, _, d₁.1⟩ ⟨o₂, _, _, d₂.1⟩)
    (by taint_decide) (fun q s ⟨o, _, d⟩ => load_ok ⟨o, _, _, d.1⟩ .edx (by decide) (by decide))
    (loaded_pins .edx (i := 2) (.inr (.inl rfl))) (by taint_decide)

/-! ## The key's buffer cleared -/

/-- In the frame, before any octet is consumed. -/
def ClrF (q : GenPoint) (t : State) : Prop := ∃ o st, GenFrame q.inputs o 0 st t

/-- The first zeros' pointer and count. -/
def ZeroLo (q : GenPoint) (v : State) : Prop :=
  v.gpr .edx = q.inputs.kp ∧ v.gpr .ecx = BitVec.ofNat 32 (4 * q.inputs.L) ∧ v.gpr .esp = q.inputs.S1

/-- The second zeros' pointer and count. -/
def ZeroHi (q : GenPoint) (v : State) : Prop :=
  v.gpr .edx = q.inputs.kp + BitVec.ofNat 32 (5 * q.inputs.L) ∧ v.gpr .ecx = BitVec.ofNat 32 (4 * q.inputs.L) ∧
    v.gpr .esp = q.inputs.S1

theorem zeroLo_pins : Pins ZeroLo [.edx, .ecx, .esp] := by
  rintro q s₁ s₂ ⟨d₁, c₁, p₁⟩ ⟨d₂, c₂, p₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [d₁.trans d₂.symm, c₁.trans c₂.symm, p₁.trans p₂.symm]

theorem zeroHi_pins : Pins ZeroHi [.edx, .ecx, .esp] := by
  rintro q s₁ s₂ ⟨d₁, c₁, p₁⟩ ⟨d₂, c₂, p₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [d₁.trans d₂.symm, c₁.trans c₂.symm, p₁.trans p₂.symm]

theorem clearLoB_ok {q : GenPoint} {t : State} (h : ClrF q t) :
    WP isa (.block (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++ ([.mov .eax (.imm 0)] : List Instr)))
      t (ZeroLo q) := by
  obtain ⟨o, st, hf⟩ := h
  have hi := hf.input
  refine WP.mono (WP.blockKeep [.eax, .ecx, .edx] (Q := fun v =>
      v.gpr .edx = arg o 0 ∧ v.gpr .ecx = BitVec.ofNat 32 (4 * q.inputs.L)) ?_ (by rfl))
    fun v ⟨⟨hd, hc⟩, k, _⟩ => ⟨by rw [hd, hi.kp_eq], hc, (k.gpr (by decide)).trans hf.sp⟩
  simp only [four, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]
  xrun [State.ea, at_, hf.arg_ea (i := 0) (d := 20) rfl, hf.arg_in (i := 0) (by decide),
    hf.arg_val (i := 0) (by decide), hf.ebp, four_val]

theorem clearHiB_ok {q : GenPoint} {t : State} (h : ClrF q t) :
    WP isa (.block (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++ ([.alu .add .edx (.reg .ecx),
      .alu .add .edx (.reg .ebp), .mov .eax (.imm 0)] : List Instr))) t (ZeroHi q) := by
  obtain ⟨o, st, hf⟩ := h
  have hi := hf.input
  refine WP.mono (WP.blockKeep [.eax, .ecx, .edx] (Q := fun v =>
      v.gpr .edx = arg o 0 + BitVec.ofNat 32 (5 * q.inputs.L) ∧ v.gpr .ecx = BitVec.ofNat 32 (4 * q.inputs.L)) ?_
      (by rfl))
    fun v ⟨⟨hd, hc⟩, k, _⟩ => ⟨by rw [hd, hi.kp_eq], hc, (k.gpr (by decide)).trans hf.sp⟩
  simp only [four, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]
  xrun [State.ea, at_, hf.arg_ea (i := 0) (d := 20) rfl, hf.arg_in (i := 0) (by decide),
    hf.arg_val (i := 0) (by decide), hf.ebp, four_val]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * q.inputs.L + q.inputs.L = 5 * q.inputs.L by omega_using []]

theorem clrF_pins : Pins ClrF [.esp, .ebp] :=
  fun q s₁ s₂ ⟨o₁, st₁, g₁⟩ ⟨o₂, st₂, g₂⟩ => anyFrame_pins q s₁ s₂ ⟨o₁, 0, st₁, g₁⟩ ⟨o₂, 0, st₂, g₂⟩

theorem clearLo_ct : RelCT isa (Two ClrF) (.seq (.block (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++
    ([.mov .eax (.imm 0)] : List Instr))) zeroLoop) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := ZeroLo) ?_ fun q t h => clearLoB_ok h) (two_taint _ zeroLo_pins (by taint_decide))
  rw [show (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++ ([.mov .eax (.imm 0)] : List Instr)) =
    [.mov .edx (.mem (param 0 0))] ++ (four ++ [.mov .eax (.imm 0)]) from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.edx, .esp, .ebp] clrF_pins (by taint_decide)
    (fun q s ⟨o, st, g⟩ => load_ok ⟨o, 0, st, g⟩ .edx (by decide) (by decide))
    (loaded_pins .edx (i := 0) (.inl rfl)) (by taint_decide)

theorem clearHi_ct : RelCT isa (Two ClrF) (.seq (.block (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++
    ([.alu .add .edx (.reg .ecx), .alu .add .edx (.reg .ebp), .mov .eax (.imm 0)] : List Instr))) zeroLoop)
    fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := ZeroHi) ?_ fun q t h => clearHiB_ok h) (two_taint _ zeroHi_pins (by taint_decide))
  rw [show (([.mov .edx (.mem (param 0 0))] : List Instr) ++ four ++
      ([.alu .add .edx (.reg .ecx), .alu .add .edx (.reg .ebp), .mov .eax (.imm 0)] : List Instr)) =
    [.mov .edx (.mem (param 0 0))] ++ (four ++ [.alu .add .edx (.reg .ecx), .alu .add .edx (.reg .ebp),
      .mov .eax (.imm 0)]) from rfl]
  exact two_split0 _ _ [.esp, .ebp] [.edx, .esp, .ebp] clrF_pins (by taint_decide)
    (fun q s ⟨o, st, g⟩ => load_ok ⟨o, 0, st, g⟩ .edx (by decide) (by decide))
    (loaded_pins .edx (i := 0) (.inl rfl)) (by taint_decide)

theorem clear_around_ct : RelCT isa (Two ClrF) clearAround fun _ _ => True := by
  unfold clearAround
  exact RelCT.seq (two_post (Ψ := ClrF) clearLo_ct fun q t ⟨o, st, g⟩ =>
    WP.mono (clearLow_ok g) fun u h => ⟨o, st, h.1⟩) clearHi_ct

/-! ## Entry and return -/

/-- The point a run starts at. -/
def initialPoint (s : State) : GenPoint :=
  ⟨genOfState s, 0, (genProgress s).left, phaseWord (genProgress s).phase, (genProgress s).remaining,
    word s.mem (arg s 7) 24, (genResult s).trace⟩

/-- A run's entry at a point. -/
def GenStart (q : GenPoint) (s : State) : Prop := contract.pre s ∧ initialPoint s = q

theorem GenStart.input {q : GenPoint} {s : State} (h : GenStart q s) : GenInput q.inputs s :=
  ⟨h.1, by rw [← h.2]; rfl⟩

/-- A run's entry, past the pushes. -/
def PushCT (q : GenPoint) (a : State) : Prop := ∃ s, GenStart q s ∧ a = pushed pushRegs s

/-- The state's pointer loaded. -/
def EntryPins (q : GenPoint) (t : State) : Prop := t.gpr .eax = q.inputs.stp ∧ t.gpr .esp = q.inputs.S1

theorem push_pins : Pins PushCT [.esp] := by
  rintro q _ _ ⟨s, h₁, rfl⟩ ⟨t, h₂, rfl⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  rw [(push_base h₁.input).sp, (push_base h₂.input).sp]

theorem entry_pins (q : GenPoint) (a : State) (h : PushCT q a) :
    WP isa (.block [.mov .eax (.mem (param 0 7))]) a (EntryPins q) := by
  obtain ⟨s, hs, rfl⟩ := h
  have hi := hs.input
  obtain hb := push_base hi
  refine WP.mono (WP.blockKeep [.eax] (Q := fun t => t.gpr .eax = arg s 7) ?_ (by rfl))
    fun t ⟨e, k, _⟩ => ⟨by rw [e, hi.stp_eq], (k.gpr (by decide)).trans hb.sp⟩
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 7) (d := 48) rfl, hb.arg_in (i := 7) (by decide),
    hb.arg_val (i := 7) (by decide)]

theorem entry_ct : RelCT isa (Two PushCT) (.block entry) fun _ _ => True := by
  rw [show entry = [.mov .eax (.mem (param 0 7))] ++ entry.drop 1 from rfl]
  exact two_split0 _ _ [.esp] [.eax, .esp] push_pins (by taint_decide) entry_pins
    (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

/-- Past the entry, at the point. -/
def ClrCT (q : GenPoint) (t : State) : Prop :=
  ∃ s, GenStart q s ∧ GenFrame q.inputs s 0 (genProgress s) t ∧ t.gpr .ebx = 4 ∧
    t.mem = (pushed pushRegs s).mem

theorem entry_post (q : GenPoint) (a : State) (h : PushCT q a) : WP isa (.block entry) a (ClrCT q) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact WP.mono (entry_ok hs.input) fun t ⟨g, hb, hm⟩ => ⟨s, hs, g, hb, hm⟩

theorem start_point (q : GenPoint) (t : State) (h : ClrCT q t) : WP isa clearAround t (GenCTL q) := by
  obtain ⟨o, ⟨hpre, e⟩, g, hbx, hm⟩ := h
  subst e
  obtain hp : GenInput (genOfState o) o := ⟨hpre, rfl⟩
  have A := hp.abi
  have hv := hp.len_valid
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  refine WP.mono (clearAround_ok g hbx ?other) fun u ⟨hl, fr⟩ =>
    ⟨o, genProgress o, ⟨rfl, rfl, rfl, by simp only [tailOf]; rfl⟩, hl, ?_⟩
  case other =>
    intro pB hph
    simp only [genProgress, keyProgressAt] at hph
    split at hph
    · cases hph
    · injection hph with hph'
      subst hph'
      rw [hm]
      obtain hf := pushed_frame (rs := pushRegs) (s := o) (by decide)
        (by simp only [List.length_cons, List.length_nil]; omega_using [h1])
      obtain hk : Region.Sub ⟨(genOfState o).slot 4, (genOfState o).L⟩ (kR o) := by
        rw [hp.kR_eq]; exact Offset.sub_base _ (by omega_using [])
      exact bytes_keep (R := ⟨(genOfState o).slot 4, (genOfState o).L⟩) hf (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact (A.lowK.symm.sub_left hk).sub_right (by rw [hp.low_eq]; exact below_sub (by decide) A.stackLow))
        (show (genOfState o).L ≤ 2 ^ 64 by omega_using [hv])
  show word u.mem (arg o 7) 24 = word o.mem (arg o 7) 24
  rw [word_keep fr fun r hr => ?_, hm]
  · exact hp.word_pushed (d := 24) (by decide)
  · obtain rfl := List.mem_singleton.mp hr
    exact A.ks.symm.sub_left (Offset.sub_base _ (by decide))

/-! ## The whole controller -/

theorem body_ct (srch : Srch) (key : KeyImpl) :
    RelCT isa (Two PushCT) (body srch.call key.call) fun _ _ => True := by
  unfold body
  exact RelCT.seq (two_post entry_ct entry_post)
    (RelCT.seq (two_post (two_map id (fun q t ⟨o, _, g, _, _⟩ => ⟨o, _, g⟩) clear_around_ct) start_point)
      (RelCT.seq (two_post (loop_ct srch key) (loop_done srch key)) finish_ct))

theorem code_ct (srch : Srch) (key : KeyImpl) :
    RelCT isa (Two GenStart) (code srch.call key.call) fun _ _ => True := by
  unfold code
  refine RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ ⟨q, h₁, h₂⟩ => ?_) ?_
  · exact (congrArg (fun q => q.inputs.sp) h₁.2).trans (congrArg (fun q => q.inputs.sp) h₂.2).symm
  · exact (body_ct srch key).mono (fun a b ⟨s₁, s₂, ⟨q, h₁, h₂⟩, e₁, e₂⟩ => ⟨q, ⟨s₁, h₁, e₁⟩, ⟨s₂, h₂, e₂⟩⟩)
      fun _ _ h => h

theorem word_bytes {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {j : Nat} (hj : j < 8) :
    m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m₁ a hj, ← Mem.extractLsb'_read m₂ a hj]
  exact congrArg (BitVec.extractLsb' (8 * j) 8) h

theorem initial_point_eq {s t : State} (H : contract.pub s t) : initialPoint s = initialPoint t := by
  sig_pub [contract, Spec.RsaKeyGen.keySearchContract, Spec.RsaKeyGen.keySearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  obtain ⟨hsp, sy, L, a0, -, a2, a3, a4, a5, a6, a7⟩ := H
  obtain ⟨L₁, htr⟩ := List.append_inj L (by simp [Spec.Rsa.wordsAt])
  obtain ⟨hw, -⟩ := List.append_inj L₁ (by simp [Spec.Rsa.wordsAt])
  obtain hj : ∀ j < 7, s.mem.readW ((arg s 7).setWidth 64 + BitVec.ofNat 64 (8 * j)) 64 =
      t.mem.readW ((arg t 7).setWidth 64 + BitVec.ofNat 64 (8 * j)) 64 := fun j hj' => by
    have := congrArg (fun l => l[j]?) hw
    simp only [Spec.Rsa.wordsAt, List.getElem?_map, List.getElem?_range hj', Option.map_some,
      Option.some.injEq] at this
    exact BitVec.eq_of_toNat_eq this
  obtain w0 := hj 0 (by decide)
  obtain w1 := hj 1 (by decide)
  obtain w3 := hj 3 (by decide)
  obtain w4 := hj 4 (by decide)
  obtain w5 := hj 5 (by decide)
  obtain w6 := hj 6 (by decide)
  simp only [Nat.reduceMul] at w0 w1 w3 w4 w5 w6
  rw [a7] at w0 w1 w3 w4 w5 w6
  obtain he : genE s = genE t := by
    simp only [genE, Spec.Rsa.bytesAt, a7]
    refine List.map_congr_left fun i hi => ?_
    exact word_bytes (m₁ := s.mem) (m₂ := t.mem) (a := (arg t 7).setWidth 64 + BitVec.ofNat 64 48) w6
      (List.mem_range.mp hi)
  obtain hL : genLen s = genLen t := by
    simp only [genLen, a7]
    exact congrArg BitVec.toNat w1
  obtain hG : genOfState s = genOfState t := by
    simp only [genOfState, a0, a2, a3, a4, a5, a6, a7, hsp, hL, he, sy]
  obtain hpw : phaseWord (genProgress s).phase = phaseWord (genProgress t).phase := by
    obtain e4 : (s.mem.readW ((arg t 7).setWidth 64 + 32) 64).toNat =
        (t.mem.readW ((arg t 7).setWidth 64 + 32) 64).toNat := congrArg BitVec.toNat w4
    simp only [genProgress, keyProgressAt, a7, e4]
    split <;> rfl
  obtain hl : (genProgress s).left = (genProgress t).left := by
    obtain e5 : (s.mem.readW ((arg t 7).setWidth 64 + 40) 64).toNat =
        (t.mem.readW ((arg t 7).setWidth 64 + 40) 64).toNat := congrArg BitVec.toNat w5
    simp only [genProgress, keyProgressAt, a7, e5]
  obtain hr : (genProgress s).remaining = (genProgress t).remaining := by
    obtain e0 : (s.mem.readW ((arg t 7).setWidth 64) 64).toNat = (t.mem.readW ((arg t 7).setWidth 64) 64).toNat := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using congrArg BitVec.toNat w0
    simp only [genProgress, keyProgressAt, a7, e0]
  have htr' : (genResult s).trace = (genResult t).trace := htr
  have w3' : word s.mem (arg t 7) 24 = word t.mem (arg t 7) 24 := w3
  simp only [initialPoint, hG, hpw, hl, hr, htr', a7, w3']

theorem constantTime (srch : Srch) (key : KeyImpl) :
    ConstantTime isa contract.pre contract.pub (code srch.call key.call) := by
  intro s t tr ur sf tf S T H E F
  exact (code_ct srch key _ _ _ _ _ _ ⟨initialPoint s, ⟨S, rfl⟩, ⟨T, (initial_point_eq H).symm⟩⟩ E F).1

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The verified key search (i686)

The controller calling the prime search for the shared round `v`
(`srchOf`) and the key (`keyImpl`), as
`Generic/MillerRabin/X86/RsaKeyGen.lean` registers it.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MillerRabin.X86 (RoundImpl)

/-! ## The callees -/

theorem frame_noSp {b : Prog isa} (hb : NoSp b) :
    NoSp (.frame (.push [.ebx, .ebp, .esi, .edi]) b (.pop .ebx 4)) := fun i hi => by
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hb i hi
  · rfl

theorem search_noSp (v : RoundImpl) : NoSp (Search.searchCode v) :=
  frame_noSp (Search.body_noSp' (Search.Cand.ofRound v))

theorem search_stack (v : RoundImpl) : stackUse (Search.searchCode v) ≤ 216 := by
  obtain h := (Search.Cand.ofRound v).stack
  obtain hb : stackUse (Impl.RsaKeyGen.X86.Search.body (Search.Cand.ofRound v).call) ≤ 200 := by
    simp only [Search.Cand.call, Impl.RsaKeyGen.X86.Search.body, Impl.RsaKeyGen.X86.Search.iteration,
      Impl.RsaKeyGen.X86.Search.candidateStep, Impl.RsaKeyGen.X86.Search.candidateRun,
      Impl.RsaKeyGen.X86.Search.classify, Impl.RsaKeyGen.X86.Search.reject, Impl.RsaKeyGen.X86.Search.short,
      Impl.RsaKeyGen.X86.Search.exhausted, Impl.RsaKeyGen.X86.Search.zeroOut, Impl.RsaKeyGen.X86.Search.callWords,
      stackUse, frameBytes, Nat.max_le]
    omega_using [h]
  show stackUse (Impl.RsaKeyGen.X86.Search.body (Search.Cand.ofRound v).call) + 16 ≤ 216
  omega_using [hb]

/-- The prime search calling the shared round `v`. -/
def srchOf (v : RoundImpl) : Srch where
  name := "vg_rsa_prime_search" ++ v.suffix
  code := Search.searchCode v
  verified := Search.search_verified v
  noSp := search_noSp v
  stack := search_stack v

theorem key_noSp : NoSp VG.Impl.RsaKeyGen.X86.KeyRuntime.code :=
  frame_noSp (noSp_seq KeyRuntime.body_noSp (noSp_block (by decide)))

theorem key_stack : stackUse VG.Impl.RsaKeyGen.X86.KeyRuntime.code ≤ 68 := by decide

/-- The key. -/
def keyImpl : KeyImpl where
  name := "vg_rsa_keygen_key"
  code := VG.Impl.RsaKeyGen.X86.KeyRuntime.code
  verified := KeyRuntime.verified
  noSp := key_noSp
  stack := key_stack

/-- The controller calling them. -/
abbrev genCode (v : RoundImpl) : Prog isa := Impl.RsaKeyGen.X86.Generate.code (srchOf v).call keyImpl.call

theorem gen_noSp (v : RoundImpl) : NoSp (genCode v) := frame_noSp (body_noSp' (srchOf v) keyImpl)

/-- No instruction of the controller, its callees' included, writes `esp`. -/
theorem genCode_sp (v : RoundImpl) : (genCode v).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  obtain equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  rw [equal, Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simpa using gen_noSp v i hi

/-! ## A state the contract allows -/

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 288
  | 2 => 0x2000
  | 3 => 0x3000
  | 4 => 0
  | 5 => 0x10000
  | 6 => 1056
  | _ => 0x6000

/-- The arguments; a state with no candidates left, primes of 32 octets and
the budget `32769 · 32 = 0x100020`; RSA's table at `0x30000`. -/
def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 32 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else if a = 0x6008 then 0x20
  else if a = 0x6010 then 0x20
  else if a = 0x6012 then 0x10
  else constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x3000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x1000, 288⟩, ⟨0x2000, 8⟩, ⟨0x10000, 8448⟩, ⟨0x6000, 56⟩, ⟨0x20004, 32⟩]
  syms _ := 0x30000

theorem sat_arguments (i : Nat) (index : i < 8) : arg satState i = satArgument i := by
  obtain cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sat_single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

theorem sat_packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

theorem sat_table : Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply sat_single_held
  intro i index
  obtain fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
  obtain small : i < 1024 := by simpa only [VG.Proof.RsaKeyGen.X86.Candidate.packed_length] using index
  obtain ix : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; exact small
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  obtain held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i ix
  refine Eq.trans (Mem.readW_congr (m := satMemory) (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_)
    held
  intro j bound
  obtain address : ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat =
      65532 + 8 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [small, bound]
  obtain far : ∀ c : Addr, c.toNat < 0x10000 →
      0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j ≠ c := by
    intro c hc e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega_using [small, bound, hc, this]
  change (if _ then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun inside => by
      change ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 32 at inside
      rw [address] at inside; omega_using [inside]),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6008 (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6010 (by decide))),
    ite_eq_right_of_eq_false _ _ (eq_false (far 0x6012 (by decide)))]

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, Spec.RsaKeyGen.keySearchContract, Spec.RsaKeyGen.keySearchSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide)]
  simp only [sat_packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)
    | (unfold Spec.RsaKeyGen.primeLenValid; decide +kernel)
    | decide +kernel
    | rfl
  all_goals done

/-! ## The controller -/

theorem gen_verified (v : RoundImpl) : Verified target (genCode v) contract :=
  ⟨correct (srchOf v) keyImpl, constantTime (srchOf v) keyImpl, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Generate
