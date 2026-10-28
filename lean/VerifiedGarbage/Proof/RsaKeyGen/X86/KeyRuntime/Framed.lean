module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySaved
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Safety
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Body
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFramed
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target

/-! # Callable native key assembly restores all cdecl registers and the return address -/

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
