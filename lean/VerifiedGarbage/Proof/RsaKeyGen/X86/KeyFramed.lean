module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallSizes
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySaved
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpCode
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase

/-! # Callable native key assembly restores all cdecl registers and the return address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86

theorem BodyOutcome.keep {E : Environment} {m : Mem} {s t : State} (R : BodyOutcome E m s)
    (eax : t.gpr .eax = s.gpr .eax) (memory : t.mem = s.mem) : BodyOutcome E m t := by
  simpa only [BodyOutcome, WrittenCore, eax, memory] using R

theorem framed_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.code s fun t =>
      abiPreserved s t ∧ BodyOutcome (callEnvironment s) (Compact.entered s).mem t := by
  have A := call_layout h
  have I := entry_input h
  have savedFit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have inner : NoSp (.seq VG.Impl.RsaKeyGen.X86.Key.body (.block Compact.restoreRegs)) :=
    KeyNoSp.sequence KeyNoSp.body_noSp (NoSp.of_all (by rfl))
  unfold VG.Impl.RsaKeyGen.X86.Key.code
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

end VG.Proof.RsaKeyGen.X86.Key
