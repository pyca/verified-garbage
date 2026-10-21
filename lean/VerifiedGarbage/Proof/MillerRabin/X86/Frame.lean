module

import VerifiedGarbage.Proof.MillerRabin.X86.BodyFrame
import VerifiedGarbage.Proof.MillerRabin.X86.SavedFrame
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryCore
import VerifiedGarbage.Proof.MillerRabin.X86.EntryArgs
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # The prepared round restores the i686 ABI after its nested calls -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem inner_noSp : NoSp (.seq (body montName montCode) (.block VG.Impl.Mont.X86.Compact.restoreRegs)) :=
  .of_all (by decide +kernel)

theorem Result.keep {s t u : State} (R : Result s t)
    (eax : u.gpr .eax = t.gpr .eax) (mem : u.mem = t.mem) : Result s u := by
  unfold Result at *
  rw [eax, mem]
  exact R

theorem Entry.framed {s : State} (E : Entry s) :
    WP isa (code montName montCode) s fun t => abiPreserved s t ∧ Result s t := by
  unfold code
  refine WP.frame (rs := Compact.savedRegisters) (by decide) (by decide) (by decide)
    (by change 16 ≤ _; have := E.stackFit; omega) inner_noSp ?_
  refine WP.seq (WP.mono E.body fun t ⟨R, K, F⟩ => ?_)
  have sp : t.gpr .esp = (entered s).gpr .esp := K.1 .esp (by decide)
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [entered, Compact.entered, pushed_esp]
    change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by have := E.stackFit; omega)]
    have := (s.gpr .esp).isLt
    omega
  have read (i : Nat) (index : i < 4) :
      readSrc t (.mem (at_ .esp (4 * i))) = some
        (s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp, entered, Compact.entered, pushed_wr]
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      rw [← savedRegion_eq]
      change (savedRegion s).Contains (addr ((entered s).gpr .esp) (4 * i)) 4
      rw [addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, E.saved_read F index]
  refine WP.mono (Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  have sp' : u.gpr .esp = (entered s).gpr .esp := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show Compact.savedRegisters.length = 4 from rfl, Compact.popped_four_value, sp', mem]
      exact E.saved_read F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', entered, Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact E.return_read F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]

end VG.Proof.MillerRabin.X86
