module

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.X86.Isa

/-! # The callee-saved registers' frame around the generator

`Compact.frame_ok`'s frame, around any body that keeps the saved registers'
slots and the return address. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Compact (savedRegisters entered popped_four_value)

theorem frameWith_ok {inner : Prog isa} (hns : NoSp (.seq inner (.block Compact.restoreRegs))) {s : State}
    {Q : Mem → BitVec 32 → Prop} (stackFit : 16 ≤ (s.gpr .esp).toNat) (stackTop : (s.gpr .esp).toNat + 4 ≤ 2 ^ 32)
    (core : WP isa inner (entered s) fun t =>
      (∀ x, (⟨((entered s).gpr .esp).setWidth 64, 20⟩ : Region).Contains x 1 → t.mem x = (entered s).mem x) ∧
      Q t.mem (t.gpr .eax) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t) :
    WP isa (.frame (.push [.ebx, .ebp, .esi, .edi]) (.seq inner (.block Compact.restoreRegs)) (.pop .ebx 4)) s
      fun t => abiPreserved s t ∧ Q t.mem (t.gpr .eax) := by
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit hns ?_
  refine WP.seq (WP.mono core fun t ⟨O, Qt, K⟩ => ?_)
  have sp : t.gpr .esp = (entered s).gpr .esp := K.1 .esp (by decide)
  have eNat : ((entered s).gpr .esp).toNat = (s.gpr .esp).toNat - 16 := by
    rw [entered, pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    have := (s.gpr .esp).isLt
    omega
  have keepAt : ∀ (k : Nat), k + 4 ≤ 20 → t.mem.readW (addr ((entered s).gpr .esp) k) 32 =
      (entered s).mem.readW (addr ((entered s).gpr .esp) k) 32 := fun k hk => by
    have address : addr ((entered s).gpr .esp) k = ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 k :=
      addr_eq (by omega)
    rw [address]
    exact Mem.readW_congr fun j hj => O _ (by
      rw [show ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 k + BitVec.ofNat 64 j =
          ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 (k + j) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
      exact Offset.contains_base _ (by omega) (by omega))
  have read (i : Nat) (hi : i < 4) :
      readSrc t (.mem (at_ .esp (4 * i))) = some (s.gpr (savedRegisters[3 - i]'(by
        change 3 - i < 4; omega))) := by
    have access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
      change (below (s.gpr .esp) 16).Contains _ 4
      have region : below (s.gpr .esp) 16 = ⟨((entered s).gpr .esp).setWidth 64, 16⟩ := by
        unfold entered savedRegisters below
        rw [pushed_esp]
        rfl
      rw [region]
      have address : addr ((entered s).gpr .esp) (4 * i) =
          ((entered s).gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i) := addr_eq (by omega)
      rw [address]
      exact Offset.contains_base _ (by omega) (by omega)
    have value : t.mem.readW (addr (t.gpr .esp) (4 * i)) 32 =
        (entered s).mem.readW (addr ((entered s).gpr .esp) (4 * i)) 32 := by
      rw [sp]; exact keepAt _ (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, value]
    exact congrArg some (pushed_word (rs := savedRegisters) (by decide) stackFit hi)
  refine WP.mono (VG.Proof.Mont.X86.Compact.restore_ok (read 0 (by decide)) (read 1 (by decide))
    (read 2 (by decide))) ?_
  rintro t' ⟨edi, esi, ebp, M, K'⟩
  have sp' : t'.gpr .esp = (entered s).gpr .esp := (K'.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show savedRegisters.length = 4 from rfl, popped_four_value, sp', M]
      have word := pushed_word (s := s) (rs := savedRegisters) (by decide) stackFit (i := 3) (by decide)
      have e12 : (((entered s).gpr .esp) + 12).setWidth 64 = addr ((entered s).gpr .esp) 12 := rfl
      rw [e12, keepAt 12 (by decide)]
      exact word
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', entered, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, M]
    have ret : (s.gpr .esp).setWidth 64 = addr ((entered s).gpr .esp) 16 := by
      unfold addr entered savedRegisters
      rw [pushed_esp]
      congr 1
      exact (BitVec.sub_add_cancel _ _).symm
    rw [ret, keepAt 16 (by decide), ← ret]
    have saved := pushed_frame (rs := savedRegisters) (s := s) (by decide) stackFit
    have separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
      unfold below
      rw [Taint.sub_setWidth stackFit]
      exact Offset.base_disjoint_below _ (by decide)
    exact saved.readW (Region.contains_self _ _) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)
  · rw [popped_mem, M, popped_gpr _ _ _ (by decide) (by decide), K'.1 .eax (by decide)]
    exact Qt

end VG.Proof.Dsa.X86.Generation
