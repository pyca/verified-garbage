module

import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # A complete callable compact multiplication restores the i686 ABI -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

def savedRegisters : List Reg := [.ebx, .ebp, .esi, .edi]
def entered (s : State) : State := pushed savedRegisters s

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem frame_ok {s : State} {W : Addr} {L : Nat} {Q : Mem → Prop}
    (stackFit : 16 ≤ (s.gpr .esp).toNat)
    (savedFar : ∀ i < 4, ∀ j < 4,
      L ≤ ofs W (addr ((entered s).gpr .esp) (4 * i) + BitVec.ofNat 64 j))
    (returnFar : ∀ j < 4, L ≤ ofs W ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 j))
    (core : WP isa Compact.core (entered s) fun t =>
      Outside W 0 L (entered s).mem t.mem ∧ Q t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t) :
    WP isa Compact.body s fun t => abiPreserved s t ∧ Q t.mem := by
  unfold Compact.body
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit inner_noSp ?_
  refine WP.seq (WP.mono core fun t ⟨O, Qt, K⟩ => ?_)
  have sp : t.gpr .esp = (entered s).gpr .esp := K.1 .esp (by decide)
  have fit : ((entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [entered, pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := (s.gpr .esp).isLt
    omega
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
      rw [sp]
      exact Mem.readW_congr fun j hj => O _ (Or.inr (by simpa only [Nat.zero_add] using savedFar i hi j (by omega)))
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, value]
    exact congrArg some (pushed_word (rs := savedRegisters) (by decide) stackFit hi)
  refine WP.mono (restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro t' ⟨edi, esi, ebp, M, K'⟩
  have sp' : t'.gpr .esp = (entered s).gpr .esp := (K'.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show savedRegisters.length = 4 from rfl, popped_four_value, sp', M]
      have word := pushed_word (s := s) (rs := savedRegisters) (by decide) stackFit (i := 3) (by decide)
      have keep : t.mem.readW (addr ((entered s).gpr .esp) 12) 32 =
          (entered s).mem.readW (addr ((entered s).gpr .esp) 12) 32 :=
        Mem.readW_congr fun j hj => O _ (Or.inr (by simpa only [Nat.zero_add] using savedFar 3 (by decide) j (by omega)))
      exact keep.trans word
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', entered, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, M]
    have keep : t.mem.readW ((s.gpr .esp).setWidth 64) 32 =
        (entered s).mem.readW ((s.gpr .esp).setWidth 64) 32 :=
      Mem.readW_congr fun j hj => O _ (Or.inr (by simpa only [Nat.zero_add] using returnFar j (by omega)))
    refine keep.trans ?_
    have saved := pushed_frame (rs := savedRegisters) (s := s) (by decide) stackFit
    have separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
      unfold below
      rw [Taint.sub_setWidth stackFit]
      exact Offset.base_disjoint_below _ (by decide)
    exact saved.readW (Region.contains_self _ _) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)
  · rw [popped_mem, M]; exact Qt

end VG.Proof.Mont.X86.Compact
