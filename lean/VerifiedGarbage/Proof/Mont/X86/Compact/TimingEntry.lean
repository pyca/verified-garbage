module

public import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingBase
import VerifiedGarbage.Proof.Framework.Offset

/-! # Only cdecl arguments above the saved-register frame are public -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Entry.saved_sp_nat {s : State} (A : Entry s) :
    ((entered s).gpr .esp).toNat + 16 = (s.gpr .esp).toNat := by
  rw [entered, pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat A.stackFit]
  have := A.stackFit
  omega

theorem Entry.saved_argByte {s : State} (A : Entry s) (k : Nat) :
    VG.X86.Taint.argByte (entered s) (16 + k) = VG.X86.Taint.argByte s k := by
  have H := VG.X86.Taint.argByte_move (s := s) (s' := entered s) (d := 0) (d' := 16)
    (by rw [A.saved_sp_nat, Nat.add_zero]) k
  simpa only [Nat.zero_add] using H

theorem Entry.timing_wf {s : State} (A : Entry s) : VG.X86.Taint.Wf (timingTaint []) (entered s) := by
  have top := A.stackBound
  have position := A.saved_sp_nat
  have addrBase : VG.X86.Taint.argByte (entered s) 16 = (s.gpr .esp).setWidth 64 := by
    have H := A.saved_argByte 0
    simpa only [Nat.add_zero, VG.X86.Taint.argByte, BitVec.add_zero] using H
  have frameBase : below (s.gpr .esp) 16 = ⟨((entered s).gpr .esp).setWidth 64, 16⟩ := by
    unfold entered savedRegisters below
    rw [pushed_esp]
    rfl
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, ?_, fun _ h => (List.not_mem_nil h).elim,
    ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
  · intro _
    refine ⟨by change ((entered s).gpr .esp).toNat + 16 + 24 ≤ 2 ^ 32; omega, ?_⟩
    intro r member
    change (⟨VG.X86.Taint.argByte (entered s) 16, 24⟩ : Region).Disjoint r
    rw [addrBase]
    rw [entered, pushed_wr, A.wr] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change (⟨(s.gpr .esp).setWidth 64, 24⟩ : Region).Disjoint (below (s.gpr .esp) 16)
      unfold below
      rw [Taint.sub_setWidth A.stackFit]
      exact Offset.base_disjoint_below _ (by decide)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) A.returnSeparate A.argSeparate.symm
  · change ((entered s).gpr .esp).toNat + 16 < 2 ^ 32
    rw [position]
    exact (s.gpr .esp).isLt
  · intro p member
    change p ∈ [(0, 0, 16)] at member
    obtain rfl := List.mem_singleton.mp member
    change (entered s).wr[0]? = some ⟨addr ((entered s).gpr .esp) 0, 16⟩
    change some (below (s.gpr .esp) 16) = some ⟨addr ((entered s).gpr .esp) 0, 16⟩
    rw [frameBase]
    simp only [addr, BitVec.add_zero]

theorem entered_agree {s t : State} (A : Entry s) (B : Entry t)
    (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i < 5, arg s i = arg t i) :
    VG.X86.Taint.Agree (timingTaint []) (entered s) (entered t) := by
  have savedSp : (entered s).gpr .esp = (entered t).gpr .esp := by
    rw [entered, entered, pushed_esp, pushed_esp, sp]
  refine ⟨⟨?_, fun h => nomatch h⟩, fun h => absurd rfl h, A.timing_wf, B.timing_wf,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => savedSp, ?_⟩
  · intro r member
    simp only [timingTaint, RegSet.mem_ofList, List.mem_singleton] at member
    subst r; exact savedSp
  · intro k low high
    change (entered s).mem (VG.X86.Taint.argByte (entered s) (16 + k)) =
      (entered t).mem (VG.X86.Taint.argByte (entered t) (16 + k))
    have bound : k < 24 := high
    rw [A.saved_argByte, B.saved_argByte, VG.X86.Taint.argByte_eq (by have := A.stackBound; omega) low bound,
      VG.X86.Taint.argByte_eq (by have := B.stackBound; omega) low bound,
      Mem.readW_byte (entered s).mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte (entered t).mem _ (Nat.mod_lt _ (by decide)),
      A.pushed_arg (by omega), B.pushed_arg (by omega), args _ (by omega)]

end VG.Proof.Mont.X86.Compact
