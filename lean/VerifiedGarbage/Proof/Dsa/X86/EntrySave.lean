module

public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! # Saving and restoring the x86 callee-saved registers -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

private theorem saved_fits : Fits 8272 Entry.savedRegisters := by decide

theorem entrySave_ok {s : State} {base : Addr} {size : Nat}
    (hb : (s.gpr .eax).setWidth 64 = base) (hf : (s.gpr .eax).toNat + size ≤ 2 ^ 32)
    (hs : 8272 ≤ size) (hw : (⟨base, size⟩ : Region) ∈ s.wr) :
    WP isa (.block Entry.save) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Saved t.mem (off base) s.gpr Entry.savedRegisters ∧ Frame [⟨base, size⟩] s.mem t.mem := by
  change WP isa (.block (saveCode .eax Entry.savedRegisters ++ [])) s _
  apply save_ofNat_ok Entry.savedRegisters saved_fits (by omega)
  · intro p hp
    rw [hb]
    exact ⟨_, hw, Offset.contains_base base (by have := saved_fits.1 p hp; omega)
      (by have := saved_fits.1 p hp; omega)⟩
  · intro t U
    refine WP.block_nil ⟨U.gpr, U.rd, U.wr, ?_, ?_⟩
    · rw [U.mem, hb]
      exact saveMem_saved_ofNat _ base _ saved_fits (by decide)
    · rw [U.mem, hb]
      apply saveMem_frame (by simp : (⟨base, size⟩ : Region) ∈ [⟨base, size⟩])
      intro p hp
      exact Offset.contains_base base (by have := saved_fits.1 p hp; omega)
        (by have := saved_fits.1 p hp; omega)

theorem entryRestore_ok {s : State} {base : Addr} {size : Nat} {g : Reg → BitVec 32}
    (hs : Scr s base size) (hz : 8272 ≤ size)
    (saved : Saved s.mem (off base) g Entry.savedRegisters) :
    WP isa (.block Entry.restore) s fun t => Restored s t g Entry.savedRegisters := by
  change WP isa (.block (restoreCode .edi
    ([(.ebx, 8256), (.ebp, 8260), (.esi, 8264)] ++ [(.edi, 8268)]) ++ [])) s _
  apply restoreBase_ok _ (by decide)
  · intro p hp
    have hb := saved_fits.1 p hp
    rw [addr_eq (by rw [hs.edi_toNat]; have := hs.nowrap; omega), hs.edi]
    exact hs.read (by omega)
  · intro p hp
    have hb := saved_fits.1 p hp
    rw [addr_eq (by rw [hs.edi_toNat]; have := hs.nowrap; omega), hs.edi]
    exact saved p hp
  · intro t H
    exact WP.block_nil H

end VG.Proof.Dsa.X86
