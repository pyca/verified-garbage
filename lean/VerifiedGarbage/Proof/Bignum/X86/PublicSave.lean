module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Saving and restoring the x86 callee-saved registers -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

private theorem saved_fits : Fits 16 PublicFn.savedRegisters := by decide

theorem entrySave_ok {s : State} {base : Addr} {size : Nat}
    (hb : (s.gpr .eax).setWidth 64 = base) (hf : (s.gpr .eax).toNat + size ≤ 2 ^ 32)
    (hs : 16 ≤ size) (hw : (⟨base, size⟩ : Region) ∈ s.wr) :
    WP isa (.block PublicFn.save) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Saved t.mem (off base) s.gpr PublicFn.savedRegisters ∧ Frame [⟨base, size⟩] s.mem t.mem := by
  change WP isa (.block (saveCode .eax PublicFn.savedRegisters ++ [])) s _
  apply save_ofNat_ok PublicFn.savedRegisters saved_fits (by omega)
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
    (hs : Scr s base size) (hz : 16 ≤ size)
    (saved : Saved s.mem (off base) g PublicFn.savedRegisters) :
    WP isa (.block PublicFn.restore) s fun t => Restored s t g PublicFn.savedRegisters := by
  change WP isa (.block (restoreCode .edi
    ([(.ebx, 0), (.ebp, 4), (.esi, 8)] ++ [(.edi, 12)]) ++ [])) s _
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

end VG.Proof.Bignum.X86
