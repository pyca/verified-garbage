module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32

/-! # Persistent-buffer address calculations preserve all memory -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem bufferPointer_ok {s : State} {base : Addr} {parent : BitVec 32}
    (F : SearchFrame s base) (saved : s.mem.readW (off base 20) 32 = parent) (reg : Reg) (offset : Nat) :
    WP isa (.block (bufferPointer reg offset)) s fun t =>
      t.gpr reg = parent + BitVec.ofNat 32 offset ∧ t.mem = s.mem ∧ Keeps [reg] s t := by
  unfold bufferPointer
  refine wp_movS (v := parent) (by rw [F.readSlot (by decide : 5 < 37), saved]) fun a sa _ =>
    wp_addi fun t at' => WP.block_nil ?_
  exact ⟨by rw [at'.gpr, sa.gpr], at'.mem.trans sa.mem, sa.keeps.trans at'.keeps⟩

theorem candidatePointer_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) (offset : Nat) :
    WP isa (.block (candidatePointer offset)) s fun t => SearchFrame t base ∧
      FrameWords t.mem base (frameUpdate words 22 (words 5 + BitVec.ofNat 32 offset)) ∧
      Outside base 88 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold candidatePointer
  refine WP.block_append (WP.mono (bufferPointer_ok F (R 5 (by decide)) .eax offset) fun a ⟨ax, mem, K⟩ => ?_)
  have Fa := F.keeps K (by decide)
  refine wp_storeS (Fa.ea (by decide : 22 < 37)) (Fa.writable (by decide : 22 < 37)) fun t at' => WP.block_nil ?_
  have memory : t.mem = s.mem.writeW (off base 88) (words 5 + BitVec.ofNat 32 offset) := by
    rw [at'.mem, ax, mem]
  exact ⟨Fa.keeps (at'.keeps []) (by decide), by rw [memory]; exact R.write (by decide : 22 < 37) _,
    by rw [memory]; exact writeW32_outside _ _ _ (by decide), K.trans (at'.keeps _)⟩
end VG.Proof.Dsa.X86.Generation
