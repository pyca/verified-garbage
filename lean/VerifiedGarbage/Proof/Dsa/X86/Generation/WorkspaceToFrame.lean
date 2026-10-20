module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32

/-! # Return a prime-test result or witness cursor to its persistent slot -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem workspaceToFrame_ok {s : State} {frame base : Addr} {size index offset : Nat}
    {words : Nat → BitVec 32} (F : SearchFrame s frame) (S : Scr s base size)
    (R : FrameWords s.mem frame words) (hi : index < 37) (room : offset + 4 ≤ size) :
    WP isa (.block (workspaceToFrame offset index)) s fun t =>
      SearchFrame t frame ∧ Scr t base size ∧
      FrameWords t.mem frame (frameUpdate words index (s.mem.readW (off base offset) 32)) ∧
      t.mem = s.mem.writeW (off frame (4 * index)) (s.mem.readW (off base offset) 32) ∧
      Outside frame (4 * index) 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold workspaceToFrame
  refine wp_movS (readSrc_sc S room) fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  refine wp_storeS (Fa.ea hi) (Fa.writable hi) fun t at' => WP.block_nil ?_
  have K := sa.keeps.trans (at'.keeps [.eax])
  have mem : t.mem = s.mem.writeW (off frame (4 * index)) (s.mem.readW (off base offset) 32) := by
    rw [at'.mem, sa.gpr, sa.mem]
  exact ⟨F.keeps K (by decide), S.of_keeps K (by decide), by rw [mem]; exact R.write hi _, mem,
    by rw [mem]; exact writeW32_outside _ _ _ (by omega), K⟩
end VG.Proof.Dsa.X86.Generation
