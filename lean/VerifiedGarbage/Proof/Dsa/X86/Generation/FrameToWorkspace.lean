module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Mont.Words32

/-! # Copy a persistent frame word into the disjoint arithmetic workspace -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem frameToWorkspace_ok {s : State} {frame base : Addr} {size index offset : Nat}
    {words : Nat → BitVec 32} (F : SearchFrame s frame) (S : Scr s base size)
    (R : FrameWords s.mem frame words) (hi : index < 37) (room : offset + 4 ≤ size)
    (apart : Region.Disjoint ⟨frame, frameBytes⟩ ⟨base, size⟩) :
    WP isa (.block (frameToWorkspace index offset)) s fun t =>
      SearchFrame t frame ∧ Scr t base size ∧ FrameWords t.mem frame words ∧
      t.mem = s.mem.writeW (off base offset) (words index) ∧
      Outside base offset 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold frameToWorkspace
  refine wp_movS (F.readWord R hi) fun a sa _ => ?_
  have Sa := S.of_keeps sa.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write room) fun t at' => WP.block_nil ?_
  have K := sa.keeps.trans (at'.keeps [.eax])
  have mem : t.mem = s.mem.writeW (off base offset) (words index) := by rw [at'.mem, sa.gpr, sa.mem]
  have O : Frame [⟨off base offset, 4⟩] s.mem t.mem := by
    rw [mem]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ 4)
  exact ⟨F.keeps K (by decide), S.of_keeps K (by decide), R.keep O (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact apart.sub_right (Offset.sub_base _ room)), mem,
    by rw [mem]; exact writeW32_outside _ _ _ (by have := S.nowrap; omega), K⟩
end VG.Proof.Dsa.X86.Generation
