module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Restore p's arithmetic base and select the current h tape chunk -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem generatorArguments_ok {s : State} {frame : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s frame) (W : FrameWords s.mem frame words) :
    WP isa (.block (workspaceBase ++ ([.mov .esi (.mem (frameSlot 21))] : List Instr))) s fun t =>
      t.gpr .edi = words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .esi = words 21 ∧ t.mem = s.mem ∧ Keeps [.edi, .esi] s t := by
  change WP isa (.block (bufferPointer .edi VG.Impl.Dsa.Generation.Layout.arithmetic ++ _)) s _
  refine WP.block_append (WP.mono (bufferPointer_ok F (W 5 (by decide)) .edi _) fun a ⟨di, mem, Ka⟩ => ?_)
  have Fa := F.keeps Ka (by decide)
  have Wa : FrameWords a.mem frame words := by rw [mem]; exact W
  refine wp_movS (Fa.readWord Wa (by decide : 21 < 37)) fun t at' _ => WP.block_nil ?_
  exact ⟨(at'.other _ (by decide)).trans di, at'.gpr, at'.mem.trans mem,
    (Ka.mono (by decide)).trans (at'.keeps.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
