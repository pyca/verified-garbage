module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Load the current seed and q buffer while retaining the hash workspace -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem qHashArgs_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) :
    WP isa (.block qHashArgs) s fun t =>
      t.gpr .esi = words 1 ∧ t.gpr .edi = words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q ∧
      t.gpr .ebp = words 14 ∧ t.mem = s.mem ∧ Keeps [.esi, .edi, .ebp] s t := by
  unfold qHashArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (F.readWord R (by decide : 1 < 37)) fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  have saved : a.mem.readW (off base 20) 32 = words 5 := by rw [sa.mem]; exact R 5 (by decide)
  refine WP.block_append (WP.mono (bufferPointer_ok Fa saved .edi _) fun b ⟨di, mem, Kb⟩ => ?_)
  have K : Keeps [.esi, .edi, .ebp] s b := (sa.keeps.mono (by decide)).trans (Kb.mono (by decide))
  have Fb := F.keeps K (by decide)
  have Rb : FrameWords b.mem base words := by rw [mem, sa.mem]; exact R
  refine wp_movS (Fb.readWord Rb (by decide : 14 < 37)) fun t bt _ => WP.block_nil ?_
  exact ⟨(bt.other _ (by decide)).trans ((Kb.1 _ (by decide)).trans sa.gpr),
    (bt.other _ (by decide)).trans di, bt.gpr, bt.mem.trans (mem.trans sa.mem), K.trans (bt.keeps.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
