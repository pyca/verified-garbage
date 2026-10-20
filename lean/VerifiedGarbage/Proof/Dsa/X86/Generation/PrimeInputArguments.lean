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
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Select a candidate and restore the arithmetic base after trial division -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem primeInputArgs_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) :
    WP isa (.block primeInputArgs) s fun t =>
      t.gpr .edi = words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .esi = words 22 ∧ t.mem = s.mem ∧ Keeps [.edi, .esi] s t := by
  unfold primeInputArgs
  change WP isa (.block (bufferPointer .edi VG.Impl.Dsa.Generation.Layout.arithmetic ++ _)) s _
  refine WP.block_append (WP.mono (bufferPointer_ok F (R 5 (by decide)) .edi _) fun a ⟨di, mem, Ka⟩ => ?_)
  have Fa := F.keeps Ka (by decide)
  have Ra : FrameWords a.mem base words := by rw [mem]; exact R
  refine wp_movS (Fa.readWord Ra (by decide : 22 < 37)) fun t at' _ => WP.block_nil ?_
  exact ⟨(at'.other _ (by decide)).trans di, at'.gpr, at'.mem.trans mem,
    (Ka.mono (by decide)).trans (at'.keeps.mono (by decide))⟩

theorem trialArgs_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) :
    WP isa (.block trialArgs) s fun t => t.gpr .esi = words 22 ∧ t.gpr .edi = words 5 ∧
      t.mem = s.mem ∧ Keeps [.esi, .edi] s t := by
  unfold trialArgs
  refine wp_movS (F.readWord R (by decide : 22 < 37)) fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  have Ra : FrameWords a.mem base words := by rw [sa.mem]; exact R
  refine wp_movS (Fa.readWord Ra (by decide : 5 < 37)) fun t at' _ => WP.block_nil ?_
  exact ⟨(at'.other _ (by decide)).trans sa.gpr, at'.gpr, at'.mem.trans sa.mem,
    (sa.keeps.mono (by decide)).trans (at'.keeps.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
