module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Load the caller's output buffer after the parameter search -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem outputArgs_ok {s : State} {base : Addr} {W : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base W) :
    WP isa (.block outputArgs) s fun t =>
      t.gpr .esi = W 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.packed ∧
      t.gpr .edx = W 6 ∧ t.gpr .ecx = W 7 ∧ t.gpr .ebx = BitVec.allOnes 32 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ecx, .edx, .esi] s t := by
  unfold outputArgs
  refine WP.block_append (WP.mono (bufferPointer_ok F (R 5 (by decide)) .esi _) fun a ⟨si, ma, Ka⟩ => ?_)
  have Fa := F.keeps Ka (by decide)
  have Ra : FrameWords a.mem base W := by rw [ma]; exact R
  refine wp_movS (Fa.readWord Ra (by decide : 6 < 37)) fun b ab _ => ?_
  have Fb := Fa.keeps ab.keeps (by decide)
  have Rb : FrameWords b.mem base W := by rw [ab.mem]; exact Ra
  refine wp_movS (Fb.readWord Rb (by decide : 7 < 37)) fun c bc _ =>
    wp_movS rfl fun t ct _ => WP.block_nil ?_
  have tail : Keeps [.ebx, .ecx, .edx] a t :=
    (ab.keeps.mono (by decide)).trans ((bc.keeps.mono (by decide)).trans (ct.keeps.mono (by decide)))
  exact ⟨(tail.1 _ (by decide)).trans si,
    (ct.other _ (by decide)).trans ((bc.other _ (by decide)).trans ab.gpr),
    (ct.other _ (by decide)).trans bc.gpr, ct.gpr,
    ct.mem.trans (bc.mem.trans (ab.mem.trans ma)),
    (Ka.mono (by decide)).trans (tail.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
