module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Candidate inputs and workspace are independent saved-buffer addresses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem candidateArgs_ok {s : State} {base : Addr} {parent : BitVec 32}
    (F : SearchFrame s base) (saved : s.mem.readW (off base 20) 32 = parent) :
    WP isa (.block candidateArgs) s fun t =>
      t.gpr .esi = parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped ∧
      t.gpr .ecx = parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q ∧
      t.gpr .edi = parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic ∧
      t.mem = s.mem ∧ Keeps [.esi, .ecx, .edi] s t := by
  unfold candidateArgs
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (bufferPointer_ok F saved .esi _) fun a ⟨si, ma, Ka⟩ => ?_)
  have Fa := F.keeps Ka (by decide)
  have savedA : a.mem.readW (off base 20) 32 = parent := ma ▸ saved
  refine WP.block_append (WP.mono (bufferPointer_ok Fa savedA .ecx _) fun b ⟨cx, mb, Kb⟩ => ?_)
  have Fb := Fa.keeps Kb (by decide)
  have savedB : b.mem.readW (off base 20) 32 = parent := mb ▸ savedA
  refine WP.mono (bufferPointer_ok Fb savedB .edi _) fun t ⟨di, mt, Kt⟩ => ?_
  exact ⟨(Kt.1 _ (by decide)).trans ((Kb.1 _ (by decide)).trans si),
    (Kt.1 _ (by decide)).trans cx, di, mt.trans (mb.trans ma),
    ((Ka.mono (by decide)).trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
