import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport

/-! The comb has a public trace: its loops' counters (`esi`) are public, and every address is
the workspace pointer `edi` plus a constant or `8 esi`, or the tables' address plus
`768 esi` and a constant. The tables' address is the word at byte `combTbl` of the workspace,
which the comb never writes, public (`pointTaint combTbl`): the digits only reach masks. -/
namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem combMultiply_ct {x : BitVec 32} : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧
      wd s.mem x combTbl = wd t.mem x combTbl) combMultiply (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (pointTaint combTbl) _ (by taint_decide)
  intro s t ⟨hs, ht, hw, hv⟩
  exact pointTaint_agree hs ht hw (by decide) hv

end VG.Proof.Ed25519.X86
