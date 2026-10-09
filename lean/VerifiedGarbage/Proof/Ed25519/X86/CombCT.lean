import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum

/-! The comb has a public trace: its loops' counters (`esi`) are public, and every address is
the workspace pointer `edi` plus a constant or `8 esi`, or the tables' address plus
`768 esi` and a constant. The tables' address is the word at byte `combTbl` of the workspace,
which the comb never writes, public (`callTaint combTbl`): the digits only reach masks. The
final addition's call of `vg_ed25519_r32_point_add` is analysed as part of the comb. -/
namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem combMultiply_ct {x : BitVec 32} : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ s.gpr .esp = t.gpr .esp ∧
      wd s.mem x combTbl = wd t.mem x combTbl) combMultiply (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (callTaint combTbl) combMultiply h).isSome = true := by
    taint_decide_sum [addSum]
  apply VG.RelCT.taint (A := taint) (callTaint combTbl) _ hc
  intro s t ⟨hs, ht, hw, hsp, hv⟩
  exact callTaint_agree hs ht hw hsp (by decide) hv

end VG.Proof.Ed25519.X86
