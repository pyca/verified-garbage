import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport

/-! The comb has a public trace: its loops' counters (`esi`) are public, every address is the
workspace pointer `edi` plus a constant or `8 esi`, and the digits only reach masks. -/
namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem combMultiply_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) combMultiply
    (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

end VG.Proof.Ed25519.X86
