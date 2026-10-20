module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
import VerifiedGarbage.Proof.Framework.AArch64.Syms
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64

theorem TransformTables.exec {s t : State} {c : Prog isa} {tr : List Leak}
 (h : TransformTables s) (he : Exec isa c s tr t) (hn : c.noFrames=true) : TransformTables t := by
 obtain ⟨hr,hw,hsp,hf⟩:=VG.AArch64.Exec.regions he hn
 exact h.frame (VG.AArch64.Exec.syms he) hr hw hsp hf (fun _ _ h=>h)

theorem WP.transformTables {s : State} {c : Prog isa} {Q : State→Prop}
 (h : WP isa c s Q) (ht : TransformTables s) (hn : c.noFrames=true) :
 WP isa c s fun t=>Q t ∧ TransformTables t := by
 obtain ⟨tr,t,he,hq⟩:=h
 exact ⟨tr,t,he,hq,ht.exec he hn⟩
end VG.Proof.MlKem.AArch64.Optimized
