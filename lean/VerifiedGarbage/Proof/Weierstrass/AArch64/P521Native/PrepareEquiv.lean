module

-- separate module: the trace-preserving loop-normalization lemma is generic and independent of the ECDH workspace layout

public import VerifiedGarbage.Proof.Framework.Block

/-! Empty terminal blocks from the native sequence builder preserve loop semantics. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG

theorem exec_loop_append_nil {M : ISA} {body : Prog M} {c : M.Cond} {s t : M.State} {trace : List Leak}
    (h : Exec M (.loop body c) s trace t) : Exec M (.loop (.seq body (.block [])) c) s trace t := by
  generalize he : Code.loop body c=program at h
  induction h with
  | loopExit hb hc _ =>
    cases he
    simpa only [List.append_nil] using Exec.loopExit (Exec.seq hb (Exec.block (is:=[]) (t:=[]) rfl)) hc
  | loopNext hb hc _ _ ih =>
    cases he
    simpa only [List.append_nil] using Exec.loopNext (Exec.seq hb (Exec.block (is:=[]) (t:=[]) rfl)) hc (ih rfl)
  | block _ => cases he
  | seq _ _ _ _ => cases he
  | iteT _ _ _ => cases he
  | iteF _ _ _ => cases he
  | call _ _ _ _ => cases he
  | frame _ _ _ _ => cases he
  | icall _ _ _ _ _ => cases he
  | icallNext _ _ _ _ => cases he


theorem wp_loop_append_nil {M : ISA} {body : Prog M} {c : M.Cond} {s : M.State} {Q : M.State → Prop}
    (h : WP M (.loop body c) s Q) : WP M (.loop (.seq body (.block [])) c) s Q := by
  obtain ⟨trace,t,run,post⟩ := h
  exact ⟨trace,t,exec_loop_append_nil run,post⟩

end VG.Proof.Weierstrass.AArch64.P521Native
