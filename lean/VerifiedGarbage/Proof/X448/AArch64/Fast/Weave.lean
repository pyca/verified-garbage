module

public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X448 on AArch64: interleaved code

Untrusted: everything here is checked by Lean. `weave a b` is a merge of
`a` and `b`, so for independent blocks it runs as `a` and then `b`.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64 VG.AArch64.Interleave
open VG.Impl.X448.AArch64.Fast (weave codeOf ops)

/-- Independent blocks, interleaved, run as the first and then the second. -/
theorem WP.weave {xb : Reg} {a b : List Instr} (hind : Indeps xb a b) {s : State}
    {Q : State → Prop} (h : WP isa (.block a) s fun t => WP isa (.block b) t Q) : WP isa (.block (weave a b)) s Q :=
  Interleave.WP.weave hind h

theorem block_codeOf {l : List Impl.X448.AArch64.Fast.Op} {s : State} {Q : State → Prop}
    (h : WP isa (ops l) s Q) : WP isa (.block (codeOf l)) s Q := by
  induction l generalizing s with
  | nil => exact h
  | cons o os ih =>
    rw [ops, WP.seq_iff] at h
    exact WP.block_append_iff.mpr (WP.mono h fun t ht => ih ht)

end VG.Proof.X448.AArch64.Fast
