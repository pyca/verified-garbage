import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# AArch64: state updates kept folded during elaboration

`State.setV` is a structure update (`{ s with v := … }`). When a proof
unifies a state built from vector writes with another state (`rfl` for a
frame fact, a lemma applied with `_` arguments), `isDefEq` unfolds the
writes into structure literals and first tries to unify the structures,
which fails after a deep traversal: seconds for a few vector instructions
(TripleDes AArch64 bitsliced `Step`: 6.6 s to 2.9 s with this module; SHA-3
`AbsorbBlock`: 4.4 s to 2.1 s). A module importing this one sees `setV`
irreducible, and proves facts about it with `RegUpd`'s lemmas (proven
before the seal) and `upd_frame`. The seal is opt-in: import it in a module
once its proofs no longer unfold `setV` (`rfl`, `decide` through a state),
never in a module that others import before theirs are converted.

Reducibility only guides elaboration: the kernel ignores it, so nothing
about what is proven changes. Lean changes the reducibility of a
definition from another module only with `allowUnsafeReducibility`.
-/

namespace VG.AArch64.RegUpd

variable (s : State)

theorem c_setV (r : VReg) (x : BitVec 128) : (s.setV r x).c = s.c := rfl
theorem nf_setV (r : VReg) (x : BitVec 128) : (s.setV r x).nf = s.nf := rfl
theorem zf_setV (r : VReg) (x : BitVec 128) : (s.setV r x).zf = s.zf := rfl
theorem vf_setV (r : VReg) (x : BitVec 128) : (s.setV r x).vf = s.vf := rfl

/-- Closes a frame fact about a chain of updates (`s'.mem = s.mem`, …), unfolding
the `let`s that name the states. -/
macro "upd_frame" : tactic => `(tactic| simp (config := { zetaDelta := true }) only [
  VG.AArch64.RegUpd.mem_write, VG.AArch64.RegUpd.rd_write, VG.AArch64.RegUpd.wr_write,
  VG.AArch64.RegUpd.sp_write, VG.AArch64.RegUpd.c_write, VG.AArch64.RegUpd.nf_write,
  VG.AArch64.RegUpd.zf_write, VG.AArch64.RegUpd.vf_write, VG.AArch64.RegUpd.mem_addWithCarry,
  VG.AArch64.RegUpd.rd_addWithCarry, VG.AArch64.RegUpd.wr_addWithCarry,
  VG.AArch64.RegUpd.sp_addWithCarry, VG.AArch64.RegUpd.v_write, VG.AArch64.RegUpd.gpr_setV,
  VG.AArch64.RegUpd.mem_setV, VG.AArch64.RegUpd.rd_setV, VG.AArch64.RegUpd.wr_setV,
  VG.AArch64.RegUpd.sp_setV, VG.AArch64.RegUpd.c_setV, VG.AArch64.RegUpd.nf_setV,
  VG.AArch64.RegUpd.zf_setV, VG.AArch64.RegUpd.vf_setV])

end VG.AArch64.RegUpd

namespace VG.AArch64

set_option allowUnsafeReducibility true in
attribute [irreducible] State.setV

end VG.AArch64
