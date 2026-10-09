import VerifiedGarbage.Proof.Framework.X86_64.Avx512

/-!
# The `zmm` comb: what the vector instructions keep

Untrusted: everything here is checked by Lean. `rfl` proofs of `t.mem = s.mem`,
for a state `t` built by vector instructions from `s` (often a local
definition), make the unifier compare the states field by field before it
reduces the projection, for seconds; `zkeep` rewrites with the frame lemmas
instead.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64

theorem zop_exec_syms (o : ZOp) (s : State) : (o.exec s).syms = s.syms := by
  cases o <;> rfl

theorem setV_syms (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).syms = s.syms := by
  cases s; rfl

theorem setZ_syms (s : State) (r : XReg) (a b c d : BitVec 128) : (s.setZ r a b c d).syms = s.syms := by
  cases s; rfl

theorem setMem_syms (s : State) (m : Mem) : (s.setMem m).syms = s.syms := by
  cases s; rfl

theorem vop_exec_syms (o : VOp) (s : State) : (o.exec s).syms = s.syms := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

/-- Closes `t.f = s.f` for `f` the memory, the regions, the registers or the statics, `t` built
from `s` by vector instructions (unfolding local definitions). -/
macro "zkeep" : tactic => `(tactic| simp (config := { zetaDelta := true }) only [ZOp.exec_mem, ZOp.exec_rd,
  ZOp.exec_wr, ZOp.exec_gpr, zop_exec_syms, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, VOp.exec_gpr, vop_exec_syms,
  State.setV_mem, State.setV_rd, State.setV_wr, State.setV_gpr, setV_syms, State.setZ_mem, State.setZ_rd,
  State.setZ_wr, State.setZ_gpr, setZ_syms, State.setMem_rd, State.setMem_wr, State.setMem_gpr, setMem_syms])

end VG.Proof.Ed25519.X86_64.Zmm
