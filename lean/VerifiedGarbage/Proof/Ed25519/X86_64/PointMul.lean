module

import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers

/-! Checkpoint generation and batch descent implement pointMul. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside ea_sc)

variable {fld : Arith} [EdArith fld]

theorem mulCounterInit_ok {s : State} {base : Addr} (hs : Scratch s base) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 count ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [mulCounterInit, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi, hw,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨Mem.readW_writeW_self64 _ _ _, fun r hr => ?_, rfl, trivial, ?_⟩
  · simp only [hr, ite_false]
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)

end VG.Proof.Ed25519.X86_64
