module

public import VerifiedGarbage.Impl.Bignum.Arm.ImportArray
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Exchange the public source and destination pointers for word import -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem importArraySwap_ok (s : State) :
    WP isa (.block importArraySwap) s fun t =>
      t.gpr .r0 = s.gpr .r1 ∧ t.gpr .r1 = s.gpr .r0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2] s t := by
  unfold importArraySwap
  refine wp_mov (op2_reg _ _) fun u a => ?_
  refine wp_mov (op2_reg _ _) fun v b => ?_
  refine wp_mov (op2_reg _ _) fun t c => WP.block_nil ?_
  exact ⟨(c.other .r0 (by decide)).trans (b.gpr.trans (a.other .r1 (by decide))),
    c.gpr.trans ((b.other .r2 (by decide)).trans a.gpr),
    c.mem.trans (b.mem.trans a.mem),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩

end VG.Proof.Bignum.Arm
