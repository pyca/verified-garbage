module

public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainMath
public import VerifiedGarbage.Impl.Bignum.AArch64.DiagonalChain
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Execute the single addition carry chain without dropping the shift bit. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.DiagonalChain
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem carry_bound (s : State) : carry s ≤ 2 := by
  have h := (s.gpr .x5).isLt
  have hc := Bool.toNat_le s.c
  unfold carry
  omega_arith

theorem exec_extr63 {s : State} {d n m : Reg} :
    exec (.extr .x d n m 63) s =
      some (s.write .x d ((s.gpr n ++ s.gpr m).extractLsb' 63 64)) := rfl

theorem core_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.DiagonalChain.core) s fun t =>
      ((t.gpr .x3).toNat + 2^64*(t.gpr .x6).toNat + 2^128*carry t =
        2*((s.gpr .x3).toNat+2^64*(s.gpr .x4).toNat) +
          (s.gpr .x2).toNat+2^64*(s.gpr .x1).toNat+carry s ∧
        t.mem = s.mem) ∧ Keep [.x3,.x5,.x6] s t := by
  refine WP.keep [.x3,.x5,.x6] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.DiagonalChain.core
  brun [exec_extr63, carry]
  simpa only [carry, shifted, off, BitVec.ofNat_add, BitVec.add_assoc, Nat.add_assoc] using
    pair_val (s.gpr .x2) (s.gpr .x1) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) s.c

end VG.Proof.Bignum.AArch64.DiagonalChain
