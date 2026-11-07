module


import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst

/-! # The header a generator-two step keeps

`HeaderKept base s t`: `t` has `s`'s first 256 bytes at `base`.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp op2_lsr op2_imm dpVal)

abbrev HeaderKept (base : BitVec 32) (s t : State) : Prop :=
  ∀ d, d + 4 ≤ 256 → t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32

end VG.Proof.Bignum.Arm.TwoExp
