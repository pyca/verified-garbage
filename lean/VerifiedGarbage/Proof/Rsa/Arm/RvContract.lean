module

public import VerifiedGarbage.Proof.Rsa.Arm.RvBody
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm

theorem test_pre (s : State) (h : (Spec.Rsa.recoverPrimesContract abi 56).pre s) : False := by
  sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  trace_state
  sorry

theorem test_post (s t : State) : (Spec.Rsa.recoverPrimesContract abi 56).post s t := by
  sig_post [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  trace_state
  sorry

theorem test_pub (s t : State) (h : (Spec.Rsa.recoverPrimesContract abi 56).pub s t) : False := by
  sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  trace_state
  sorry

end VG.Proof.Rsa.Arm.Recover
