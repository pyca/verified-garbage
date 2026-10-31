module

public import VerifiedGarbage.Proof.Ed25519.Arm.Pow250Verified
public import VerifiedGarbage.Proof.Ed25519.Arm.MulFnVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
import VerifiedGarbage.Proof.Ed25519.Arm.SpecConv
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap
import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
public import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
public import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
public import VerifiedGarbage.Proof.Ed25519.Arm.SpecConv
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.X25519.Arm.AddSub
public import VerifiedGarbage.Proof.X25519.Arm.Cswap

/-! # Products and powers in curve25519's field, in radix `2^16`, on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Gf25519R16.Arm

open VG.Spec.X25519.Field16 VG.Impl.Ed25519.Arm VG.Proof.Ed25519.Arm.Pow250

def artifacts : List Artifact := [
  mulApi.artifact Arm.target {
    code := mulFn
    verified := Proof.Ed25519.Arm.Mul.mulFn_verified
    stack := 0 },
  pow250Api.artifact Arm.target {
    code := pow250Fn
    verified := pow250Fn_verified
    stack := 0 }]

end VG.Artifacts.Gf25519R16.Arm
