module

public import VerifiedGarbage.Proof.Ed25519.Arm.Point16Verified
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

/-! # Ed25519's point addition and doubling, in radix `2^16`, on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Ed25519R16.Arm

open VG.Spec.Ed25519.Point16 VG.Impl.Ed25519.Arm.Point16 VG.Proof.Ed25519.Arm.Point16

/-- How the functions work. -/
def notes : List String := ["Uses baseline integer instructions. The function saves `r4` to `r9` \
  in its own working space and runs the complete addition formula as the ARMv7 Ed25519 code \
  inlined it: nine products of sixteen-limb field elements, by X25519's ARMv7 product (row by \
  row, with only the low 32-bit `mul`, then `lo + 38 hi` and the carry folded in), and \
  additions and subtractions, with the temporaries in bytes 576 to 1087. It then restores the \
  registers."]

def artifacts : List Artifact := [
  addApi.artifact Arm.target {
    notes := notes
    code := addFn
    verified := addFn_verified
    stack := 0 },
  doubleApi.artifact Arm.target {
    notes := notes
    code := doubleFn
    verified := doubleFn_verified
    stack := 0 }]

end VG.Artifacts.Ed25519R16.Arm
