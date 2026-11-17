module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTMul
public import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTMul
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
import VerifiedGarbage.Proof.Ed25519.Arm.PackField
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap
meta import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
meta import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
meta import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
meta import VerifiedGarbage.Proof.Ed25519.Arm.PackField
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
meta import VerifiedGarbage.Proof.Ed25519.Arm.Points
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.Arm.AddSub
meta import VerifiedGarbage.Proof.X25519.Arm.Cswap

/-! Public scalar pointers remain public across point preparation. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def pointFromPrepareCT : Prog isa :=
  .seq (.block [.str .r12 .r0 52]) (fieldCode false [.const 16 Spec.Ed25519.d])

end VG.Proof.Ed25519.Arm
