module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Packed hint count and norm-success bit, exactly as returned to the signer. -/
def hintFinishValue (counts failures : BitVec 128) : BitVec 64 :=
  (vword counts 0+vword counts 1+vword counts 2+vword counts 3).setWidth 64 |||
    (finishValue failures <<< 32)

end VG.Proof.MlDsa.AArch64.Optimized.Response
