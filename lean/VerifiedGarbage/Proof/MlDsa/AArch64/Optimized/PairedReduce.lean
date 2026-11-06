module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec

import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask minMask)

/-- Register-parametric form used by the two interleaved final r0 lanes. -/
def reduceRegs (a t : VReg) : List Instr :=
 [.vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31)]

def normRegs (a t : VReg) : List Instr :=
 [.vop (.add .s4 t a .v9),.vop (.umin t t .v10),
  .vop (.cmeq .s4 t t .v10),.vop (.logic .orr .v30 .v30 t)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
