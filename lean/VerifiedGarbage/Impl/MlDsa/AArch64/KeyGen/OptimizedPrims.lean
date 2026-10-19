module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Optimized
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64

def primitives (c : Impl.Sha3.AArch64.Callee) : Prims := primsWith c

def keyGenWith (c : Impl.Sha3.AArch64.Callee) (p : Spec.MlDsa.Params) : Prog isa :=
  codeWith c (primitives c) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
