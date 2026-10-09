import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Optimized
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.AddSub
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenRound
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64

def primitives (c : Impl.Sha3.AArch64.Callee) : Prims :=
  { primsWith c with
    add := Impl.MlDsa.AArch64.Optimized.AddSub.code false
    power2Round := Impl.MlDsa.AArch64.Optimized.KeygenRound.power2Round
    simpleBitPack := Impl.MlDsa.AArch64.Optimized.KeygenPack.simple
    bitPack := Impl.MlDsa.AArch64.Optimized.KeygenPack.signed }

def keyGenWith (c : Impl.Sha3.AArch64.Callee) (p : Spec.MlDsa.Params) : Prog isa :=
  codeWith c (primitives c) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
