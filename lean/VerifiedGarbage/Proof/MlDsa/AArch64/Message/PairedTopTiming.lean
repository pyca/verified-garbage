module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedCallTiming

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots pairedSignRootConsts)
variable {p : Params}

structure SPub (p : Params) (s t : State) extends Message.SPub p s t where
  roots : rootsAt s=rootsAt t

end VG.Proof.MlDsa.AArch64.Message.Paired
