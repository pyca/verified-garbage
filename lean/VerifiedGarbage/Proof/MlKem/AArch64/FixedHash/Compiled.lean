module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedule
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Pad
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.SqueezeCode
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-- A proof-oriented decomposition of the measured fixed hash generator. -/
def compiled (c : Impl.Sha3.AArch64.Callee) (sc : Reg) (st wk rate sfx : Nat)
 (ins outs : List Piece) : Prog isa :=
 .seq (.block (zeroState sc st ++ [.str .x .x30 sc (wk+600)]))
 (.seq (compile c sc st wk rate (schedule rate ins).1)
 (.seq (.block (padCode sc st rate (schedule rate ins).2 sfx))
 (.seq (permute c sc st wk)
 (.seq (.block (squeezeCode sc st 0 outs)) (.block [.ldr .x .x30 sc (wk+600)])))))

end VG.Proof.MlKem.AArch64.FixedHash
