module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive

/-! One public-value derivation program for every shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedDerive.code (MontCall.op b.name b.mul)

end VG.Proof.Ffdh.Arm.SharedDerive
