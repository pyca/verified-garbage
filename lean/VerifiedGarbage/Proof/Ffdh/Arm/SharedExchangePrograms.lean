module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange

/-! One shared-secret exponentiation program for every shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedExchange.code (MontCall.op b.name b.mul)

end VG.Proof.Ffdh.Arm.SharedExchange
