module

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.TCB.Arm.Isa

/-! Cached attempts instantiate one shared callable Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm

def prepare : Prog isa := VG.Impl.Ffdh.Arm.CachedPrepare.code

def sample : Prog isa := VG.Impl.Ffdh.Arm.CachedSample.code

def tail (backend : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.KeyGenerate.tail
    (VG.Impl.Ffdh.Arm.CachedPower.code (MontCall.op backend.name backend.mul))

def code (backend : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample (tail backend)

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
