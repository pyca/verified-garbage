module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Impl.Weierstrass.AArch64.JointMixed
public import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
public import VerifiedGarbage.Impl.Weierstrass.AArch64.ArithmeticTable

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.P256Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64

def cfg : Joint.Cfg := ⟨Cfg.jacWinCfg p256,bitsAt 4 0,p256.sl ONEP,p256.combCfg.tsym⟩

def cachedOps : CachedJac.Ops where
  head := VG.Impl.P256.VerifyArithmetic.program cfg.K.M
    (VG.Impl.Weierstrass.CachedJac.head cfg.K.S cfg.K.R cfg.K.E)
  tail := VG.Impl.P256.VerifyArithmetic.program cfg.K.M (jacTail cfg.K.S cfg.K.R cfg.K.E cfg.K.D)
  double := VG.Impl.P256.VerifyDouble.double cfg.K.M cfg.K.S cfg.K.R cfg.K.D

def ops : Joint.Ops where
  table := ArithmeticTable.table cfg.K
  cache := CachedJac.cache cfg.K
  digitQ := CachedJac.digit cfg.K cachedOps
  double := VG.Impl.P256.VerifyArithmetic.double cfg.K.M cfg.K.S cfg.K.R
  mixedAdd := Joint.mixedAdd cfg.K cfg.K.R cfg.K.E cfg.K.D

def points : Prog isa := Joint.points cfg ops (p256.sl U) (p256.sl V)

def verify : Prog isa :=
  .seq (.block (Cfg.args p256)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith p256 (some D)) <|
  .seq (.block (Cfg.loadS p256)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer p256)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate p256) <|
  .seq (Cfg.scalars p256) <| .seq p256.nPow <| .seq (Cfg.uv p256) <|
  .seq points (Cfg.tail p256)

end VG.Impl.Ecdsa.Verify.AArch64.P256Joint
