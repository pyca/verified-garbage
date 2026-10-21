module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Impl.Weierstrass.AArch64.JointMixed
public import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
public import VerifiedGarbage.Impl.Weierstrass.AArch64.ArithmeticTable
public import VerifiedGarbage.Impl.P256.GTable9

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.P256Joint
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64

/-- P-256 as verification has it: its table is `[m]G`, `m = 1 … 256`, a comb of one window of nine
bits, in the static `VG_P256_GTAB` (`combConsts`), which the generator's digits of width nine
index. -/
def p256v : Cfg :=
  { p256 with tbl := Impl.P256.p256G9, start := Impl.P256.p256G9Start, tsym := "VG_P256_GTAB" }

/-- The generator's width-nine digits at 2112, past `Q`'s (at 1824) and below the table of `Q`'s
odd multiples (at 2848). -/
def cfg : Joint.Cfg := ⟨Cfg.jacWinCfg p256,2112,p256.sl ONEP,p256v.tsym,9⟩

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
