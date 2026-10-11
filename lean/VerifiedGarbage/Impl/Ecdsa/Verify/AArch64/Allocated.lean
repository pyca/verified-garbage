module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
public import VerifiedGarbage.Impl.P256.VerifyAllocated

/-! Public P-256 verification with register-allocated point and inversion arithmetic. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.P256Allocated
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.P256

def cfg := P256Joint.cfg
def K := cfg.K

def mixedAdd : Prog isa :=
  .seq (.block (zeroMask 4 K.R.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt 4 K.D K.E)) <|
  .seq (.block (copy 4 K.S.t2 K.R.x ++ copy 4 K.S.t4 K.R.y)) <|
  .seq (VerifyAllocated.program .mixedHead) <|
  .seq (.block (zeroMask 4 K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask 4 K.S.t5)) <|
      .ite (.nonzero .x .x2) (VerifyDouble.double K.M K.S K.R K.D)
        (.block (Jacobian.infinity K K.D)))
    (VerifyAllocated.program .mixedTail)

def cachedOps : CachedJac.Ops where
  head := VerifyAllocated.program .cachedHead
  tail := VerifyAllocated.program .jacTail
  double := P256Joint.cachedOps.double

def ops : Joint.Ops where
  table := P256Joint.ops.table
  cache := P256Joint.ops.cache
  digitQ := CachedJac.digit K cachedOps
  double := VerifyAllocated.program .doubleRR
  mixedAdd := mixedAdd

def extra : List (Reg × Nat) := [(.x26,7800),(.x27,7808),(.x28,7816),(.x30,7824)]
def saveExtra : List Instr := extra.map fun (r,off) => st r off
def restoreExtra : List Instr := extra.map fun (r,off) => ld r off

def points : Prog isa :=
  .seq (.block saveExtra) <|
  .seq (Joint.points cfg ops (p256.sl U) (p256.sl V)) (.block restoreExtra)

def inverseUpdate : List Instr := VerifyAllocatedCode.inverseUpdate

def inverseBatch : Prog isa :=
  .seq (.block p256.invN.batchStart) (.seq (wsteps 59) (.block inverseUpdate))

def inverseNine : InvCfg :=
  let c := 2^45 * (2^256)^3 % p256.C.n
  {p256.invN with B := 9,C := c,Cn := p256.C.n-c}

/-- The check preserves the divstep delta in x1 for the tenth-batch path. -/
def inverseCheck : List Instr :=
  let p := p256.invN
  [ld .x2 p.sG] ++ (List.range (p.L-1)).flatMap (fun i =>
    [ld .x3 (p.sG+8*(i+1)),.logic .orr .x .x2 .x2 .x3])

def inverse : Prog isa :=
  let finish := .seq (.block inverseCheck) <|
    .ite (.nonzero .x .x2)
      (.seq (.block [.movz .x .x19 1 0]) (.seq inverseBatch (.block p256.invN.finish)))
      (.block inverseNine.finish)
  .seq (.block saveExtra) <|
  .seq (.seq (.block inverseNine.init)
    (.seq (.loop inverseBatch (.nonzero .x .x19)) finish)) (.block restoreExtra)

def verify : Prog isa :=
  .seq (.block (Cfg.args p256)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.prefixWith p256 (some D)) <|
  .seq (.block (Cfg.loadS p256)) <|
  .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer p256)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.validate p256) <|
  .seq (Cfg.scalars p256) <| .seq inverse <| .seq (Cfg.uv p256) <|
  .seq points (Cfg.tail p256)

end VG.Impl.Ecdsa.Verify.AArch64.P256Allocated
