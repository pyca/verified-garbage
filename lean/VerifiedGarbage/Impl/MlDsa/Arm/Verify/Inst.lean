module

public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint

/-!
# ML-DSA verification on 32-bit ARM, with this library's primitives

`verify` (`Verify.lean`) called with the ARM implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.Verify

open VG.Arm

/-- The ARM implementations of the primitives verification calls. -/
def prims (u : Bool) : Prims where
  ntt := Arith.ntt u
  invNtt := Arith.nttInv u
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  sub := Arith.sub
  rejNtt := Sample.rejNTT
  ball := Sample.sampleInBall
  useHint := Round.useHint
  simpleBitPack := Pack.simpleBitPack
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack
  normLt := Round.normLt
  sfx := Arith.suffix u

end VG.Impl.MlDsa.Arm.Verify
