module

public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.AddSub
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.ExpandMask
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint

/-!
# ML-DSA signing on 32-bit ARM, with this library's primitives

The ARM implementations of the primitives signing calls (`Arith/`,
`Sample/`, `Round/`, `Pack/`), which `sign` (`Sign.lean`) and the
preparations of keys are emitted with.
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.Sign

open VG.Arm

/-- The ARMv7 implementations of the primitives. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  add := Arith.add
  sub := Arith.sub
  rejNTT := Sample.rejNTT
  expandMask := Sample.expandMask
  ball := Sample.sampleInBall
  highBits := Round.highBits
  lowBits := Round.lowBits
  normLt := Round.normLt
  makeHint := Round.makeHint
  simpleBitPack := Pack.simpleBitPack
  bitPack := Pack.bitPack
  bitUnpack := Pack.bitUnpack
  hintBitPack := Pack.hintBitPack

end VG.Impl.MlDsa.Arm.Sign
