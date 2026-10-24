module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Round
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Hint
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.ExpandMask
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Ball

/-!
# ML-DSA signing on PPC64LE, with this library's primitives

`sign` (`Sign.lean`) called with the PPC64LE implementations of the
primitives it calls.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sign

open VG.PPC64LE

/-- The PPC64LE implementations of the primitives signing calls. -/
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

/-- `vg_mldsa44_sign` -/
def sign44 : Prog isa := sign prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_sign` -/
def sign65 : Prog isa := sign prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_sign` -/
def sign87 : Prog isa := sign prims Spec.MlDsa.mlDsa87

end VG.Impl.MlDsa.PPC64LE.Sign
