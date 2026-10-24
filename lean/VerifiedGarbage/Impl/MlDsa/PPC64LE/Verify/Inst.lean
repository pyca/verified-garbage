module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Round
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Hint
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Ball

/-!
# ML-DSA verification on PPC64LE, with this library's primitives

`verify` (`Verify.lean`) called with the PPC64LE implementations of the
primitives it calls.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Verify

open VG.PPC64LE

/-- The PPC64LE implementations of the primitives verification calls. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
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

/-- `vg_mldsa44_verify` -/
def verify44 : Prog isa := verify prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_verify` -/
def verify65 : Prog isa := verify prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_verify` -/
def verify87 : Prog isa := verify prims Spec.MlDsa.mlDsa87

end VG.Impl.MlDsa.PPC64LE.Verify
