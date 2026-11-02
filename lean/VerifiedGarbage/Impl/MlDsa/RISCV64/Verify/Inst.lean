module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Round
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Hint
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sample

/-!
# ML-DSA verification on RISC-V, with this library's primitives

`verify` (`Verify.lean`) called with the RISC-V implementations of the
primitives it calls.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Verify

open VG.RISCV64

/-- The RISC-V implementations of the primitives verification calls. -/
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

end VG.Impl.MlDsa.RISCV64.Verify
