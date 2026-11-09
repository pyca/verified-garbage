module

public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Entry
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.X86.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
public import VerifiedGarbage.Impl.MlDsa.X86.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/-!
# ML-DSA verification on x86 (32-bit), with this library's primitives

`verify` (`Verify.lean`) called with the x86 implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`), as
`vg_mldsa*_verify_core`, and the functions that call it (`Entry.lean`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Verify

open VG.X86

/-- The x86 implementations of the primitives verification calls. -/
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

/-- `vg_mldsa{44,65,87}_verify`, for the module `module`. -/
def verifyOf (p : Spec.MlDsa.Params) (module : String) : Prog isa :=
  verifyEntry p prims (coreName module) (verify prims p)
/-- `vg_mldsa{44,65,87}_verify_prepared`, for the module `module`. -/
def verifyPreparedOf (p : Spec.MlDsa.Params) (module : String) : Prog isa :=
  verifyPrepared p (coreName module) (verify prims p)

/-- `vg_mldsa44_verify` -/
def verify44 : Prog isa := verifyOf Spec.MlDsa.mlDsa44 "mldsa44"
/-- `vg_mldsa65_verify` -/
def verify65 : Prog isa := verifyOf Spec.MlDsa.mlDsa65 "mldsa65"
/-- `vg_mldsa87_verify` -/
def verify87 : Prog isa := verifyOf Spec.MlDsa.mlDsa87 "mldsa87"

end VG.Impl.MlDsa.X86.Verify
