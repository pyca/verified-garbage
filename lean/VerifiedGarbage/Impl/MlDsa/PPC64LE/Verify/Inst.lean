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

`withCache` (`Verify.lean`) called with the PPC64LE implementations of the
primitives it calls, the kernels `vg_mldsa*_verify_with_cache`, and the
entries calling them: `vg_mldsa*_verify` (`verify44`, …) and
`vg_mldsa*_verify_prepared` (`verifyPrepared44`, …).
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

/-- `vg_mldsa44_verify_with_cache` -/
def withCache44 : Prog isa := withCache prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_verify_with_cache` -/
def withCache65 : Prog isa := withCache prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_verify_with_cache` -/
def withCache87 : Prog isa := withCache prims Spec.MlDsa.mlDsa87

/-- `vg_mldsa44_verify` -/
def verify44 : Prog isa := entry Spec.MlDsa.mlDsa44 "vg_mldsa44_verify_with_cache" withCache44 false
/-- `vg_mldsa65_verify` -/
def verify65 : Prog isa := entry Spec.MlDsa.mlDsa65 "vg_mldsa65_verify_with_cache" withCache65 false
/-- `vg_mldsa87_verify` -/
def verify87 : Prog isa := entry Spec.MlDsa.mlDsa87 "vg_mldsa87_verify_with_cache" withCache87 false
/-- `vg_mldsa44_verify_prepared` -/
def verifyPrepared44 : Prog isa := entry Spec.MlDsa.mlDsa44 "vg_mldsa44_verify_with_cache" withCache44 true
/-- `vg_mldsa65_verify_prepared` -/
def verifyPrepared65 : Prog isa := entry Spec.MlDsa.mlDsa65 "vg_mldsa65_verify_with_cache" withCache65 true
/-- `vg_mldsa87_verify_prepared` -/
def verifyPrepared87 : Prog isa := entry Spec.MlDsa.mlDsa87 "vg_mldsa87_verify_with_cache" withCache87 true

end VG.Impl.MlDsa.PPC64LE.Verify
