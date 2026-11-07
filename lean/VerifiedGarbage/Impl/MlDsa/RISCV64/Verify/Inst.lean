module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Round
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Hint
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sample
public import VerifiedGarbage.Impl.MlDsa.RISCV64.PreparedKey.Entry

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

/-- `vg_mldsa44_verify_with_cache` -/
def withCache44 : Prog isa := verify prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_verify_with_cache` -/
def withCache65 : Prog isa := verify prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_verify_with_cache` -/
def withCache87 : Prog isa := verify prims Spec.MlDsa.mlDsa87

/-- `vg_mldsa44_verify` (`q` false) and `vg_mldsa44_verify_prepared` (`q` true). -/
def verify44E (q : Bool) : Prog isa :=
  PreparedKey.verifyEntry Spec.MlDsa.mlDsa44 "vg_mldsa44_verify_with_cache" withCache44 q
/-- `vg_mldsa65_verify` (`q` false) and `vg_mldsa65_verify_prepared` (`q` true). -/
def verify65E (q : Bool) : Prog isa :=
  PreparedKey.verifyEntry Spec.MlDsa.mlDsa65 "vg_mldsa65_verify_with_cache" withCache65 q
/-- `vg_mldsa87_verify` (`q` false) and `vg_mldsa87_verify_prepared` (`q` true). -/
def verify87E (q : Bool) : Prog isa :=
  PreparedKey.verifyEntry Spec.MlDsa.mlDsa87 "vg_mldsa87_verify_with_cache" withCache87 q

/-- `vg_mldsa44_verify` -/
def verify44 : Prog isa := verify44E false
/-- `vg_mldsa65_verify` -/
def verify65 : Prog isa := verify65E false
/-- `vg_mldsa87_verify` -/
def verify87 : Prog isa := verify87E false

end VG.Impl.MlDsa.RISCV64.Verify
