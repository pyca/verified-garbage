module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sample
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Round
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Hint
public import VerifiedGarbage.Impl.MlDsa.RISCV64.PreparedKey.Entry

/-!
# ML-DSA signing on RISC-V, with this library's primitives

`sign` (`Sign.lean`) called with the RISC-V implementations of the
primitives it calls, the kernel `vg_mldsa*_sign_with_cache`, and its entries
(`PreparedKey/Entry.lean`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Sign

open VG.RISCV64

/-- The RISC-V implementations of the primitives signing calls. -/
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

/-- `vg_mldsa44_sign_with_cache` -/
def withCache44 : Prog isa := sign prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_sign_with_cache` -/
def withCache65 : Prog isa := sign prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_sign_with_cache` -/
def withCache87 : Prog isa := sign prims Spec.MlDsa.mlDsa87

/-- `vg_mldsa44_sign` (`q` false) and `vg_mldsa44_sign_prepared` (`q` true). -/
def sign44E (q : Bool) : Prog isa :=
  PreparedKey.signEntry Spec.MlDsa.mlDsa44 "vg_mldsa44_sign_with_cache" withCache44 q
/-- `vg_mldsa65_sign` (`q` false) and `vg_mldsa65_sign_prepared` (`q` true). -/
def sign65E (q : Bool) : Prog isa :=
  PreparedKey.signEntry Spec.MlDsa.mlDsa65 "vg_mldsa65_sign_with_cache" withCache65 q
/-- `vg_mldsa87_sign` (`q` false) and `vg_mldsa87_sign_prepared` (`q` true). -/
def sign87E (q : Bool) : Prog isa :=
  PreparedKey.signEntry Spec.MlDsa.mlDsa87 "vg_mldsa87_sign_with_cache" withCache87 q

/-- `vg_mldsa44_sign` -/
def sign44 : Prog isa := sign44E false
/-- `vg_mldsa65_sign` -/
def sign65 : Prog isa := sign65E false
/-- `vg_mldsa87_sign` -/
def sign87 : Prog isa := sign87E false

end VG.Impl.MlDsa.RISCV64.Sign
