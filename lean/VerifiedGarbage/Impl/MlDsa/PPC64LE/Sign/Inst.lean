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

`withCache` (`Sign.lean`) called with the PPC64LE implementations of the
primitives it calls, the kernels `vg_mldsa*_sign_with_cache`, and the
entries calling them: `vg_mldsa*_sign` (`sign44`, …) and
`vg_mldsa*_sign_prepared` (`signPrepared44`, …).
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

/-- `vg_mldsa44_sign_with_cache` -/
def withCache44 : Prog isa := withCache prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_sign_with_cache` -/
def withCache65 : Prog isa := withCache prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_sign_with_cache` -/
def withCache87 : Prog isa := withCache prims Spec.MlDsa.mlDsa87

/-- `vg_mldsa44_sign` -/
def sign44 : Prog isa := entry "vg_mldsa44_sign_with_cache" withCache44 Spec.MlDsa.mlDsa44 false
/-- `vg_mldsa65_sign` -/
def sign65 : Prog isa := entry "vg_mldsa65_sign_with_cache" withCache65 Spec.MlDsa.mlDsa65 false
/-- `vg_mldsa87_sign` -/
def sign87 : Prog isa := entry "vg_mldsa87_sign_with_cache" withCache87 Spec.MlDsa.mlDsa87 false
/-- `vg_mldsa44_sign_prepared` -/
def signPrepared44 : Prog isa := entry "vg_mldsa44_sign_with_cache" withCache44 Spec.MlDsa.mlDsa44 true
/-- `vg_mldsa65_sign_prepared` -/
def signPrepared65 : Prog isa := entry "vg_mldsa65_sign_with_cache" withCache65 Spec.MlDsa.mlDsa65 true
/-- `vg_mldsa87_sign_prepared` -/
def signPrepared87 : Prog isa := entry "vg_mldsa87_sign_with_cache" withCache87 Spec.MlDsa.mlDsa87 true

end VG.Impl.MlDsa.PPC64LE.Sign
