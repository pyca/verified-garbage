module

public import VerifiedGarbage.Impl.MlDsa.X86.Sign.Entry
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.X86.Sample.ExpandMask
public import VerifiedGarbage.Impl.MlDsa.X86.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
public import VerifiedGarbage.Impl.MlDsa.X86.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/-!
# ML-DSA signing on x86 (32-bit), with this library's primitives

The x86 implementations of the primitives signing calls (`Arith/`,
`Sample/`, `Round/`, `Pack/`), which `sign` (`Sign.lean`) is emitted with,
as `vg_mldsa*_sign_core`, and the functions that call it (`Entry.lean`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Sign

open VG.X86

/-- The x86 implementations of the primitives signing calls. -/
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

/-- `vg_mldsa{44,65,87}_sign`, for the module `module`. -/
def signOf (p : Spec.MlDsa.Params) (module : String) : Prog isa :=
  signEntry p (coreName module) (sign prims p)
/-- `vg_mldsa{44,65,87}_sign_prepared`, for the module `module`. -/
def signPreparedOf (p : Spec.MlDsa.Params) (module : String) : Prog isa :=
  signPrepared p (coreName module) (sign prims p)

end VG.Impl.MlDsa.X86.Sign
