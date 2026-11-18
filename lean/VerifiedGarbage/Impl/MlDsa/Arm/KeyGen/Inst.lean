module

public import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.KeyGen
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejBounded
public import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode

/-!
# ML-DSA key generation on 32-bit ARM, with this library's primitives

`keyGen` (`KeyGen.lean`) called with the ARM implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.Arm.KeyGen

open VG.Arm

/-- The ARM implementations of the primitives key generation calls, the
transforms with `umaal` if `u`. -/
def prims (u : Bool) : Prims where
  ntt := Arith.ntt u
  invNtt := Arith.nttInv u
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  add := Arith.add
  rejNtt := Sample.rejNTT
  rejBounded := Sample.rejBounded
  power2Round := Round.power2Round
  simpleBitPack := Pack.simpleBitPack
  bitPack := Pack.bitPack
  sfx := Arith.suffix u

end VG.Impl.MlDsa.Arm.KeyGen
