module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.KeyGen
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Arith
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Round
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.RejBounded

/-!
# ML-DSA key generation on PPC64LE, with this library's primitives

`keyGen` (`KeyGen.lean`) called with the PPC64LE implementations of the
primitives it calls (`Arith.lean`, `Round.lean`, `Pack/`, `Sample/`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.KeyGen

open VG.PPC64LE

/-- The PPC64LE implementations of the primitives key generation calls. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  add := Arith.add
  rejNtt := Sample.rejNTT
  rejBounded := Sample.rejBounded
  power2Round := Round.power2Round
  simpleBitPack := Pack.simpleBitPack
  bitPack := Pack.bitPack

/-- `vg_mldsa44_keygen` -/
def keyGen44 : Prog isa := keyGen prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_keygen` -/
def keyGen65 : Prog isa := keyGen prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_keygen` -/
def keyGen87 : Prog isa := keyGen prims Spec.MlDsa.mlDsa87

end VG.Impl.MlDsa.PPC64LE.KeyGen
