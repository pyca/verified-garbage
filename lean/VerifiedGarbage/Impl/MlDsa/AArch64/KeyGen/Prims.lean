module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BallDispatch
public import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Hint
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedSecrets
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.AddSub
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenRound
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack

/-!
# ML-DSA on AArch64: key generation and verification with this library's primitives

The AArch64 implementations of the primitives (`primsWith`), which
`vg_mldsa{44,65,87}_keygen` (`KeyGen/OptimizedPrims.lean`), `_sign` and
`_verify` call.
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.KeyGen

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call

/-- The AArch64 primitives. -/
def primsWith (c : Impl.Sha3.AArch64.Callee) : Prims where
  suffix := c.suffix
  ntt := Arith.Neon.ntt
  invNtt := Arith.Neon.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  add := Optimized.AddSub.code false
  sub := Optimized.AddSub.code true
  rejNtt := Sample.rejNTTWith c
  rej4 := Optimized.ResidentRej.selected c.pairedSha3
  rejBounded := Sample.rejBoundedWith c
  ball := Optimized.Ball.selected c
  power2Round := Optimized.KeygenRound.power2Round
  useHint := Round.useHint
  normLt := Round.normLt
  simpleBitPack := Optimized.KeygenPack.simple
  bitPack := Optimized.KeygenPack.signed
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack

end VG.Impl.MlDsa.AArch64.KeyGen
