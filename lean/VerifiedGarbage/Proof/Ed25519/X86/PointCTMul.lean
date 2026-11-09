module

public import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
public import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
public import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame

/-! Merged from `Proof.Ed25519.X86.PointCTBatch`. -/

@[expose] public section

/-! Merged from `Proof.Ed25519.X86.PointCTMulLoop`. -/

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulCTInput (x : BitVec 32) (scalar count : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  bound : scalar < 2 ^ (16 * count)
  bits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat
  d : env s.mem x 16 = Spec.Ed25519.d

end VG.Proof.Ed25519.X86
