module

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
public import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Hint
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.Arm.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackCT

/-!
# ML-DSA verification on 32-bit ARM, with this library's primitives

The ARM implementations of the primitives (`prims u`, the transforms with
`umaal` or without) are verified with at most
28 bytes of stack, and their frames use no more (`prims_ok`), so the kernel
with them is verified with 36.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm
open VG.Impl.MlDsa.Arm.Verify

theorem prims_ok (u : Bool) : VPrimsOk (prims u) 28 where
  ntt := ⟨⟨28, by decide, Arith.Ntt.verified u⟩, by cases u <;> decide +kernel⟩
  invNtt := ⟨⟨28, by decide, Arith.NttInv.verified u⟩, by cases u <;> decide +kernel⟩
  mul := ⟨⟨24, by decide, Arith.Mul.mul_verified⟩, by cases u <;> decide +kernel⟩
  mulAdd := ⟨⟨24, by decide, Arith.Mul.mulAdd_verified⟩, by cases u <;> decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by cases u <;> decide +kernel⟩
  rejNtt := ⟨⟨8, by decide, Sample.rejNTT_verified⟩, by cases u <;> decide +kernel⟩
  ball := ⟨⟨8, by decide, Sample.sampleInBall_verified⟩, by cases u <;> decide +kernel⟩
  useHint := ⟨⟨12, by decide, Round.UseHint.verified⟩, by cases u <;> decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by cases u <;> decide +kernel⟩
  bitUnpack := ⟨⟨4, by decide, Pack.bitUnpack_verified⟩, by cases u <;> decide +kernel⟩
  unpackT1 := ⟨⟨0, by decide, Pack.unpackT1_verified⟩, by cases u <;> decide +kernel⟩
  hintUnpack := ⟨⟨16, by decide, Pack.Hint.hintBitUnpack_verified⟩, by cases u <;> decide +kernel⟩
  normLt := ⟨⟨4, by decide, Round.NormLt.verified⟩, by cases u <;> decide +kernel⟩

end VG.Proof.MlDsa.Arm.Verify
