module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Top
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintUnpackCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA verification on PPC64LE, with this library's primitives

The PPC64LE implementations of the primitives (`prims`) are verified with at
most 96 bytes of stack, and their frames use no more (`prims_ok`), so
verification with them is verified with 96 (`verify44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Verify

theorem prims_ok : VPrimsOk prims 96 where
  ntt := ⟨⟨96, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨96, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨48, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  ball := ⟨⟨48, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  useHint := ⟨⟨0, by decide, Round.UseHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  unpackT1 := ⟨⟨0, by decide, Pack.unpackT1_verified⟩, by decide +kernel⟩
  hintUnpack := ⟨⟨0, by decide, Pack.hintBitUnpack_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩

theorem verify44_sat : (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 PPC64LE.abi 96).pre
    (verifySat Spec.MlDsa.mlDsa44) := by
  sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs, verifySat]

theorem verify44_verified :
    Verified PPC64LE.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 PPC64LE.abi 96) :=
  verify_verified prims_ok (by decide) _ (.inl rfl) verify44_sat

theorem verify65_sat : (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 PPC64LE.abi 96).pre
    (verifySat Spec.MlDsa.mlDsa65) := by
  sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs, verifySat]

theorem verify65_verified :
    Verified PPC64LE.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 PPC64LE.abi 96) :=
  verify_verified prims_ok (by decide) _ (.inr (.inl rfl)) verify65_sat

theorem verify87_sat : (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 PPC64LE.abi 96).pre
    (verifySat Spec.MlDsa.mlDsa87) := by
  sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs, verifySat]

theorem verify87_verified :
    Verified PPC64LE.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 PPC64LE.abi 96) :=
  verify_verified prims_ok (by decide) _ (.inr (.inr rfl)) verify87_sat

end VG.Proof.MlDsa.PPC64LE.Verify
