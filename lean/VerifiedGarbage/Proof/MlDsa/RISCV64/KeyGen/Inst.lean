module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Top
public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.BitPack
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA key generation on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers' Keccak frames; the others use none),
and their frames use no more (`prims_ok`), so key generation with them is
verified with 1168 (`keyGen44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen

theorem prims_ok : PrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  rejBounded := ⟨⟨1168, by decide, Sample.rejBounded_verified⟩, by decide +kernel⟩
  power2Round := ⟨⟨0, by decide, Round.Power2Round.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩

theorem keyGen44_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168).pre (keyGenSat Spec.MlDsa.mlDsa44) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs, keyGenSat]

theorem keyGen44_verified :
    Verified RISCV64.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168) :=
  keyGen_verified prims_ok (by decide) _ (.inl rfl) keyGen44_sat

theorem keyGen65_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168).pre (keyGenSat Spec.MlDsa.mlDsa65) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs, keyGenSat]

theorem keyGen65_verified :
    Verified RISCV64.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inl rfl)) keyGen65_sat

theorem keyGen87_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168).pre (keyGenSat Spec.MlDsa.mlDsa87) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, RISCV64.abi, RISCV64.argRegs, keyGenSat]

theorem keyGen87_verified :
    Verified RISCV64.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inr rfl)) keyGen87_sat

end VG.Proof.MlDsa.RISCV64.KeyGen
