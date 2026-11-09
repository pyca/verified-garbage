module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Top
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintUnpackCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA verification on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers', for the sponge's frames; the others
use none), and their frames use no more (`prims_ok`), so verification with
them is verified with 1168 (`verify44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Verify

theorem prims_ok : VPrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  ball := ⟨⟨1168, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  useHint := ⟨⟨0, by decide, Round.UseHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  unpackT1 := ⟨⟨0, by decide, Pack.unpackT1_verified⟩, by decide +kernel⟩
  hintUnpack := ⟨⟨0, by decide, Pack.hintBitUnpack_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩

theorem withCache44_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa44) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified :
    Verified RISCV64.target withCache44 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inl rfl) withCache44_sat

theorem withCache65_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa65) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified :
    Verified RISCV64.target withCache65 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inr (.inl rfl)) withCache65_sat

theorem withCache87_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa87) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified :
    Verified RISCV64.target withCache87 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inr (.inr rfl)) withCache87_sat

end VG.Proof.MlDsa.RISCV64.Verify
