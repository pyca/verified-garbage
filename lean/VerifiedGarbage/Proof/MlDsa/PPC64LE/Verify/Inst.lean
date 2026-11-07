module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Entry
import VerifiedGarbage.Proof.MlDsa.PPC64LE.PreparedKey
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
verification's kernel with them is verified with 96 + 96
(`withCache44_verified`, …), and the entries calling it with 48 more
(`verify44_verified`, `verifyPrepared44_verified`, …): the precondition of a
prepared key's holds of the memory its preparation writes
(`PreparedKey.public_mem`).
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

theorem withCache44_sat :
    (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 PPC64LE.abi (96 + 96)).pre (kSat Spec.MlDsa.mlDsa44) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified : Verified PPC64LE.target withCache44
    (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 PPC64LE.abi (96 + 96)) :=
  withCache_verified prims_ok (by decide) _ (.inl rfl) (by decide +kernel) withCache44_sat

theorem withCache65_sat :
    (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 PPC64LE.abi (96 + 96)).pre (kSat Spec.MlDsa.mlDsa65) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified : Verified PPC64LE.target withCache65
    (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 PPC64LE.abi (96 + 96)) :=
  withCache_verified prims_ok (by decide) _ (.inr (.inl rfl)) (by decide +kernel) withCache65_sat

theorem withCache87_sat :
    (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 PPC64LE.abi (96 + 96)).pre (kSat Spec.MlDsa.mlDsa87) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified : Verified PPC64LE.target withCache87
    (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 PPC64LE.abi (96 + 96)) :=
  withCache_verified prims_ok (by decide) _ (.inr (.inr rfl)) (by decide +kernel) withCache87_sat

/-! ## The entries -/

/-- A state that satisfies `preparedVerifyContract`'s precondition, with the
memory `m`, a prepared public key at `0x10000`. -/
def pvSat (p : Spec.MlDsa.Params) (m : Mem) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x20000 | _ => 0
  lr := 0
  sp := 0x100000
  mem := m
  rd := [⟨0x10000, Spec.MlDsa.preparedPublicKeyBytes p⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x20000, KeyGen.scrLen p⟩]

theorem prepared_sat {p : Spec.MlDsa.Params}
    (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∃ s, (Proof.MlDsa.preparedVerifyContract p PPC64LE.abi (191 + 1 + 48)).pre s := by
  obtain ⟨m, hm⟩ := PreparedKey.public_mem hp3
  refine ⟨pvSat p m, ?_⟩
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [Proof.MlDsa.preparedVerifyContract, Proof.MlDsa.preparedVerifySig, PPC64LE.abi, PPC64LE.argRegs, pvSat]
    sig_and_intros
    all_goals first
      | exact hm
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem verify_sat {p : Spec.MlDsa.Params}
    (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∃ s, (Spec.MlDsa.verifyContract p PPC64LE.abi (191 + 1 + 48)).pre s := by
  refine ⟨verifySat p, ?_⟩
  rcases hp3 with rfl | rfl | rfl
  all_goals sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs, verifySat]

theorem verify44_verified :
    Verified PPC64LE.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 PPC64LE.abi 240) :=
  verify_entry_verified withCache44_verified (by decide +kernel) (by decide) (verify_sat (.inl rfl))
theorem verify65_verified :
    Verified PPC64LE.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 PPC64LE.abi 240) :=
  verify_entry_verified withCache65_verified (by decide +kernel) (by decide) (verify_sat (.inr (.inl rfl)))
theorem verify87_verified :
    Verified PPC64LE.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 PPC64LE.abi 240) :=
  verify_entry_verified withCache87_verified (by decide +kernel) (by decide) (verify_sat (.inr (.inr rfl)))

theorem verifyPrepared44_verified : Verified PPC64LE.target verifyPrepared44
    (Proof.MlDsa.preparedVerifyContract Spec.MlDsa.mlDsa44 PPC64LE.abi 240) :=
  prepared_entry_verified withCache44_verified (by decide +kernel) (by decide) (.inl rfl) (prepared_sat (.inl rfl))
theorem verifyPrepared65_verified : Verified PPC64LE.target verifyPrepared65
    (Proof.MlDsa.preparedVerifyContract Spec.MlDsa.mlDsa65 PPC64LE.abi 240) :=
  prepared_entry_verified withCache65_verified (by decide +kernel) (by decide) (.inr (.inl rfl))
    (prepared_sat (.inr (.inl rfl)))
theorem verifyPrepared87_verified : Verified PPC64LE.target verifyPrepared87
    (Proof.MlDsa.preparedVerifyContract Spec.MlDsa.mlDsa87 PPC64LE.abi 240) :=
  prepared_entry_verified withCache87_verified (by decide +kernel) (by decide) (.inr (.inr rfl))
    (prepared_sat (.inr (.inr rfl)))

end VG.Proof.MlDsa.PPC64LE.Verify
