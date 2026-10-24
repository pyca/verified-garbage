module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Top
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA key generation on PPC64LE, with this library's primitives

The PPC64LE implementations of the primitives (`prims`) are verified with at
most 96 bytes of stack, and their frames use no more (`prims_ok`), so key
generation with them is verified with 96 (`keyGen44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen

theorem prims_ok : PrimsOk prims 96 where
  ntt := ⟨⟨96, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨96, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨48, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  rejBounded := ⟨⟨48, by decide, Sample.rejBounded_verified⟩, by decide +kernel⟩
  power2Round := ⟨⟨0, by decide, Round.Power2Round.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩

theorem keyGen44_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 PPC64LE.abi 96).pre (keyGenSat Spec.MlDsa.mlDsa44) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs, keyGenSat]

theorem keyGen44_verified :
    Verified PPC64LE.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 PPC64LE.abi 96) :=
  keyGen_verified prims_ok (by decide) _ (.inl rfl) keyGen44_sat

theorem keyGen65_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 PPC64LE.abi 96).pre (keyGenSat Spec.MlDsa.mlDsa65) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs, keyGenSat]

theorem keyGen65_verified :
    Verified PPC64LE.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 PPC64LE.abi 96) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inl rfl)) keyGen65_sat

theorem keyGen87_sat : (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 PPC64LE.abi 96).pre (keyGenSat Spec.MlDsa.mlDsa87) := by
  sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs, keyGenSat]

theorem keyGen87_verified :
    Verified PPC64LE.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 PPC64LE.abi 96) :=
  keyGen_verified prims_ok (by decide) _ (.inr (.inr rfl)) keyGen87_sat

end VG.Proof.MlDsa.PPC64LE.KeyGen
