module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Verified
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.PPC64LE.PreparedKey
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Copy
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on PPC64LE, `sign_message`, `verify_message_cached` and their prepared versions, with this library's functions on `μ`

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message_cached` calling the
PPC64LE `vg_mldsa*_sign` and `vg_mldsa*_verify` (`Sign/Inst.lean`,
`Verify/Inst.lean`), and `vg_mldsa*_sign_message_prepared` and
`vg_mldsa*_verify_message_prepared` calling `vg_mldsa*_sign_prepared` and
`vg_mldsa*_verify_prepared`, verified with 240 bytes of stack, whose frames
use no more (`sign44Fn`, …): so the functions on messages are verified with
240 (`signMessage44_verified`, …). The preconditions with prepared keys hold
of the memory their preparation writes (`PreparedKey.secret_mem`,
`PreparedKey.public_mem`), with `tr` of the key written after it
(`pv_mem`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Satisfiability -/

section
variable {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
include hp3

/-- `mcSat` satisfies `verifyMessageCachedContract`'s precondition with 240 bytes of stack. -/
theorem verifyMessageCached_sat : ∃ s, (msgVK p false PPC64LE.abi 240).pre s := by
  refine ⟨mcSat p, ?_⟩
  simp only [msgVK, Bool.false_eq_true, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl <;>
    sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, PPC64LE.abi, PPC64LE.argRegs] <;> sig_and_intros
  all_goals first
    | exact mcSat_digest (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem signMessage_sat : ∃ s, (msgSK p false PPC64LE.abi 240).pre s := by
  refine ⟨msSat p, ?_⟩
  simp only [msgSK, Bool.false_eq_true, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals sig_sat_check [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs, msSat]

/-- A state that satisfies `preparedSignMessageContract`'s precondition,
with the memory `m`, a prepared private key at `0x10000`. -/
def pmsSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x8000 | .r6 => 0x9000 | .r8 => 0xA000 | .r9 => 0xB000 | .r10 => 0x20000
    | _ => 0
  lr := 0
  sp := 0x100000
  mem := m
  rd := [⟨0x10000, preparedSecretKeyBytes p⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, 32⟩]
  wr := [⟨0xB000, p.sigLen⟩, ⟨0x20000, messageScratchWords p * 8⟩]

theorem preparedSignMessage_sat : ∃ s, (msgSK p true PPC64LE.abi 240).pre s := by
  obtain ⟨m, hm⟩ := PreparedKey.secret_mem hp3
  refine ⟨pmsSat p m, ?_⟩
  simp only [msgSK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedSignMessageContract, preparedSignMessageSig, PPC64LE.abi, PPC64LE.argRegs, pmsSat]
    sig_and_intros
    all_goals first
      | exact hm
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

/-- Some memory holds a prepared public key at `0x10000`, and `tr` of it at `0xC000`. -/
theorem pv_mem : ∃ m : Mem, PreparedPublicKey p m 0x10000 ∧
    bytesAt m 0xC000 64 = pkTr (bytesAt m 0x10000 p.pkLen) := by
  obtain ⟨m, hm⟩ := PreparedKey.public_mem hp3
  have hl : (pkTr (bytesAt m 0x10000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  have hf : Frame [⟨0xC000, 64⟩] m (VG.WriteBytes.writeBytes m 0xC000 (pkTr (bytesAt m 0x10000 p.pkLen))) :=
    VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have hd : (⟨0x10000, preparedPublicKeyBytes p⟩ : Region).Disjoint ⟨0xC000, 64⟩ := by
    rcases hp3 with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  have hfit : (0x10000 : Addr).toNat + preparedPublicKeyBytes p ≤ 2 ^ 64 := by
    rcases hp3 with rfl | rfl | rfl <;> decide
  have hk : bytesAt (VG.WriteBytes.writeBytes m 0xC000 (pkTr (bytesAt m 0x10000 p.pkLen))) 0x10000 p.pkLen =
      bytesAt m 0x10000 p.pkLen := by
    have hs : Region.Sub ⟨0x10000, p.pkLen⟩ ⟨0x10000, preparedPublicKeyBytes p⟩ := fun a ha => by
      simp only [Region.Contains, preparedPublicKeyBytes] at ha ⊢; omega
    exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hd.sub_left hs) (by rcases hp3 with rfl | rfl | rfl <;> decide)
  refine ⟨_, preparedPublicKey_frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd) hfit hm,
    ?_⟩
  rw [hk]
  have := bytesAt_writeBytes_self m 0xC000 (pkTr (bytesAt m 0x10000 p.pkLen)) (by rw [hl]; decide)
  rwa [hl] at this

/-- A state that satisfies `preparedVerifyMessageContract`'s precondition,
with the memory `m`, a prepared public key at `0x10000` and `tr` at `0xC000`. -/
def pmcSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x8000 | .r6 => 0x9000 | .r8 => 0xA000 | .r9 => 0x20000 | .r10 => 0xC000
    | _ => 0
  lr := 0
  sp := 0x100000
  mem := m
  rd := [⟨0x10000, preparedPublicKeyBytes p⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, p.sigLen⟩, ⟨0xC000, 64⟩]
  wr := [⟨0x20000, messageScratchWords p * 8⟩]

theorem preparedVerifyMessage_sat : ∃ s, (msgVK p true PPC64LE.abi 240).pre s := by
  obtain ⟨m, hm, ht⟩ := pv_mem hp3
  refine ⟨pmcSat p m, ?_⟩
  simp only [msgVK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, PPC64LE.abi, PPC64LE.argRegs, pmcSat]
    sig_and_intros
    all_goals first
      | exact hm
      | exact ht
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

end

/-! ## ML-DSA-44 -/

theorem sign44Fn : Callee Impl.MlDsa.PPC64LE.Sign.sign44 (fun stk => signK mlDsa44 false PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Sign.sign44_verified⟩, by decide +kernel⟩

theorem signPrepared44Fn :
    Callee Impl.MlDsa.PPC64LE.Sign.signPrepared44 (fun stk => signK mlDsa44 true PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Sign.signPrepared44_verified⟩, by decide +kernel⟩

theorem verify44Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verify44 (fun stk => verifyK mlDsa44 false PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Verify.verify44_verified⟩, by decide +kernel⟩

theorem verifyPrepared44Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verifyPrepared44 (fun stk => verifyK mlDsa44 true PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Verify.verifyPrepared44_verified⟩, by decide +kernel⟩

theorem signMessage44_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage sign44Api.name Impl.MlDsa.PPC64LE.Sign.sign44 mlDsa44)
      (signMessageContract mlDsa44 PPC64LE.abi 240) :=
  signMessage_verified (.inl rfl) (by decide) sign44Fn _ (signMessage_sat (.inl rfl))

theorem preparedSignMessage44_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
        Impl.MlDsa.PPC64LE.Sign.signPrepared44 mlDsa44)
      (preparedSignMessageContract mlDsa44 PPC64LE.abi 240) :=
  signMessage_verified (.inl rfl) (by decide) signPrepared44Fn _ (preparedSignMessage_sat (.inl rfl))

theorem verifyMessageCached44_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessageCached verify44Api.name Impl.MlDsa.PPC64LE.Verify.verify44
        mlDsa44)
      (verifyMessageCachedContract mlDsa44 PPC64LE.abi 240) :=
  verifyMessageCached_verified (.inl rfl) (by decide) verify44Fn _ (verifyMessageCached_sat (.inl rfl))

theorem preparedVerifyMessage44_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared44 mlDsa44)
      (preparedVerifyMessageContract mlDsa44 PPC64LE.abi 240) :=
  verifyMessageCached_verified (.inl rfl) (by decide) verifyPrepared44Fn _ (preparedVerifyMessage_sat (.inl rfl))

/-! ## ML-DSA-65 -/

theorem sign65Fn : Callee Impl.MlDsa.PPC64LE.Sign.sign65 (fun stk => signK mlDsa65 false PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Sign.sign65_verified⟩, by decide +kernel⟩

theorem signPrepared65Fn :
    Callee Impl.MlDsa.PPC64LE.Sign.signPrepared65 (fun stk => signK mlDsa65 true PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Sign.signPrepared65_verified⟩, by decide +kernel⟩

theorem verify65Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verify65 (fun stk => verifyK mlDsa65 false PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Verify.verify65_verified⟩, by decide +kernel⟩

theorem verifyPrepared65Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verifyPrepared65 (fun stk => verifyK mlDsa65 true PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Verify.verifyPrepared65_verified⟩, by decide +kernel⟩

theorem signMessage65_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage sign65Api.name Impl.MlDsa.PPC64LE.Sign.sign65 mlDsa65)
      (signMessageContract mlDsa65 PPC64LE.abi 240) :=
  signMessage_verified (.inr (.inl rfl)) (by decide) sign65Fn _ (signMessage_sat (.inr (.inl rfl)))

theorem preparedSignMessage65_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
        Impl.MlDsa.PPC64LE.Sign.signPrepared65 mlDsa65)
      (preparedSignMessageContract mlDsa65 PPC64LE.abi 240) :=
  signMessage_verified (.inr (.inl rfl)) (by decide) signPrepared65Fn _ (preparedSignMessage_sat (.inr (.inl rfl)))

theorem verifyMessageCached65_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessageCached verify65Api.name Impl.MlDsa.PPC64LE.Verify.verify65
        mlDsa65)
      (verifyMessageCachedContract mlDsa65 PPC64LE.abi 240) :=
  verifyMessageCached_verified (.inr (.inl rfl)) (by decide) verify65Fn _ (verifyMessageCached_sat (.inr (.inl rfl)))

theorem preparedVerifyMessage65_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared65 mlDsa65)
      (preparedVerifyMessageContract mlDsa65 PPC64LE.abi 240) :=
  verifyMessageCached_verified (.inr (.inl rfl)) (by decide) verifyPrepared65Fn _ (preparedVerifyMessage_sat (.inr (.inl rfl)))

/-! ## ML-DSA-87 -/

theorem sign87Fn : Callee Impl.MlDsa.PPC64LE.Sign.sign87 (fun stk => signK mlDsa87 false PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Sign.sign87_verified⟩, by decide +kernel⟩

theorem signPrepared87Fn :
    Callee Impl.MlDsa.PPC64LE.Sign.signPrepared87 (fun stk => signK mlDsa87 true PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Sign.signPrepared87_verified⟩, by decide +kernel⟩

theorem verify87Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verify87 (fun stk => verifyK mlDsa87 false PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Verify.verify87_verified⟩, by decide +kernel⟩

theorem verifyPrepared87Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verifyPrepared87 (fun stk => verifyK mlDsa87 true PPC64LE.abi stk) 240 :=
  ⟨⟨240, Nat.le_refl _, Verify.verifyPrepared87_verified⟩, by decide +kernel⟩

theorem signMessage87_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage sign87Api.name Impl.MlDsa.PPC64LE.Sign.sign87 mlDsa87)
      (signMessageContract mlDsa87 PPC64LE.abi 240) :=
  signMessage_verified (.inr (.inr rfl)) (by decide) sign87Fn _ (signMessage_sat (.inr (.inr rfl)))

theorem preparedSignMessage87_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
        Impl.MlDsa.PPC64LE.Sign.signPrepared87 mlDsa87)
      (preparedSignMessageContract mlDsa87 PPC64LE.abi 240) :=
  signMessage_verified (.inr (.inr rfl)) (by decide) signPrepared87Fn _ (preparedSignMessage_sat (.inr (.inr rfl)))

theorem verifyMessageCached87_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessageCached verify87Api.name Impl.MlDsa.PPC64LE.Verify.verify87
        mlDsa87)
      (verifyMessageCachedContract mlDsa87 PPC64LE.abi 240) :=
  verifyMessageCached_verified (.inr (.inr rfl)) (by decide) verify87Fn _ (verifyMessageCached_sat (.inr (.inr rfl)))

theorem preparedVerifyMessage87_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87")
        Impl.MlDsa.PPC64LE.Verify.verifyPrepared87 mlDsa87)
      (preparedVerifyMessageContract mlDsa87 PPC64LE.abi 240) :=
  verifyMessageCached_verified (.inr (.inr rfl)) (by decide) verifyPrepared87Fn _ (preparedVerifyMessage_sat (.inr (.inr rfl)))

end VG.Proof.MlDsa.PPC64LE.Message
