module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Verified
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Inst
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on RISC-V, `sign_message` and `verify_message_cached`, with this library's functions on `μ`

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message_cached` calling the
RISCV64 `vg_mldsa*_sign` and
`vg_mldsa*_verify` (`PreparedKey/Inst.lean`), verified with 1184
bytes of stack, whose frames use no more (`sign44Fn`, …): so the functions on
messages are verified with 1184 (`signMessage44_verified`,
`verifyMessageCached44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem sign44Fn : Callee Impl.MlDsa.RISCV64.Sign.sign44 (fun stk => signContract mlDsa44 RISCV64.abi stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.sign44_verified⟩, by decide +kernel⟩

theorem verify44Fn :
    Callee Impl.MlDsa.RISCV64.Verify.verify44 (fun stk => verifyContract mlDsa44 RISCV64.abi stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.verify44_verified⟩, by decide +kernel⟩

theorem signMessage44_sat : (signMessageContract mlDsa44 RISCV64.abi 1184).pre (msSat mlDsa44) := by
  sig_sat_check [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs, msSat]

theorem signMessage44_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage sign44Api.name Impl.MlDsa.RISCV64.Sign.sign44 mlDsa44)
      (signMessageContract mlDsa44 RISCV64.abi 1184) :=
  signMessage_verified (.inl rfl) (q := false) (by decide) sign44Fn _ ⟨_, signMessage44_sat⟩

/-- `tr` of `mvcSat` is `H` of its key by `mvcMem_tr`; the rest by evaluation. -/
theorem verifyMessageCached44_sat :
    (verifyMessageCachedContract mlDsa44 RISCV64.abi 1184).pre (mvcSat mlDsa44) := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs, mvcSat]
  sig_and_intros
  all_goals first
    | exact mvcMem_tr (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verifyMessageCached44_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessageCached verify44Api.name Impl.MlDsa.RISCV64.Verify.verify44 mlDsa44)
      (verifyMessageCachedContract mlDsa44 RISCV64.abi 1184) :=
  verifyMessageCached_verified (.inl rfl) (q := false) (by decide) verify44Fn _ ⟨_, verifyMessageCached44_sat⟩

theorem sign65Fn : Callee Impl.MlDsa.RISCV64.Sign.sign65 (fun stk => signContract mlDsa65 RISCV64.abi stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.sign65_verified⟩, by decide +kernel⟩

theorem verify65Fn :
    Callee Impl.MlDsa.RISCV64.Verify.verify65 (fun stk => verifyContract mlDsa65 RISCV64.abi stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.verify65_verified⟩, by decide +kernel⟩

theorem signMessage65_sat : (signMessageContract mlDsa65 RISCV64.abi 1184).pre (msSat mlDsa65) := by
  sig_sat_check [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs, msSat]

theorem signMessage65_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage sign65Api.name Impl.MlDsa.RISCV64.Sign.sign65 mlDsa65)
      (signMessageContract mlDsa65 RISCV64.abi 1184) :=
  signMessage_verified (.inr (.inl rfl)) (q := false) (by decide) sign65Fn _ ⟨_, signMessage65_sat⟩

/-- `tr` of `mvcSat` is `H` of its key by `mvcMem_tr`; the rest by evaluation. -/
theorem verifyMessageCached65_sat :
    (verifyMessageCachedContract mlDsa65 RISCV64.abi 1184).pre (mvcSat mlDsa65) := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs, mvcSat]
  sig_and_intros
  all_goals first
    | exact mvcMem_tr (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verifyMessageCached65_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessageCached verify65Api.name Impl.MlDsa.RISCV64.Verify.verify65 mlDsa65)
      (verifyMessageCachedContract mlDsa65 RISCV64.abi 1184) :=
  verifyMessageCached_verified (.inr (.inl rfl)) (q := false) (by decide) verify65Fn _ ⟨_, verifyMessageCached65_sat⟩

theorem sign87Fn : Callee Impl.MlDsa.RISCV64.Sign.sign87 (fun stk => signContract mlDsa87 RISCV64.abi stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.sign87_verified⟩, by decide +kernel⟩

theorem verify87Fn :
    Callee Impl.MlDsa.RISCV64.Verify.verify87 (fun stk => verifyContract mlDsa87 RISCV64.abi stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.verify87_verified⟩, by decide +kernel⟩

theorem signMessage87_sat : (signMessageContract mlDsa87 RISCV64.abi 1184).pre (msSat mlDsa87) := by
  sig_sat_check [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs, msSat]

theorem signMessage87_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage sign87Api.name Impl.MlDsa.RISCV64.Sign.sign87 mlDsa87)
      (signMessageContract mlDsa87 RISCV64.abi 1184) :=
  signMessage_verified (.inr (.inr rfl)) (q := false) (by decide) sign87Fn _ ⟨_, signMessage87_sat⟩

/-- `tr` of `mvcSat` is `H` of its key by `mvcMem_tr`; the rest by evaluation. -/
theorem verifyMessageCached87_sat :
    (verifyMessageCachedContract mlDsa87 RISCV64.abi 1184).pre (mvcSat mlDsa87) := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs, mvcSat]
  sig_and_intros
  all_goals first
    | exact mvcMem_tr (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verifyMessageCached87_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessageCached verify87Api.name Impl.MlDsa.RISCV64.Verify.verify87 mlDsa87)
      (verifyMessageCachedContract mlDsa87 RISCV64.abi 1184) :=
  verifyMessageCached_verified (.inr (.inr rfl)) (q := false) (by decide) verify87Fn _ ⟨_, verifyMessageCached87_sat⟩

/-! ## With prepared keys -/

/-- A state that satisfies `preparedSignMessageContract`'s precondition, with the prepared key in `m`. -/
def mspSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a3 => 0x10100 | .a5 => 0x10200 | .a6 => 0x11000 | .a7 => 0x20000
    | _ => 0
  sp := 0x100000
  mem := m
  rd := [⟨0x4000, preparedSecretKeyBytes p⟩, ⟨0x10000, 0⟩, ⟨0x10100, 0⟩, ⟨0x10200, 32⟩]
  wr := [⟨0x11000, p.sigLen⟩, ⟨0x20000, messageScratchWords p * 8⟩]

/-- `m`, with `H` of the encoded key at `0x4000` written to `tr`, at `0x12000`. -/
def trMem (p : Params) (m : Mem) : Mem := fun a =>
  if 0x12000 ≤ a.toNat ∧ a.toNat < 0x12040 then (pkTr (bytesAt m 0x4000 p.pkLen)).getD (a.toNat - 0x12000) 0
  else m a

/-- A state that satisfies `preparedVerifyMessageContract`'s precondition, with the prepared key in `m`. -/
def mvpSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a3 => 0x10100 | .a5 => 0x11000 | .a6 => 0x20000 | .a7 => 0x12000
    | _ => 0
  sp := 0x100000
  mem := trMem p m
  rd := [⟨0x4000, preparedPublicKeyBytes p⟩, ⟨0x10000, 0⟩, ⟨0x10100, 0⟩, ⟨0x11000, p.sigLen⟩, ⟨0x12000, 64⟩]
  wr := [⟨0x20000, messageScratchWords p * 8⟩]

theorem trMem_key {p : Params} {m : Mem} {L : Nat} (hp : L ≤ 0xE000) :
    bytesAt (trMem p m) 0x4000 L = bytesAt m 0x4000 L := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x4000 : Addr) + BitVec.ofNat 64 i).toNat = 0x4000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [trMem, he]
  split
  · rename_i h; omega
  · rfl

theorem trMem_tr {p : Params} {m : Mem} (hp : p.pkLen ≤ 0xE000) :
    bytesAt (trMem p m) 0x12000 64 = pkTr (bytesAt (trMem p m) 0x4000 p.pkLen) := by
  rw [trMem_key hp]
  have hl : (pkTr (bytesAt m 0x4000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0x12000 : Addr) + BitVec.ofNat 64 i).toNat = 0x12000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  simp only [trMem, he, show 0x12000 ≤ 0x12000 + i ∧ 0x12000 + i < 0x12040 by omega, and_self, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem mspSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedSecretKey p m 0x4000) : (signMessageEK p true 1184).pre (mspSat p m) := by
  simp only [signMessageEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedSignMessageContract, preparedSignMessageSig, RISCV64.abi, RISCV64.argRegs, mspSat]
    sig_and_intros
    all_goals first
      | exact hk
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem mvpSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedPublicKey p m 0x4000) : (verifyMessageEK p true 1184).pre (mvpSat p m) := by
  have hk' : PreparedPublicKey p (trMem p m) 0x4000 := by
    refine PreparedKey.preparedPublic_of_bytes (trMem_key ?_) hk
    rcases hp3 with rfl | rfl | rfl <;> decide
  have ht : p.pkLen ≤ 0xE000 := by rcases hp3 with rfl | rfl | rfl <;> decide
  simp only [verifyMessageEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, RISCV64.abi, RISCV64.argRegs, mvpSat]
    sig_and_intros
    all_goals first
      | exact hk'
      | exact trMem_tr ht
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem signPrepared44Fn :
    Callee (Impl.MlDsa.RISCV64.Sign.sign44E true) (fun stk => PreparedKey.signEK mlDsa44 true stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.signPrepared44_verified⟩, by decide +kernel⟩

theorem verifyPrepared44Fn :
    Callee (Impl.MlDsa.RISCV64.Verify.verify44E true) (fun stk => PreparedKey.verifyEK mlDsa44 true stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.verifyPrepared44_verified⟩, by decide +kernel⟩

theorem signMessagePrepared44_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa44")
        (Impl.MlDsa.RISCV64.Sign.sign44E true) mlDsa44)
      (preparedSignMessageContract mlDsa44 RISCV64.abi 1184) :=
  signMessage_verified (.inl rfl) (q := true) (by decide) signPrepared44Fn _
    (by obtain ⟨m, hm⟩ := PreparedKey.secret44_mem; exact ⟨mspSat _ m, mspSat_pre (.inl rfl) hm⟩)

theorem verifyMessagePrepared44_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa44")
        (Impl.MlDsa.RISCV64.Verify.verify44E true) mlDsa44)
      (preparedVerifyMessageContract mlDsa44 RISCV64.abi 1184) :=
  verifyMessageCached_verified (.inl rfl) (q := true) (by decide) verifyPrepared44Fn _
    (by obtain ⟨m, hm⟩ := PreparedKey.public44_mem; exact ⟨mvpSat _ m, mvpSat_pre (.inl rfl) hm⟩)

theorem signPrepared65Fn :
    Callee (Impl.MlDsa.RISCV64.Sign.sign65E true) (fun stk => PreparedKey.signEK mlDsa65 true stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.signPrepared65_verified⟩, by decide +kernel⟩

theorem verifyPrepared65Fn :
    Callee (Impl.MlDsa.RISCV64.Verify.verify65E true) (fun stk => PreparedKey.verifyEK mlDsa65 true stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.verifyPrepared65_verified⟩, by decide +kernel⟩

theorem signMessagePrepared65_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa65")
        (Impl.MlDsa.RISCV64.Sign.sign65E true) mlDsa65)
      (preparedSignMessageContract mlDsa65 RISCV64.abi 1184) :=
  signMessage_verified (.inr (.inl rfl)) (q := true) (by decide) signPrepared65Fn _
    (by obtain ⟨m, hm⟩ := PreparedKey.secret65_mem; exact ⟨mspSat _ m, mspSat_pre (.inr (.inl rfl)) hm⟩)

theorem verifyMessagePrepared65_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa65")
        (Impl.MlDsa.RISCV64.Verify.verify65E true) mlDsa65)
      (preparedVerifyMessageContract mlDsa65 RISCV64.abi 1184) :=
  verifyMessageCached_verified (.inr (.inl rfl)) (q := true) (by decide) verifyPrepared65Fn _
    (by obtain ⟨m, hm⟩ := PreparedKey.public65_mem; exact ⟨mvpSat _ m, mvpSat_pre (.inr (.inl rfl)) hm⟩)

theorem signPrepared87Fn :
    Callee (Impl.MlDsa.RISCV64.Sign.sign87E true) (fun stk => PreparedKey.signEK mlDsa87 true stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.signPrepared87_verified⟩, by decide +kernel⟩

theorem verifyPrepared87Fn :
    Callee (Impl.MlDsa.RISCV64.Verify.verify87E true) (fun stk => PreparedKey.verifyEK mlDsa87 true stk) 1184 :=
  ⟨⟨1184, Nat.le_refl _, PreparedKey.verifyPrepared87_verified⟩, by decide +kernel⟩

theorem signMessagePrepared87_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage (Proof.MlDsa.preparedSignName "mldsa87")
        (Impl.MlDsa.RISCV64.Sign.sign87E true) mlDsa87)
      (preparedSignMessageContract mlDsa87 RISCV64.abi 1184) :=
  signMessage_verified (.inr (.inr rfl)) (q := true) (by decide) signPrepared87Fn _
    (by obtain ⟨m, hm⟩ := PreparedKey.secret87_mem; exact ⟨mspSat _ m, mspSat_pre (.inr (.inr rfl)) hm⟩)

theorem verifyMessagePrepared87_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessageCached (Proof.MlDsa.preparedVerifyName "mldsa87")
        (Impl.MlDsa.RISCV64.Verify.verify87E true) mlDsa87)
      (preparedVerifyMessageContract mlDsa87 RISCV64.abi 1184) :=
  verifyMessageCached_verified (.inr (.inr rfl)) (q := true) (by decide) verifyPrepared87Fn _
    (by obtain ⟨m, hm⟩ := PreparedKey.public87_mem; exact ⟨mvpSat _ m, mvpSat_pre (.inr (.inr rfl)) hm⟩)

end VG.Proof.MlDsa.RISCV64.Message
