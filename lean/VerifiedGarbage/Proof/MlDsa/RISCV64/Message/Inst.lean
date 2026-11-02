module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Message.Verified
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Inst
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on RISC-V, `sign_message` and `verify_message`, with this library's functions on `μ`

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message` calling the
RISCV64 `vg_mldsa*_sign` and `vg_mldsa*_verify` (`Sign/Inst.lean`,
`Verify/Inst.lean`), verified with 1168 bytes of stack, whose frames use no
more (`sign44Fn`, …): so the functions on messages are verified with 1168
(`signMessage44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Callee)
open VG.Spec.MlDsa

theorem sign44Fn : Callee Impl.MlDsa.RISCV64.Sign.sign44 (fun stk => signContract mlDsa44 RISCV64.abi stk) 1168 :=
  ⟨⟨1168, Nat.le_refl _, Sign.sign44_verified⟩, by decide +kernel⟩

theorem verify44Fn :
    Callee Impl.MlDsa.RISCV64.Verify.verify44 (fun stk => verifyContract mlDsa44 RISCV64.abi stk) 1168 :=
  ⟨⟨1168, Nat.le_refl _, Verify.verify44_verified⟩, by decide +kernel⟩

theorem signMessage44_sat : (signMessageContract mlDsa44 RISCV64.abi 1168).pre (msSat mlDsa44) := by
  sig_sat_check [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs, msSat]

theorem verifyMessage44_sat : (verifyMessageContract mlDsa44 RISCV64.abi 1168).pre (mvSat mlDsa44) := by
  sig_sat_check [verifyMessageContract, verifyMessageSig, RISCV64.abi, RISCV64.argRegs, mvSat]

theorem signMessage44_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage sign44Api.name Impl.MlDsa.RISCV64.Sign.sign44 mlDsa44)
      (signMessageContract mlDsa44 RISCV64.abi 1168) :=
  signMessage_verified (.inl rfl) (by decide) sign44Fn _ signMessage44_sat

theorem verifyMessage44_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessage verify44Api.name Impl.MlDsa.RISCV64.Verify.verify44 mlDsa44)
      (verifyMessageContract mlDsa44 RISCV64.abi 1168) :=
  verifyMessage_verified (.inl rfl) (by decide) verify44Fn _ verifyMessage44_sat

theorem sign65Fn : Callee Impl.MlDsa.RISCV64.Sign.sign65 (fun stk => signContract mlDsa65 RISCV64.abi stk) 1168 :=
  ⟨⟨1168, Nat.le_refl _, Sign.sign65_verified⟩, by decide +kernel⟩

theorem verify65Fn :
    Callee Impl.MlDsa.RISCV64.Verify.verify65 (fun stk => verifyContract mlDsa65 RISCV64.abi stk) 1168 :=
  ⟨⟨1168, Nat.le_refl _, Verify.verify65_verified⟩, by decide +kernel⟩

theorem signMessage65_sat : (signMessageContract mlDsa65 RISCV64.abi 1168).pre (msSat mlDsa65) := by
  sig_sat_check [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs, msSat]

theorem verifyMessage65_sat : (verifyMessageContract mlDsa65 RISCV64.abi 1168).pre (mvSat mlDsa65) := by
  sig_sat_check [verifyMessageContract, verifyMessageSig, RISCV64.abi, RISCV64.argRegs, mvSat]

theorem signMessage65_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage sign65Api.name Impl.MlDsa.RISCV64.Sign.sign65 mlDsa65)
      (signMessageContract mlDsa65 RISCV64.abi 1168) :=
  signMessage_verified (.inr (.inl rfl)) (by decide) sign65Fn _ signMessage65_sat

theorem verifyMessage65_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessage verify65Api.name Impl.MlDsa.RISCV64.Verify.verify65 mlDsa65)
      (verifyMessageContract mlDsa65 RISCV64.abi 1168) :=
  verifyMessage_verified (.inr (.inl rfl)) (by decide) verify65Fn _ verifyMessage65_sat

theorem sign87Fn : Callee Impl.MlDsa.RISCV64.Sign.sign87 (fun stk => signContract mlDsa87 RISCV64.abi stk) 1168 :=
  ⟨⟨1168, Nat.le_refl _, Sign.sign87_verified⟩, by decide +kernel⟩

theorem verify87Fn :
    Callee Impl.MlDsa.RISCV64.Verify.verify87 (fun stk => verifyContract mlDsa87 RISCV64.abi stk) 1168 :=
  ⟨⟨1168, Nat.le_refl _, Verify.verify87_verified⟩, by decide +kernel⟩

theorem signMessage87_sat : (signMessageContract mlDsa87 RISCV64.abi 1168).pre (msSat mlDsa87) := by
  sig_sat_check [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs, msSat]

theorem verifyMessage87_sat : (verifyMessageContract mlDsa87 RISCV64.abi 1168).pre (mvSat mlDsa87) := by
  sig_sat_check [verifyMessageContract, verifyMessageSig, RISCV64.abi, RISCV64.argRegs, mvSat]

theorem signMessage87_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.signMessage sign87Api.name Impl.MlDsa.RISCV64.Sign.sign87 mlDsa87)
      (signMessageContract mlDsa87 RISCV64.abi 1168) :=
  signMessage_verified (.inr (.inr rfl)) (by decide) sign87Fn _ signMessage87_sat

theorem verifyMessage87_verified :
    Verified RISCV64.target
      (Impl.MlDsa.RISCV64.Message.verifyMessage verify87Api.name Impl.MlDsa.RISCV64.Verify.verify87 mlDsa87)
      (verifyMessageContract mlDsa87 RISCV64.abi 1168) :=
  verifyMessage_verified (.inr (.inr rfl)) (by decide) verify87Fn _ verifyMessage87_sat

end VG.Proof.MlDsa.RISCV64.Message
