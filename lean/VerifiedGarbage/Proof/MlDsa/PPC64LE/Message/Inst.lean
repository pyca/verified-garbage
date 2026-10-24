module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.Verified
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Inst
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on PPC64LE, `sign_message` and `verify_message`, with this library's functions on `μ`

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message` calling the
PPC64LE `vg_mldsa*_sign` and `vg_mldsa*_verify` (`Sign/Inst.lean`,
`Verify/Inst.lean`), verified with 96 bytes of stack, whose frames use no
more (`sign44Fn`, …): so the functions on messages are verified with 96
(`signMessage44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa

theorem sign44Fn : Callee Impl.MlDsa.PPC64LE.Sign.sign44 (fun stk => signContract mlDsa44 PPC64LE.abi stk) 96 :=
  ⟨⟨96, Nat.le_refl _, Sign.sign44_verified⟩, by decide +kernel⟩

theorem verify44Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verify44 (fun stk => verifyContract mlDsa44 PPC64LE.abi stk) 96 :=
  ⟨⟨96, Nat.le_refl _, Verify.verify44_verified⟩, by decide +kernel⟩

theorem signMessage44_sat : (signMessageContract mlDsa44 PPC64LE.abi 96).pre (msSat mlDsa44) := by
  sig_sat_check [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs, msSat]

theorem verifyMessage44_sat : (verifyMessageContract mlDsa44 PPC64LE.abi 96).pre (mvSat mlDsa44) := by
  sig_sat_check [verifyMessageContract, verifyMessageSig, PPC64LE.abi, PPC64LE.argRegs, mvSat]

theorem signMessage44_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage sign44Api.name Impl.MlDsa.PPC64LE.Sign.sign44 mlDsa44)
      (signMessageContract mlDsa44 PPC64LE.abi 96) :=
  signMessage_verified (.inl rfl) (by decide) sign44Fn _ signMessage44_sat

theorem verifyMessage44_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessage verify44Api.name Impl.MlDsa.PPC64LE.Verify.verify44 mlDsa44)
      (verifyMessageContract mlDsa44 PPC64LE.abi 96) :=
  verifyMessage_verified (.inl rfl) (by decide) verify44Fn _ verifyMessage44_sat

theorem sign65Fn : Callee Impl.MlDsa.PPC64LE.Sign.sign65 (fun stk => signContract mlDsa65 PPC64LE.abi stk) 96 :=
  ⟨⟨96, Nat.le_refl _, Sign.sign65_verified⟩, by decide +kernel⟩

theorem verify65Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verify65 (fun stk => verifyContract mlDsa65 PPC64LE.abi stk) 96 :=
  ⟨⟨96, Nat.le_refl _, Verify.verify65_verified⟩, by decide +kernel⟩

theorem signMessage65_sat : (signMessageContract mlDsa65 PPC64LE.abi 96).pre (msSat mlDsa65) := by
  sig_sat_check [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs, msSat]

theorem verifyMessage65_sat : (verifyMessageContract mlDsa65 PPC64LE.abi 96).pre (mvSat mlDsa65) := by
  sig_sat_check [verifyMessageContract, verifyMessageSig, PPC64LE.abi, PPC64LE.argRegs, mvSat]

theorem signMessage65_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage sign65Api.name Impl.MlDsa.PPC64LE.Sign.sign65 mlDsa65)
      (signMessageContract mlDsa65 PPC64LE.abi 96) :=
  signMessage_verified (.inr (.inl rfl)) (by decide) sign65Fn _ signMessage65_sat

theorem verifyMessage65_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessage verify65Api.name Impl.MlDsa.PPC64LE.Verify.verify65 mlDsa65)
      (verifyMessageContract mlDsa65 PPC64LE.abi 96) :=
  verifyMessage_verified (.inr (.inl rfl)) (by decide) verify65Fn _ verifyMessage65_sat

theorem sign87Fn : Callee Impl.MlDsa.PPC64LE.Sign.sign87 (fun stk => signContract mlDsa87 PPC64LE.abi stk) 96 :=
  ⟨⟨96, Nat.le_refl _, Sign.sign87_verified⟩, by decide +kernel⟩

theorem verify87Fn :
    Callee Impl.MlDsa.PPC64LE.Verify.verify87 (fun stk => verifyContract mlDsa87 PPC64LE.abi stk) 96 :=
  ⟨⟨96, Nat.le_refl _, Verify.verify87_verified⟩, by decide +kernel⟩

theorem signMessage87_sat : (signMessageContract mlDsa87 PPC64LE.abi 96).pre (msSat mlDsa87) := by
  sig_sat_check [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs, msSat]

theorem verifyMessage87_sat : (verifyMessageContract mlDsa87 PPC64LE.abi 96).pre (mvSat mlDsa87) := by
  sig_sat_check [verifyMessageContract, verifyMessageSig, PPC64LE.abi, PPC64LE.argRegs, mvSat]

theorem signMessage87_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.signMessage sign87Api.name Impl.MlDsa.PPC64LE.Sign.sign87 mlDsa87)
      (signMessageContract mlDsa87 PPC64LE.abi 96) :=
  signMessage_verified (.inr (.inr rfl)) (by decide) sign87Fn _ signMessage87_sat

theorem verifyMessage87_verified :
    Verified PPC64LE.target
      (Impl.MlDsa.PPC64LE.Message.verifyMessage verify87Api.name Impl.MlDsa.PPC64LE.Verify.verify87 mlDsa87)
      (verifyMessageContract mlDsa87 PPC64LE.abi 96) :=
  verifyMessage_verified (.inr (.inr rfl)) (by decide) verify87Fn _ verifyMessage87_sat

end VG.Proof.MlDsa.PPC64LE.Message
