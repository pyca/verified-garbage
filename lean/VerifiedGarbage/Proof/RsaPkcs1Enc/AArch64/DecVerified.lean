import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCT4
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: verified

The pieces' relations put together (`dec_ct`), and with correctness
(`dec_ok`): `vg_rsa_pkcs1_decrypt`, for any implementation `v` of SHA-256's
compression function and `pv` of `vg_rsa_private_checked`, is verified
against the shared contract with the stack it and its callee use
(`dec_verified`), given that the contract is satisfiable for it (which the
registration file checks).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

theorem pub_sp {P : Nat} {s₁ s₂ : State} (h : (decSpec P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

theorem dec_ct (v : Compress) (pv : PrivImpl) :
    ConstantTime isa (decSpec (pv.S + 1)).pre (decSpec (pv.S + 1)).pub (code (HH v) pv.name pv.code) := by
  have hS := pv.S15
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [body_eq]
  refine ((setup_ct pv.S).seq ((priv_ct pv).seq ((dBuild_ct pv.S).seq ((hashD_ct (v := v) hS).seq
    ((kdkMac_ct hS).seq ((clLoop_ct hS).seq ((amLoop_ct hS).seq (maskPart_ct.seq (alPart_ct.seq
      (scanPart_ct.seq selPart_ct)))))))))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack the function uses: the callee's and the frames'. -/
def decStack (pv : PrivImpl) : Nat := pv.stack + 224

theorem decStack_eq (pv : PrivImpl) : decStack pv = pv.S + 1 + 224 := by rw [decStack, pv.stack_eq]

/-- `vg_rsa_pkcs1_decrypt`, with `v` and `pv`. -/
theorem dec_verified (v : Compress) (pv : PrivImpl)
    (hsat : ∃ s, (Spec.RsaPkcs1Enc.decryptContract AArch64.abi (decStack pv)).pre s) :
    Verified AArch64.target (code (HH v) pv.name pv.code)
      (Spec.RsaPkcs1Enc.decryptContract AArch64.abi (decStack pv)) := by
  rw [decStack_eq] at hsat ⊢
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := dec_ok v pv h
    exact ⟨t, s', he, hp⟩) (dec_ct v pv) (Contract.Implies.refl hsat)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
