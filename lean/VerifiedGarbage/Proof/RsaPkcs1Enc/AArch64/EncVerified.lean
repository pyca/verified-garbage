import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the shared contract

`encK` is the shared contract `Spec.RsaPkcs1Enc.encryptContract` on the
registers and the stack (`encrypt_implies`), with the stack the frames use
and the callee's: `vg_rsa_pkcs1_encrypt`, calling any implementation `v` of
`vg_rsa_public_checked`, is verified against it (`enc_verified`), given that
it is satisfiable for `v`'s stack (which the registration file checks).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- The stack the function uses: the callee's, the inner frame and the
frame of its return address. -/
def encStack (v : PubImpl) : Nat := v.stack + 1088

theorem encStack_eq (v : PubImpl) : encStack v = v.S + 1 + 1088 := by rw [encStack, v.stack_eq]

theorem map_toNat_inj : ∀ {a b : List Byte}, a.map (·.toNat) = b.map (·.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

/-- The leak of `n` and `e`, split. -/
theorem leak_split {a b c d : List Byte} (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat))
    (hl : a.length = c.length) : a = c ∧ b = d := by
  rw [List.map_append, List.map_append] at h
  obtain ⟨e₁, e₂⟩ := List.append_inj h (by simp only [List.length_map, hl])
  exact ⟨map_toNat_inj e₁, map_toNat_inj e₂⟩

theorem encrypt_implies (S : Nat) (hsat : ∃ s, (Spec.RsaPkcs1Enc.encryptContract AArch64.abi (S + 1 + 1088)).pre s) :
    (encK (S + 1)).Implies (Spec.RsaPkcs1Enc.encryptContract AArch64.abi (S + 1 + 1088)) where
  pre := by
    intro s h
    sig_pre [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, AArch64.abi, AArch64.argRegs,
      _root_.List.range, _root_.List.range.loop, List.append_eq] at h
    simp only [encK]
    sig_split h
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    rintro s s' - h
    sig_post [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, AArch64.abi, AArch64.argRegs,
      _root_.List.range, _root_.List.range.loop, List.append_eq]
    exact h
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, AArch64.abi, AArch64.argRegs,
      _root_.List.range, _root_.List.range.loop, List.append_eq] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3⟩ := h
    obtain ⟨hn, he⟩ := leak_split hl (by rw [bytesAt_length, bytesAt_length, h3])
    refine ⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, ?_, ?_⟩
    · exact hn
    · exact he
  sat := hsat

/-- `vg_rsa_pkcs1_encrypt`, calling `v`. -/
theorem enc_verified (v : PubImpl)
    (hsat : ∃ s, (Spec.RsaPkcs1Enc.encryptContract AArch64.abi (encStack v)).pre s) :
    Verified AArch64.target (code v.name v.code) (Spec.RsaPkcs1Enc.encryptContract AArch64.abi (encStack v)) := by
  rw [encStack_eq] at hsat ⊢
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := enc_ok v h
    exact ⟨t, s', he, hp⟩) (enc_ct v) (encrypt_implies v.S hsat)

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
