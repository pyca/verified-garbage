module

import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcBody
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcBuild
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcVerified.lean`): the frames around
the body (`wrap_ok`, `wrap_ct`), the result as the shared contract states
it, and a state that meets it (`sat`): `vg_rsa_pkcs1_encrypt_precomputed`,
calling any implementation `c` of `vg_rsa_public_precomputed_checked`, is
verified (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- Encryption, once the lengths are as the contract has them. -/
theorem encrypt_eq {nB eB M PS : List Byte} (hM : M.length + 11 ≤ nB.length)
    (hPS : PS.length = nB.length - M.length - 3) :
    Spec.RsaPkcs1Enc.encrypt nB eB M PS =
      if zm PS = 0 then Spec.Rsa.publicOpChecked nB eB (Spec.RsaPkcs1Enc.encode M PS) else none := by
  simp only [Spec.RsaPkcs1Enc.encrypt, hM, hPS, true_and, zm]
  split <;> simp_all

theorem spec_sp {s : State} (h : spec.pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, -⟩ := h
  exact ⟨hsp, by omega⟩

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem code_ok (c : Ver.PublicImpl) {s : State} (h : spec.pre s) :
    WP isa (code c.name c.code) s fun t => abiPreserved s t ∧ spec.post s t := by
  have hin := in_of_pre h
  obtain ⟨hs, hfit⟩ := spec_sp h
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hs ⊢; omega
  have hb := (body_vp (P := ep s) c).wp _ _ (entered_state h)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp c) hsp hfit (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 44) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 44) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro) => entered_ro hsp ok hR
    sig_post [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
      argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    intro hp
    have hn : (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat).length = (arg s 3).toNat :=
      Proof.RsaPkcs1Sig.bytesAt_len _ _ _
    have w := res _ hn hp
    have hM : msgB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64)
        (arg s 7).toNat := ro (R := (ep s).MSG) (by simp)
    have hP : psB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64)
        (arg s 9).toNat := ro (R := (ep s).PS) (by simp)
    have hml := hin.mlK
    have hpl := hin.plK
    rw [encrypt_eq (by simp only [Proof.RsaPkcs1Sig.bytesAt_len]; exact hml)
      (by simp only [Proof.RsaPkcs1Sig.bytesAt_len]; exact hpl)]
    simp only [enc] at w
    rw [hM, hP] at w
    exact w

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hp
  obtain ⟨hab, hc⟩ := List.append_inj hl (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a3, a5])
  obtain ⟨-, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a3])
  have hw := map_toNat_inj hc
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]
  rw [a4, a5] at he
  rw [a12, a13] at hw
  rw [he, hw]

theorem code_ct (c : Ver.PublicImpl) : ConstantTime isa spec.pre spec.pub (code c.name c.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
      argVal, argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus of 64 bytes, `e` of one,
an empty message, the padding string of 61 bytes, and the stack arguments
above `0x20000`. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x10 else if a = 131080 then 64 else if a = 131085 then 0x20 else
    if a = 131088 then 64 else if a = 131093 then 0x21 else if a = 131096 then 1 else
    if a = 131101 then 0x30 else if a = 131109 then 0x31 else if a = 131112 then 61 else
    if a = 131117 then 0x40 else if a = 131120 then 0x20 else if a = 131121 then 4 else
    if a = 131125 then 0x70 else if a = 131128 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 61⟩, ⟨0x7000, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩, ⟨0x20004, 56⟩]

theorem sat : ∃ s, spec.pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 0x2000 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 0x2100 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 0x3000 := by decide
  have a7 : arg satState 7 = 0 := by decide
  have a8 : arg satState 8 = 0x3100 := by decide
  have a9 : arg satState 9 = 61 := by decide
  have a10 : arg satState 10 = 0x4000 := by decide
  have a11 : arg satState 11 = 1056 := by decide
  have a12 : arg satState 12 = 0x7000 := by decide
  have a13 : arg satState 13 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.scratchWords, Spec.Rsa.precomputedWords,
      Spec.Rsa.modulusWords] using satState

theorem code_noSp (c : Ver.PublicImpl) : NoSp (code c.name c.code) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp c)) restore_noSp)

theorem code_sp (c : Ver.PublicImpl) : (code c.name c.code).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp c)

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling `c`, meets the shared contract. -/
theorem code_verified (c : Ver.PublicImpl) : Verified target (code c.name c.code) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct c, sat⟩

end VG.Proof.RsaPkcs1Enc.X86.Pc
