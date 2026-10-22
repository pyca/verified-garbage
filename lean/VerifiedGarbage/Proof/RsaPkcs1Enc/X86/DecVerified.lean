module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecBody
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecBase
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 decryption on x86: verified

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecVerified.lean`): the frames around
the body (`wrap_ok`, `wrap_ct`), the result as the shared contract states
it, and a state that meets it (`sat`): `vg_rsa_pkcs1_decrypt`, calling
`vg_rsa_private_checked` over any implementation `c` of
`vg_rsa_private_crt` and SHA-256's and HMAC-SHA-256's functions made with
any SHA-256 backend `v`, is verified (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

/-- The code, with the backend `v` and calling `vg_rsa_private_checked` over `c`. -/
abbrev decryptCode (v : Backend) (c : CrtImpl) : Prog isa := code v.F (privName c) (privCode c)

theorem spec_sp {s : State} (h : spec.pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  obtain ⟨hsp, hsa, -⟩ := h
  exact ⟨hsp, by omega⟩

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem code_ok (v : Backend) (c : CrtImpl) {s : State} (h : spec.pre s) :
    WP isa (decryptCode v c) s fun t => abiPreserved s t ∧ spec.post s t := by
  have hin := in_of_pre h
  obtain ⟨hs, hfit⟩ := spec_sp h
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hs ⊢; omega
  have hb := (body_vp (P := ep s) v c).wp _ _ (entered_state h)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp v c) hsp hfit (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 3392) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 3392) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro) => entered_ro hsp ok hR
    sig_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes]
    unfold Res at res
    rw [show dB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).D) (by simp),
      show cB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).INP) (by simp),
      show pB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).PP) (by simp),
      show qB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).QQ) (by simp),
      show dpB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DP) (by simp),
      show dqB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DQ) (by simp),
      show qiB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).QI) (by simp)] at res
    rw [BitVec.setWidth_append_eq_right]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22⟩ := hp
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a4])
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a11, a12, a13, a14, a15, a17, a19, a21, a22]
  rw [a3, a4] at hn
  rw [a5, a6] at he
  rw [hn, he]

theorem code_ct (v : Backend) (c : CrtImpl) : ConstantTime isa spec.pre spec.pub (decryptCode v c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp v c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) v c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus and a ciphertext of 64
bytes, `e`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` of one byte, and the stack
arguments above `0x20000`. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 16 else if a = 131080 then 64 else if a = 131085 then 104 else
    if a = 131089 then 32 else if a = 131092 then 64 else if a = 131097 then 33 else if a = 131100 then 1 else
    if a = 131105 then 34 else if a = 131108 then 1 else if a = 131113 then 48 else if a = 131116 then 64 else
    if a = 131121 then 49 else if a = 131124 then 1 else if a = 131129 then 50 else if a = 131132 then 1 else
    if a = 131137 then 51 else if a = 131140 then 1 else if a = 131145 then 52 else if a = 131148 then 1 else
    if a = 131153 then 53 else if a = 131156 then 1 else if a = 131161 then 64 else if a = 131164 then 32 else
    if a = 131165 then 4 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x3000, 64⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩,
    ⟨0x3400, 1⟩, ⟨0x3500, 1⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x6800, 8⟩, ⟨0x4000, 8448⟩, ⟨0x20004, 92⟩]

theorem sat : ∃ s, spec.pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 0x6800 := by decide
  have a3 : arg satState 3 = 0x2000 := by decide
  have a4 : arg satState 4 = 64 := by decide
  have a5 : arg satState 5 = 0x2100 := by decide
  have a6 : arg satState 6 = 1 := by decide
  have a7 : arg satState 7 = 0x2200 := by decide
  have a8 : arg satState 8 = 1 := by decide
  have a9 : arg satState 9 = 0x3000 := by decide
  have a10 : arg satState 10 = 64 := by decide
  have a11 : arg satState 11 = 0x3100 := by decide
  have a12 : arg satState 12 = 1 := by decide
  have a13 : arg satState 13 = 0x3200 := by decide
  have a14 : arg satState 14 = 1 := by decide
  have a15 : arg satState 15 = 0x3300 := by decide
  have a16 : arg satState 16 = 1 := by decide
  have a17 : arg satState 17 = 0x3400 := by decide
  have a18 : arg satState 18 = 1 := by decide
  have a19 : arg satState 19 = 0x3500 := by decide
  have a20 : arg satState 20 = 1 := by decide
  have a21 : arg satState 21 = 0x4000 := by decide
  have a22 : arg satState 22 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes,
    stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, e,
      esp, satState, stackBytes, frameBytes, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using satState

theorem code_noSp (v : Backend) (c : CrtImpl) : NoSp (decryptCode v c) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp v c)) restore_noSp)

theorem code_sp (v : Backend) (c : CrtImpl) : (decryptCode v c).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp v c)

/-- `vg_rsa_pkcs1_decrypt` with the backend `v`, calling `vg_rsa_private_checked` over `c`, meets the
shared contract. -/
theorem code_verified (v : Backend) (c : CrtImpl) : Verified target (decryptCode v c) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok v c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct v c, sat⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
