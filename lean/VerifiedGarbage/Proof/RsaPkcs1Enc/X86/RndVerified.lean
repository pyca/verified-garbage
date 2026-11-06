module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndAccept
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndReject
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Wrap

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86: verified

The body (`body_vp`): the scan's registers, the scan, and `PS` drawn
(`Proof/RsaPkcs1Enc/X86/RndAccept.lean`) or not (`RndReject.lean`). The frames
around it (`wrap_ok`, `wrap_ct`), the result as the shared contract states
it, and a state that meets it (`sat`): `vg_rsa_pkcs1_encrypt_random`,
calling `vg_rsa_pkcs1_encrypt_precomputed` (by the name `encName`) with any
implementation `c` of `vg_rsa_public_precomputed_checked`, is verified
(`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Rnd

open VG VG.Impl.RsaPkcs1Enc.X86.Random VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable {P : RP}

/-- The callee's name. -/
def encName : String := "vg_rsa_pkcs1_encrypt_precomputed"

/-- The code of the callee, calling `c`. -/
abbrev enc (c : Ver.PublicImpl) : Prog isa := Impl.RsaPkcs1Enc.X86.Precomputed.code c.name c.code

theorem body_vp (encName : String) (c : Ver.PublicImpl) : VP (S P) (body encName (enc c)) (Fin P) :=
  head_vp.seq (scan_vp.seq (cmp_vp.seq (VP.ite (fun _ _ h => ⟨_, h.2⟩)
    (fun _ _ _ _ h₁ h₂ => by show eval .e _ = eval .e _; simp only [eval]; rw [h₁.2, h₂.2])
    (accept_vp encName c) reject_vp)))

theorem noSp_ite {c : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite c a b) := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h, hb i h]

theorem body_noSp (encName : String) (c : Ver.PublicImpl) : NoSp (body encName (enc c)) :=
  noSp_seq (.of_all (by decide)) (noSp_seq (.of_all (by decide)) (noSp_seq (.of_all (by decide))
    (noSp_ite (noSp_seq (.of_all (by decide)) (noSp_seq (.of_all (by decide)) (noSp_seq (.of_all (by decide))
      (noSp_seq (noSp_call (Pc.code_noSp c)) (.of_all (by decide)))))) (.of_all (by decide)))))

theorem spec_sp {s : State} (h : spec.pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argSlots,
    argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, -⟩ := h
  exact ⟨hsp, by omega⟩

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem code_ok (encName : String) (c : Ver.PublicImpl) {s : State} (h : spec.pre s) :
    WP isa (code encName (enc c)) s fun t => abiPreserved s t ∧ spec.post s t := by
  have hin := in_of_pre h
  obtain ⟨hs, hfit⟩ := spec_sp h
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hs ⊢; omega
  have hb := (body_vp (P := ep s) encName c).wp _ _ (entered_state h)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp encName c) hsp hfit (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := roomC) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := roomC) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro) => entered_ro hsp ok hR
    have hR : rB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat :=
      ro (R := (ep s).RAND) (by simp)
    have hM : msgB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat :=
      ro (R := (ep s).MSG) (by simp)
    unfold Res at res
    rw [hR, hM] at res
    sig_post [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argSlots,
      argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argSlots,
    argVal, argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hp
  have l1 : ((Spec.Rsa.bytesAt s₁.mem ((arg s₁ 3).setWidth 64) (arg s₁ 4).toNat ++
      Spec.Rsa.bytesAt s₁.mem ((arg s₁ 5).setWidth 64) (arg s₁ 6).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt s₂.mem ((arg s₂ 3).setWidth 64) (arg s₂ 4).toNat ++
      Spec.Rsa.bytesAt s₂.mem ((arg s₂ 5).setWidth 64) (arg s₂ 6).toNat).map (·.toNat)).length := by
    simp [Proof.RsaPkcs1Sig.bytesAt_len, a4, a6]
  have l2 : ((Spec.Rsa.wordsAt s₁.mem ((arg s₁ 13).setWidth 64) (arg s₁ 14).toNat).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt s₂.mem ((arg s₂ 13).setWidth 64) (arg s₂ 14).toNat).map (·.toNat)).length := by
    simp [Spec.Rsa.wordsAt, a14]
  obtain ⟨h12, h3⟩ := List.append_inj hl (by simp only [List.length_append, l1, l2])
  obtain ⟨h1, h2⟩ := List.append_inj h12 l1
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj h1) (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a4])
  have hw := map_toNat_inj h2
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]
  rw [a3, a4] at hn
  rw [a5, a6] at he
  rw [a13, a14] at hw
  rw [a4, a8, a9, a10] at h3
  rw [hn, he, hw, h3]

theorem code_ct (encName : String) (c : Ver.PublicImpl) :
    ConstantTime isa spec.pre spec.pub (code encName (enc c)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argSlots,
      argVal, argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp encName c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) encName c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus of 64 bytes, `e` of one,
an empty message and tape, and the stack arguments above `0x20000`. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x10 else if a = 131080 then 64 else if a = 131085 then 0x80 else
    if a = 131089 then 0x20 else if a = 131092 then 64 else if a = 131097 then 0x21 else
    if a = 131100 then 1 else if a = 131105 then 0x30 else if a = 131113 then 0x31 else
    if a = 131121 then 0x40 else if a = 131124 then 0x20 else if a = 131125 then 4 else
    if a = 131129 then 0x70 else if a = 131132 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x7000, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 16⟩, ⟨0x4000, 8448⟩, ⟨0x20004, 60⟩]

theorem sat : ∃ s, spec.pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 0x8000 := by decide
  have a3 : arg satState 3 = 0x2000 := by decide
  have a4 : arg satState 4 = 64 := by decide
  have a5 : arg satState 5 = 0x2100 := by decide
  have a6 : arg satState 6 = 1 := by decide
  have a7 : arg satState 7 = 0x3000 := by decide
  have a8 : arg satState 8 = 0 := by decide
  have a9 : arg satState 9 = 0x3100 := by decide
  have a10 : arg satState 10 = 0 := by decide
  have a11 : arg satState 11 = 0x4000 := by decide
  have a12 : arg satState 12 = 1056 := by decide
  have a13 : arg satState 13 = 0x7000 := by decide
  have a14 : arg satState 14 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, e, esp, satState, stackBytes, frameBytes,
      roomC, Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.scratchWords, Spec.Rsa.precomputedWords,
      Spec.Rsa.modulusWords, Spec.RsaPkcs1Enc.padEntropy] using satState

theorem code_noSp (encName : String) (c : Ver.PublicImpl) : NoSp (code encName (enc c)) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp encName c)) restore_noSp)

theorem code_sp (encName : String) (c : Ver.PublicImpl) :
    (code encName (enc c)).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp encName c)

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
with `c`, meets the shared contract. -/
theorem code_verified (encName : String) (c : Ver.PublicImpl) : Verified target (code encName (enc c)) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok encName c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct encName c, sat⟩

end VG.Proof.RsaPkcs1Enc.X86.Rnd
