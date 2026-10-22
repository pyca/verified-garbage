module

public import VerifiedGarbage.Proof.RsaPss.X86.SgCall
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# RSASSA-PSS signing on x86: verified

As on ARMv7 (`Proof/RsaPss/Arm/SgVerified.lean`): the body (`body_vp`),
which writes `esp` only through the frames of its calls (`body_noSp`), the
frames around it (`wrap_ok`, `wrap_ct`) and the result as the shared
contract states it: `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling
`vg_rsa_private_checked` over any implementation `v` of
`vg_rsa_private_crt`, is verified for any hash function `h` it is given a
satisfiable contract for (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

variable (h : PssHash)

theorem body_noSp (v : CrtImpl) : NoSp (signBody h.H (privName v) (privCode v)) := by
  have sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig16
  have p3 := sp.cpSalt
  have p4 := sp.lenArgs18
  have p5 := sp.putH
  have hct := ctHash_noSp h
  have hm := mgfXor_noSp h
  have hp := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  simp only [signBody, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [signEnc, yDig, signFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

theorem body_vp (P : EP) (v : CrtImpl) :
    VP (S h P) (signBody h.H (privName v) (privCode v)) (Fin h P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1⟩
  show VP _ (.seq (.block (signChk ++ params h.H)) (.ite .ne signFail (.seq (signEnc h.H) (.seq (.block privArgs)
    (.call (privName v) (privCode v)))))) _
  exact (chk_vp h P).seq (VP.ite (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.2.2.2.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2.2, h₂.2.2.2.2.2])
    (fail_vp h P) (((enc_vp h P hP).mono (fun σ s ⟨h1, e⟩ => e0_of h h1 e) fun _ _ h => h).seq
      ((pa_vp h P).seq (call_vp h P v))))

/-- The code, calling `vg_rsa_private_checked` over `v`. -/
abbrev signCode (v : CrtImpl) : Prog isa := sign h.H (privName v) (privCode v)

theorem spec_sp {s : State} (hs : (spec h.G).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argSlots, argVal, argBytes, stackBelow] at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem entered_state {s : State} (hs : (spec h.G).pre s) :
    S h (ep s) (entered frameBytes s) (entered frameBytes s) := by
  have hi := in_of_pre hs
  rw [h.glen] at hi
  exact ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem code_ok (v : CrtImpl) {s : State} (hs : (spec h.G).pre s) :
    WP isa (signCode h v) s fun t => abiPreserved s t ∧ (spec h.G).post s t := by
  have hin := in_of_pre hs
  rw [h.glen] at hin
  obtain ⟨hsp0, hfit⟩ := spec_sp h hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hb := (body_vp h (ep s) v).wp _ _ (entered_state h hs)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp h v) hsp hfit (W := ((ep s).lay h.D).W)
    (Q := fun r m => Res h (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro h.D) (rw := (ep s).rw) (C := 3392) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro h.D) (rw := (ep s).rw) (C := 3392) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro h.D) => entered_ro hsp ok hR
    sig_post [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argSlots, argVal, argBytes]
    unfold Res at res
    rw [show pB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).PP) (by simp),
      show qB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).QQ) (by simp),
      show dpB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DP) (by simp),
      show dqB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DQ) (by simp),
      show qiB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).QI) (by simp),
      show digB h (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DIG h.D) (by simp),
      show saltB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).SALT) (by simp)] at res
    rw [BitVec.setWidth_append_eq_right, h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h.G).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argSlots, argVal, argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20⟩ := hp
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a3])
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a12, a14, a16, a17, a18, a19, a20]
  rw [a2, a3] at hn
  rw [a4, a5] at he
  rw [hn, he]

theorem code_ct (v : CrtImpl) : ConstantTime isa (spec h.G).pre (spec h.G).pub (signCode h v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argSlots, argVal, argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp h v) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h (ep s₁) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h h₁, by rw [hep]; exact entered_state h h₂⟩

theorem code_noSp (v : CrtImpl) : NoSp (signCode h v) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp h v)) restore_noSp)

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling `vg_rsa_private_checked` over `v`, meets the shared
contract (satisfiable, `SgSat.lean`). -/
theorem sign_verified (hsat : ∃ s, (spec h.G).pre s) (v : CrtImpl) :
    Verified target (signCode h v) (spec h.G) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h v, hsat⟩

end VG.Proof.RsaPss.X86.Sg
