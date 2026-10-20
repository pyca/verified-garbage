module

import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.RsaPss.Arm.SgChk
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS signing on ARMv7: verified

The body (`body_vp`): the checks, then zeros and 0 if something does not
fit, or the encoding and the call. The frames around it (`wrap_ok`,
`wrap_ct`), the result as the shared contract states it, and a state that
meets it (`sat`): `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling
`vg_rsa_private_checked` over any implementation `v` of
`vg_rsa_private_crt`, is verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable (h : PssHash)

theorem body_vp (P : EP) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (S h P) (signBody h.H (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Fin h P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1⟩
  show VP _ (.seq (.block (signChk h.H)) (.seq (.block (params ++ saltFits)) (.ite .ne signFail
    (.seq (signEnc h.H) (.seq (.block privArgs) (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v))))))) _
  exact (chk_vp h P).seq ((par_vp h P).seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.2.2.2.2.2, h₂.2.2.2.2.2])
    (fail_vp h P) (((enc_vp h P hP).mono (fun σ s ⟨h1, e⟩ => e0_of h h1 e) fun _ _ h => h).seq
      ((pa_vp h P).seq (call_vp h P v)))))

/-- The code, calling `vg_rsa_private_checked` over `v`. -/
abbrev signCode (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  sign h.H (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)

theorem entered_state {s : State} (hs : (spec h.G).pre s) :
    S h (ep s) (entered frameBytes s) (entered frameBytes s) := by
  have hi := in_of_pre hs
  rw [h.glen] at hi
  exact ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (hs : (spec h.G).pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val] at hs
  exact hs.1

theorem code_ok (v : Proof.Rsa.Arm.CrtImpl) {s : State} (hs : (spec h.G).pre s) :
    WP isa (signCode h v) s fun t => abiPreserved s t ∧ (spec h.G).post s t := by
  have hsp := spec_sp h hs
  have hin := in_of_pre hs
  rw [h.glen] at hin
  have st := entered_state h hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  have hb := (body_vp h (ep s) v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := ((ep s).lay h.D).W)
    (Q := fun r m => Res h (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 68) (C := 3440) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).PP, (ep s).QQ, (ep s).DP, (ep s).DQ, (ep s).QI, (ep s).DIG h.D, (ep s).SALT])
      (rw := [(ep s).OUT, (ep s).SCR]) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).PP, (ep s).QQ, (ep s).DP, (ep s).DQ, (ep s).QI,
        (ep s).DIG h.D, (ep s).SALT]) =>
      entered_ro (F := frameBytes) (A := 68) (C := 3440) (argv := (ep s).argv) (rw := [(ep s).OUT, (ep s).SCR])
        hin.ok hsp' hR
    have hP : pB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2))
        (stackArg s 3).toNat := ro (R := (ep s).PP) (by simp)
    have hQ : qB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4))
        (stackArg s 5).toNat := ro (R := (ep s).QQ) (by simp)
    have hDP : dpB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6))
        (stackArg s 3).toNat := ro (R := (ep s).DP) (by simp)
    have hDQ : dqB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 8))
        (stackArg s 5).toNat := ro (R := (ep s).DQ) (by simp)
    have hQI : qiB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10))
        (stackArg s 3).toNat := ro (R := (ep s).QI) (by simp)
    have hD : digB h (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 12)) h.D :=
      ro (R := (ep s).DIG h.D) (by simp)
    have hS : saltB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 13))
        (stackArg s 14).toNat := ro (R := (ep s).SALT) (by simp)
    unfold Res at res
    rw [hP, hQ, hDP, hDQ, hQI, hD, hS] at res
    rw [h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h.G).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hp
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, h3])
  simp only [ep]
  rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a8, a10, a12, a13, a14, a15, a16]
  rw [h2, h3] at hn
  rw [a0, a1] at he
  rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
    show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he]

theorem code_ct (v : Proof.Rsa.Arm.CrtImpl) : ConstantTime isa (spec h.G).pre (spec h.G).pub (signCode h v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h (ep s₁) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h h₁, by rw [hep]; exact entered_state h h₂⟩

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign`, calling `vg_rsa_private_checked` over `v`, meets the shared
contract (satisfiable, `SgSat.lean`). -/
theorem sign_verified (hsat : ∃ s, (spec h.G).pre s) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (signCode h v) (spec h.G) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h v, hsat⟩

end VG.Proof.RsaPss.Arm.Sg
