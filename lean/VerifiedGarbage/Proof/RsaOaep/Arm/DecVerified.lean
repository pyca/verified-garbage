module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecEnd
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Wrap
public import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Nat.Bitwise.Basic

/-!
# RSAES-OAEP decryption on ARMv7: verified

The body (`body_vp`): the private-key operation into `EM`'s place, then
zeros and `(r = 2) ? 2 : 0` if `k < 2 hLen + 2`, or the decoding. The
frames around it (`wrap_ok`, `wrap_ct`), the result as the shared contract
states it: `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, calling
`vg_rsa_private_checked` over any implementation `v` of
`vg_rsa_private_crt`, is verified (`dec_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {F G H : State → State → Prop} {a b c d e r : Prog isa}

theorem relCT_assoc' {Q R : State → State → Prop} (h : RelCT isa Q (.seq a (.seq b c)) R) :
    RelCT isa Q (.seq (.seq a b) c) R := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem VP.assoc' (h : VP F (.seq a (.seq b c)) G) : VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_assoc' h.ct⟩

/-- A piece of `n` steps, then the rest. -/
theorem VP.cont2 (h : VP F (.seq a b) G) (h₂ : VP G r H) : VP F (.seq a (.seq b r)) H := VP.assoc (h.seq h₂)

theorem VP.cont3 (h : VP F (.seq a (.seq b c)) G) (h₂ : VP G r H) : VP F (.seq a (.seq b (.seq c r))) H :=
  VP.assoc (VP.cont2 (VP.assoc' h) h₂)

theorem VP.cont4 (h : VP F (.seq a (.seq b (.seq c d))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d r)))) H :=
  VP.assoc (VP.cont3 (VP.assoc' h) h₂)

theorem VP.cont5 (h : VP F (.seq a (.seq b (.seq c (.seq d e)))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d (.seq e r))))) H :=
  VP.assoc (VP.cont4 (VP.assoc' h) h₂)

end

variable (h g : OHash)

/-- The decoding, when `k ≥ 2 hLen + 2`. -/
theorem main_vp (P : EP) :
    VP (fun σ s => C2 h.H.D P σ s ∧ isa.eval .ne s = some false) (decMain h.H g.H) (Fin h.G g.G P) :=
  (lab_vp h P).seq (VP.cont4 (unmask_vp h g P) (VP.cont5 (acc_vp h g P) (VP.cont3 (tscan_vp h g P)
    (VP.cont4 (buf_vp h g P) ((shift_vp h g P).seq ((okMask_vp h g P).seq (VP.cont2 (outCopy_vp h g P)
      (VP.cont2 (outMask_vp h g P) (end_vp h g P)))))))))

theorem body_vp (P : EP) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (S P) (decBody h.H g.H (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Fin h.G g.G P) :=
  (start_vp P).seq ((pa_vp P).seq ((call_vp P v).seq ((chk_vp h P).seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.2.2.2.2.2, h₂.2.2.2.2.2])
    (fail_vp h g P) (main_vp h g P)))))

/-- The code, calling `vg_rsa_private_checked` over `v`. -/
abbrev decCode (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  decrypt h.H g.H (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)

theorem entered_state {s : State} (hs : (spec h g).pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) := by
  have hi := in_of_pre hs
  exact ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (hs : (spec h g).pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, reduceClassify, Loc.val] at hs
  exact hs.1

theorem code_ok (v : Proof.Rsa.Arm.CrtImpl) {s : State} (hs : (spec h g).pre s) :
    WP isa (decCode h g v) s fun t => abiPreserved s t ∧ (spec h g).post s t := by
  have hsp := spec_sp h g hs
  have hin := in_of_pre hs
  have st := entered_state h g hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  have hb := (body_vp h g (ep s) v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := (ep s).lay.W)
    (Q := fun r m => Res h.G g.G (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 76) (C := 3440) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).PP, (ep s).QQ, (ep s).DP, (ep s).DQ, (ep s).QI, (ep s).LAB, (ep s).CT])
      (rw := [(ep s).OUT, (ep s).ML, (ep s).SCR]) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).PP, (ep s).QQ, (ep s).DP, (ep s).DQ,
        (ep s).QI, (ep s).LAB, (ep s).CT]) =>
      entered_ro (F := frameBytes) (A := 76) (C := 3440) (argv := (ep s).argv)
        (rw := [(ep s).OUT, (ep s).ML, (ep s).SCR]) hin.ok hsp' hR
    have hP : pB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3))
        (stackArg s 4).toNat := ro (R := (ep s).PP) (by simp)
    have hQ : qB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5))
        (stackArg s 6).toNat := ro (R := (ep s).QQ) (by simp)
    have hDP : dpB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 7))
        (stackArg s 4).toNat := ro (R := (ep s).DP) (by simp)
    have hDQ : dqB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 9))
        (stackArg s 6).toNat := ro (R := (ep s).DQ) (by simp)
    have hQI : qiB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 11))
        (stackArg s 4).toNat := ro (R := (ep s).QI) (by simp)
    have hL : labB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 13))
        (stackArg s 14).toNat := ro (R := (ep s).LAB) (by simp)
    have hC : ctB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 15))
        (stackArg s 0).toNat := ro (R := (ep s).CT) (by simp)
    unfold Res at res
    rw [hP, hQ, hDP, hDQ, hQI, hL, hC] at res
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h g).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18⟩ := hp
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, a0])
  simp only [ep]
  rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a9, a11, a13, a14, a15, a17, a18]
  rw [h3, a0] at hn
  rw [a1, a2] at he
  rw [show State.addr (s₂.gpr .r3) = BitVec.setWidth 64 (s₂.gpr .r3) from rfl, hn,
    show State.addr (stackArg s₂ 1) = BitVec.setWidth 64 (stackArg s₂ 1) from rfl, he]

theorem code_ct (v : Proof.Rsa.Arm.CrtImpl) : ConstantTime isa (spec h g).pre (spec h g).pub (decCode h g v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h g hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h g h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h g (ep s₁) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h g h₁, by rw [hep]; exact entered_state h g h₂⟩

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, calling `vg_rsa_private_checked` over `v`, meets the
shared contract (satisfiable, `DecSat.lean`). -/
theorem dec_verified (hsat : ∃ s, (spec h g).pre s) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (decCode h g v) (spec h g) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h g v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h g v, hsat⟩

end VG.Proof.RsaOaep.Arm.Dec
