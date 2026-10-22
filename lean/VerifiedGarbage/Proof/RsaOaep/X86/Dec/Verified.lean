module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.End
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSAES-OAEP decryption on x86: verified

As on ARMv7 (`Proof/RsaOaep/Arm/DecVerified.lean`): the private-key
operation and the check of `k` (`pa_vp`, `call_vp`, `chk_vp`), then zeros if
`k` is too short (`fail_vp`) or the decoding (`main_vp`): `body_vp`. The body
writes `esp` only through the frames of its calls (`body_noSp`); the frames
around it (`wrap_ok`, `wrap_ct`) and the result as the shared contract states
it: `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, calling `vg_rsa_private_checked` over
`v`, is verified, given a state that meets the contract (`Dec/Sat.lean`):
`dec_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes seqs countLoop zeroLoop clrArgs)

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

theorem vpAssoc (h : VP F (.seq (.seq a b) c) G) : VP F (.seq a (.seq b c)) G :=
  ⟨fun σ s hs => WP.assoc (h.wp σ s hs), RelCT.assoc h.ct⟩

theorem vpAssoc' (h : VP F (.seq a (.seq b c)) G) : VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_assoc' h.ct⟩

/-- A piece of `n` steps, then the rest. -/
theorem VP.cont2 (h : VP F (.seq a b) G) (h₂ : VP G r H) : VP F (.seq a (.seq b r)) H := vpAssoc (h.seq h₂)

theorem VP.cont3 (h : VP F (.seq a (.seq b c)) G) (h₂ : VP G r H) : VP F (.seq a (.seq b (.seq c r))) H :=
  vpAssoc (VP.cont2 (vpAssoc' h) h₂)

theorem VP.cont4 (h : VP F (.seq a (.seq b (.seq c d))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d r)))) H :=
  vpAssoc (VP.cont3 (vpAssoc' h) h₂)

end

variable (h g : OHash)

/-- The decoding, when `k ≥ 2 hLen + 2`. -/
theorem main_vp (P : EP) :
    VP (fun σ s => C2 h.H.D P σ s ∧ isa.eval .b s = some false) (decMain h.H g.H) (Fin h.G g.G P) := by
  show VP _ (.seq (hashLabel h.H 17 oLh) (.seq (.block (seedArgs h.H 4)) (.seq (mgfXor g.H)
    (.seq (.block (dbArgs h.H 4)) (.seq (mgfXor g.H) (.seq (.block (cmpSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.cmpBody) (.seq (.block accPut) (.seq (.block (scanSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.scanBody) (.seq (.block scanEnd) (.seq (.block (clrArgs oBuf 2048))
    (.seq zeroLoop (.seq (.block (tSet h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq shift (.seq (.block okMask)
    (.seq (.block outSet) (.seq (countLoop outBody) (.seq (.block (mlSet h.H)) (.block decRet)))))))))))))))))))))
    _
  exact (lab_vp h P).seq (VP.cont4 (unmask_vp h g P) (VP.cont3 (acc_vp h g P) (VP.cont3 (tscan_vp h g P)
    (buf_vp h g P ((shift_vp h g P).seq ((okMask_vp h g P).seq (VP.cont2 (out_vp h g P) (end_vp h g P))))))))

theorem body_vp (P : EP) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (S P) (decBody h.H g.H (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (Fin h.G g.G P) := by
  show VP _ (.seq (.block (decStart ++ privArgs)) (.seq (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v))
    (.seq (.block (decChk h.H)) (.ite .b decFail (decMain h.H g.H))))) _
  exact (pa_vp P).seq ((call_vp P v).seq ((chk_vp h P).seq (VP.ite
    (fun σ s hs => ⟨decide (P.K < 2 * h.H.D + 2), by simp only [eval, hs.2.2.2.2.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2.2, h₂.2.2.2.2.2]) (fail_vp h g P) (main_vp h g P))))

/-! ## The stack -/

theorem body_noSp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    NoSp (decBody h.H g.H (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) := by
  obtain ⟨-, -, -, p4, -, p6, -, -, -, p10, p11, p12, p13, p14⟩ := h.certs.parts
  have hm := mgfX_noSp g
  have hl := hashLabel_noSp h (j := 17) (o := oLh) (NoSp.of_all (by decide +kernel))
    (NoSp.of_all (by decide +kernel))
  have hc := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  simp only [decBody, decMain, decFail, shift, passOne, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply RsaPss.X86.noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | exact hm | exact hl | exact hc | exact p4 | exact p6 | exact p10 | exact p11 | exact p12 | exact p13
    | exact p14
    | exact NoSp.of_all (by decide +kernel))

/-! ## The entry -/

/-- The code, calling `vg_rsa_private_checked` over `v`. -/
abbrev decCode (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : Prog isa :=
  decrypt h.H g.H (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)

theorem entered_state {s : State} (hs : (spec h.G g.G).pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  have hi := in_of_pre hs
  ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (hs : (spec h.G g.G).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argSlots, argVal, argBytes,
    stackBelow] at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem code_ok (v : Proof.Rsa.X86.PrivChecked.CrtImpl) {s : State} (hs : (spec h.G g.G).pre s) :
    WP isa (decCode h g v) s fun t => abiPreserved s t ∧ (spec h.G g.G).post s t := by
  have hin := in_of_pre hs
  obtain ⟨hsp0, hfit⟩ := spec_sp h g hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hb := (body_vp h g (ep s) v).wp _ _ (entered_state h g hs)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp h g v) hsp hfit (W := (ep s).lay.W)
    (Q := fun r m => Res h.G g.G (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 3392) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 3392) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro) => entered_ro hsp ok hR
    sig_post [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argSlots, argVal, argBytes]
    unfold Res at res
    have hP : pB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat :=
      ro (R := (ep s).PP) (by simp)
    have hQ : qB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat :=
      ro (R := (ep s).QQ) (by simp)
    have hDP : dpB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 11).setWidth 64)
        (arg s 8).toNat := ro (R := (ep s).DP) (by simp)
    have hDQ : dqB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 13).setWidth 64)
        (arg s 10).toNat := ro (R := (ep s).DQ) (by simp)
    have hQI : qiB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 15).setWidth 64)
        (arg s 8).toNat := ro (R := (ep s).QI) (by simp)
    have hL : labB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 17).setWidth 64)
        (arg s 18).toNat := ro (R := (ep s).LAB) (by simp)
    have hC : ctB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 19).setWidth 64)
        (arg s 4).toNat := ro (R := (ep s).CT) (by simp)
    rw [hP, hQ, hDP, hDQ, hQI, hL, hC] at res
    rw [BitVec.setWidth_append_eq_right]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h.G g.G).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argSlots, argVal, argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22⟩ := hp
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.bytesAt_len, a4])
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a17, a18, a19, a21, a22]
  rw [a3, a4] at hn
  rw [a5, a6] at he
  rw [hn, he]

theorem code_ct (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    ConstantTime isa (spec h.G g.G).pre (spec h.G g.G).pub (decCode h g v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h g hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argSlots, argVal, argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp h g v) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h g (ep s₁) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h g h₁, by rw [hep]; exact entered_state h g h₂⟩

theorem code_noSp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : NoSp (decCode h g v) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp h g v)) restore_noSp)

theorem code_sp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : (decCode h g v).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp h g v)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, calling `vg_rsa_private_checked` over `v`, meets the shared
contract (satisfiable, `Dec/Sat.lean`). -/
theorem dec_verified (hsat : ∃ s, (spec h.G g.G).pre s) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (decCode h g v) (spec h.G g.G) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h g v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h g v, hsat⟩

end VG.Proof.RsaOaep.X86.Dec
