import VerifiedGarbage.Proof.AesGcmSiv.Arm.Seal

/-!
# AES-GCM-SIV on ARMv7: `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 176`, the comparison, the mask and the restore
compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.Arm (SavedAt savedR)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

theorem ite_ofNat (c : Prop) [Decidable c] :
    (if c then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (if c then 1 else 0) := by
  split <;> rfl

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (hti : TagInputEq) {s : State} (h : openPre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' := by
  obtain ⟨L, P⟩ := args_of_open h
  have hRb := L.rounds_le
  have hn := L.n_lt
  have A₀ := args_of s
  refine WP.seq (WP.mono (entry_ok L P) fun s₀ En₀ => ?_)
  have A₀' : Args (prmOf s) s₀.mem := A₀.frame L En₀.frame (by disj_tac L)
  -- The received tag, copied to `W`.
  obtain ⟨s₁, run₁, fR, hR₁, ho₁, sp₁, rd₁, wr₁⟩ := recv_ok L En₀.env A₀'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have fR' : Frame [⟨State.addr (prmOf s).W + BitVec.ofNat 64 0, 16⟩] s₀.mem s₁.mem := by
    rw [BitVec.add_zero]; exact fR
  have E₁ : Env (prmOf s) s₁ := En₀.env.of_others ho₁ sp₁ rd₁ wr₁
  have sv₁ : SavedAt s₁.mem (prmOf s).W s := En₀.saved.frame fR' (by disj_tac L)
  have f₁ : Frame [savedR (prmOf s).W, ⟨State.addr (prmOf s).W + BitVec.ofNat 64 0, 16⟩] s.mem s₁.mem :=
    (En₀.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have A₁ : Args (prmOf s) s₁.mem := A₀'.frame L fR' (by disj_tac L)
  have hT₁ : bytesAt s₁.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [BitVec.add_zero, hR₁, bytesAt_keep En₀.frame (by disj_tac L) (by decide)]
  -- The keys.
  refine WP.seq (WP.mono (keys_ok L E₁) fun s₂ Ky => ?_)
  have A₂ : Args (prmOf s) s₂.mem := A₁.frame L Ky.frame (by disj_tac L)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok L Ky.env A₂) fun s₃ Cr => ?_)
  have A₃ : Args (prmOf s) s₃.mem := A₂.frame L Cr.frame (by disj_tac L)
  have a₃ : bytesAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16 =
      bytesAt s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16 :=
    bytesAt_keep Cr.frame (by disj_tac L) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.hkey, a₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem (State.addr (prmOf s).W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.Arm.blockAt_frame Cr.frame (by disj_tac L), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok L Cr.env A₃ hG₃ hY₃) fun s₄ Po => ?_)
  have A₄ : Args (prmOf s) s₄.mem := A₃.frame L Po.frame (by disj_tac L)
  -- Its tag at `W + 176`.
  refine WP.seq (WP.mono (tag_ok L Po.env (o := 176) (by decide)) fun s₅ Tg => ?_)
  have A₅ : Args (prmOf s) s₅.mem := A₄.frame L Tg.frame (by disj_tac L)
  -- The comparison.
  obtain ⟨s₆, run₆, r0₆, ho₆, hm₆, sp₆, rd₆, wr₆⟩ := cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env (prmOf s) s₆ := Tg.env.of_others ho₆ sp₆ rd₆ wr₆
  rw [ite_ofNat] at r0₆
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ (hm₆ ▸ A₅) r0₆) fun s₇ Mk => ?_)
  -- The restore.
  have sv₇ : SavedAt s₇.mem (prmOf s).W s := by
    have := ((((sv₁.frame Ky.frame (by disj_tac L)).frame Cr.frame (by disj_tac L)).frame Po.frame
      (by disj_tac L)).frame Tg.frame (by disj_tac L))
    rw [← hm₆] at this
    exact this.frame Mk.frame (by disj_tac L)
  refine WP.mono (exit_ok L Mk.env rfl sv₇) fun s' ⟨ga, hm, hr0⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem (State.addr (prmOf s).K) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R :=
    ciph_keep f₁ (by disj_tac L) hRb
  have n₁ : bytesAt s₁.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 :=
    bytesAt_keep f₁ (by disj_tac L) (by decide)
  have n₃ : bytesAt s₃.mem (State.addr (prmOf s).N) 12 = bytesAt s.mem (State.addr (prmOf s).N) 12 := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by decide), bytesAt_keep Ky.frame (by disj_tac L) (by decide), n₁]
  have a₃' : bytesAt s₃.mem (State.addr (prmOf s).A) (prmOf s).al =
      bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al := by
    rw [bytesAt_keep Cr.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep Ky.frame (by disj_tac L) (by have := L.al_lt; omega),
      bytesAt_keep f₁ (by disj_tac L) (by have := L.al_lt; omega)]
  have d₂ : bytesAt s₂.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by omega), bytesAt_keep f₁ (by disj_tac L) (by omega)]
  have tag₂ : bytesAt s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [bytesAt_keep Ky.frame (by disj_tac L) (by decide), hT₁]
  have tag₅ : bytesAt s₅.mem (State.addr (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (State.addr (prmOf s).T) 16 := by
    rw [bytesAt_keep Tg.frame (by disj_tac L) (by decide), bytesAt_keep Po.frame (by disj_tac L) (by decide),
      bytesAt_keep Cr.frame (by disj_tac L) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (State.addr (prmOf s).W + BitVec.ofNat 64 192) (prmOf s).R := by
    rw [ciph_keep Po.frame (by disj_tac L) hRb, ciph_cryR L Cr.frame]
  have d₆ : bytesAt s₆.mem (State.addr (prmOf s).D) (prmOf s).n = bytesAt s₃.mem (State.addr (prmOf s).D) (prmOf s).n := by
    rw [hm₆, bytesAt_keep Tg.frame (by disj_tac L) (by omega), bytesAt_keep Po.frame (by disj_tac L) (by omega)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.data
  rw [hm₆, tg, tag₅] at md
  rw [← hm₆, d₆, pt₃] at md
  have ax : s'.gpr .r0 = s₆.gpr .r0 := by rw [hr0, Mk.r0]
  rw [r0₆, tg, tag₅] at ax
  show openPost (openResult s) s' (State.addr (prmOf s).D) (prmOf s).n
  have hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
            (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) =
          bytesAt s.mem (State.addr (prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
          (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (State.addr (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (State.addr (prmOf s).N) 12) = dk at md ax hdec
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (State.addr (prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
        (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) =
      bytesAt s.mem (State.addr (prmOf s).T) 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax]; simp only [hc, ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc, ↓reduceIte]
  · have hc' : ¬bytesAt s.mem (State.addr (prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (State.addr (prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (State.addr (prmOf s).T) 16))
          (bytesAt s.mem (State.addr (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (State.addr (prmOf s).A) (prmOf s).al)) :=
      Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax]; simp only [hc', ↓reduceIte]; rfl
    · rw [hm, md]; simp only [hc', ↓reduceIte]

end VG.Proof.AesGcmSiv.Arm
