module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Seal
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Fn

/-!
# AES-GCM-SIV on PPC64LE: `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, the
received tag copied to `W` (`recv`), the keys, counter mode on the data from
it, POLYVAL of the result and the tag input, its tag at `W + 240`, the
comparison, the mask and `restore` (`open_wp`), computing `decryptWith`
(RFC 8452 §5) of the arguments, without a branch on the comparison.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Spec.Aes (bytesAt)
open VG.PPC64LE.Spill (Saved)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesCcm.PPC64LE (wp_mv)

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

theorem setWidth_ind (P : Prop) [Decidable P] :
    (BitVec.ofNat 64 (if P then 1 else 0)).setWidth 32 = if P then 1 else 0 := by
  split <;> rfl

/-- A buffer missing `W` and the data misses what counter mode writes. -/
theorem buf_cryR {c : Cx} {P : Addr} {len : Nat} (hw : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3824⟩)
    (hd : (⟨P, len⟩ : Region).Disjoint ⟨c.D, c.n⟩) : ∀ r ∈ cryR c.W c.D c.n, (⟨P, len⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hd

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem open_wp' (hti : TagInputEq) {c : Cx} {s : State} (Ar : Args c s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧
      openOut (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
        (bytesAt s.mem c.N 12) (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) (bytesAt s.mem c.T 16))
        (s'.gpr .r3) (bytesAt s'.mem c.D c.n) c.n := by
  have L := Ar.lay
  have hRb := L.rb
  have hn := L.n_lt
  have hal := L.al_lt
  unfold «open»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  -- The received tag, copied to `W`.
  refine WP.seq (WP.mono (recv_wp En.env) fun s₂ ⟨pk₂, hm₂⟩ => ?_)
  have E₂ := En.env.of_pk pk₂
  have fR : Frame [⟨c.W + BitVec.ofNat 64 0, 16⟩] s₁.mem s₂.mem := by
    rw [hm₂, BitVec.add_zero]; exact copy2Mem_frame _ _ _
  have fR' : Frame (wRs c.W [(0, 16)]) s₁.mem s₂.mem := fR
  -- The keys.
  refine WP.seq (WP.mono (keys_wp L E₂) fun s₃ Ky => ?_)
  have E₃ := E₂.of_pk Ky.pk
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_wp L E₃) fun s₄ Cr => ?_)
  have E₄ := E₃.of_pk Cr.pk
  have fK := Ky.frame
  rw [keyR_eq] at fK
  have dC : ∀ {d : Nat}, d + 16 ≤ 96 → ∀ r ∈ cryR c.W c.D c.n, (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl hd) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.d_w' (by omega)).symm
  have a₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16 = bytesAt s₃.mem (c.W + BitVec.ofNat 64 16) 16 :=
    bytesAt_keep Cr.frame (dC (by decide)) (by decide)
  have hG₄ : Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₄.mem (c.W + BitVec.ofNat 64 16) 16)) := by
    rw [blockAt_frame Cr.frame (dC (by decide)), Ky.hkey, a₄]
  have hY₄ : Spec.Gcm.blockAt s₄.mem (c.W + BitVec.ofNat 64 80) = 0 := by
    rw [blockAt_frame Cr.frame (dC (by decide)), Ky.acc]
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_wp L E₄ hG₄ hY₄) fun s₅ Po => ?_)
  have E₅ := E₄.of_pk Po.pk
  -- Its tag at `W + 240`.
  refine WP.seq (WP.mono (tag_wp L E₅ (o := 240) (by decide)) fun s₆ Tg => ?_)
  have E₆ := E₅.of_pk Tg.pk
  -- The comparison.
  refine WP.seq (WP.mono (cmp_wp E₆) fun s₇ ⟨pk₇, hm₇, r25₇⟩ => ?_)
  have E₇ := E₆.of_pk pk₇
  -- The mask.
  refine WP.seq (WP.mono (mask_wp L E₇ r25₇) fun s₈ ⟨pk₈, r25₈, hm₈⟩ => ?_)
  have E₈ := E₇.of_pk pk₈
  have fP := Po.frame
  have fT := Tg.frame
  rw [polyR_eq] at fP
  rw [tagR_eq] at fT
  have fM : Frame [⟨c.D, c.n⟩] s₇.mem s₈.mem := by
    rw [hm₈]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [List.length_map, Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)
  have f₈ : Frame (mutR c) s₁.mem s₈.mem :=
    (((((fR'.sub (wRs_mut (by decide))).trans (fK.sub (wRs_mut (by decide)))).trans
      (Cr.frame.sub (cryR_mut c))).trans (fP.sub (wRs_mut (by decide)))).trans
      (hm₇ ▸ fT.sub (wRs_mut (by decide)))).trans (fM.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_data)
  have pk₁₈ : PK s₁ s₈ := pk₂.trans (Ky.pk.trans (Cr.pk.trans (Po.pk.trans (Tg.pk.trans (pk₇.trans pk₈)))))
  -- The result, and `restore`.
  refine WP.block_append (wp_mv fun s₉ u₉ => WP.block_nil ?_)
  have sv₉ : Saved c.W (saveG s) savedL s₉.mem := by rw [u₉.mem]; exact saved_mut L f₈ En.saved
  have pk₁₉ : PK s₁ s₉ := pk₁₈.trans (PK.ofUpd u₉)
  refine WP.mono (exit_wp (E₈.of_pk (PK.ofUpd u₉)) sv₉ (by rw [pk₁₉.sp, En.sp])
    (fun r hr => by rw [pk₁₉.gpr r (other_keep r hr), En.others r hr])) fun s' ⟨abi, hm, hr3⟩ => ⟨abi, ?_⟩
  -- What the pieces read.
  have hK₁ : Spec.GcmSiv.ctxCiph s₂.mem c.K c.R = Spec.GcmSiv.ctxCiph s.mem c.K c.R := by
    rw [ciph_keep fR' (buf_keep L.k_w (by decide)) hRb]
    unfold Spec.GcmSiv.ctxCiph
    rw [entry_buf En.frame (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega)]
  have n₂ : bytesAt s₂.mem c.N 12 = bytesAt s.mem c.N 12 := by
    rw [bytesAt_keep fR' (buf_keep L.n_w (by decide)) (by decide), entry_buf En.frame L.n_w (by decide)]
  have n₄ : bytesAt s₄.mem c.N 12 = bytesAt s.mem c.N 12 := by
    rw [bytesAt_keep Cr.frame (buf_cryR L.n_w L.n_d) (by decide),
      bytesAt_keep fK (buf_keep L.n_w (by decide)) (by decide), n₂]
  have a₄' : bytesAt s₄.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [bytesAt_keep Cr.frame (buf_cryR L.a_w L.a_d) (by omega),
      bytesAt_keep fK (buf_keep L.a_w (by decide)) (by omega),
      bytesAt_keep fR' (buf_keep L.a_w (by decide)) (by omega), entry_buf En.frame L.a_w (by omega)]
  have d₃ : bytesAt s₃.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [bytesAt_keep fK (buf_keep L.d_w (by decide)) (by omega),
      bytesAt_keep fR' (buf_keep L.d_w (by decide)) (by omega), entry_buf En.frame L.d_w (by omega)]
  have tag₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s.mem c.T 16 := by
    rw [bytesAt_keep fK (w_keep L (by decide) (by decide)) (by decide), BitVec.add_zero, hm₂, copy2Mem_bytes,
      entry_buf En.frame L.t_w (by decide)]
  have tag₆ : bytesAt s₆.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s.mem c.T 16 := by
    rw [bytesAt_keep fT (w_keep L (by decide) (by decide)) (by decide),
      bytesAt_keep fP (w_keep L (by decide) (by decide)) (by decide),
      bytesAt_keep Cr.frame (dC (by decide)) (by decide), tag₃]
  rw [BitVec.add_zero] at tag₃ tag₆
  have ci₅ : Spec.GcmSiv.ctxCiph s₅.mem (c.W + BitVec.ofNat 64 256) c.R =
      Spec.GcmSiv.ctxCiph s₃.mem (c.W + BitVec.ofNat 64 256) c.R := by
    rw [ciph_keep fP (w_keep L (by decide) (by decide)) hRb, ciph_cryR L Cr.frame]
  have d₇ : bytesAt s₇.mem c.D c.n = bytesAt s₄.mem c.D c.n := by
    rw [hm₇, bytesAt_keep fT (buf_keep L.d_w (by decide)) (by omega),
      bytesAt_keep fP (buf_keep L.d_w (by decide)) (by omega)]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₂] at au ci
  have pt₄ := Cr.data
  rw [tag₃, d₃, ci] at pt₄
  have po := Po.out
  rw [a₄, ← au, n₄, a₄', pt₄] at po
  have tg := Tg.out
  rw [ci₅, ci, po] at tg
  have r3' : s'.gpr .r3 = s₇.gpr .r25 := by rw [hr3, u₉.gpr, r25₈]
  rw [r25₇, tag₆, tg] at r3'
  have md : bytesAt s'.mem c.D c.n = (bytesAt s₇.mem c.D c.n).map fun b =>
      if bytesAt s.mem c.T 16 = Spec.GcmSiv.ctxCiph s₅.mem (c.W + BitVec.ofNat 64 256) c.R
        (bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) 16) then b else 0 := by
    have e := Proof.AesGcm.PPC64LE.bytesAt_writeBytes_self s₇.mem c.D
      ((bytesAt s₇.mem c.D c.n).map fun b => if bytesAt s₆.mem c.W 16 =
        bytesAt s₆.mem (c.W + BitVec.ofNat 64 240) 16 then b else 0)
      (by rw [List.length_map, Proof.Cmac.bytesAt_length]; omega)
    rw [List.length_map, Proof.Cmac.bytesAt_length] at e
    rw [hm, u₉.mem, hm₈, e, tag₆, Tg.out]
  rw [d₇, pt₄, ci₅, ci, po] at md
  rw [decrypt_eq hti]
  simp only
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem c.K c.R) (Spec.GcmSiv.keyLen c.R)
    (bytesAt s.mem c.N 12) = dk at md r3'
  have hlen : (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem c.T 16))
      (bytesAt s.mem c.D c.n)).length = c.n := by
    rw [GcmSiv.length_ctr (Spec.GcmSiv.aes dk.2) (fun y => GcmSiv.aesWith_length _ _ y), Proof.Cmac.bytesAt_length]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem c.N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem c.T 16))
        (bytesAt s.mem c.D c.n)) (bytesAt s.mem c.A c.al)) = bytesAt s.mem c.T 16
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have hc' := hc.symm
    refine ⟨?_, ?_⟩
    · rw [r3', ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl
    · rw [md]; simp only [ite_eq_left_of_eq_true _ _ (eq_true hc'), List.map_id']
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have hc' : ¬bytesAt s.mem c.T 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem c.N 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem c.T 16))
          (bytesAt s.mem c.D c.n)) (bytesAt s.mem c.A c.al)) := fun h => hc h.symm
    refine ⟨?_, ?_⟩
    · rw [r3', ite_eq_right_of_eq_false _ _ (eq_false hc')]; rfl
    · rw [md]; simp only [ite_eq_right_of_eq_false _ _ (eq_false hc'), List.map_const', hlen, Spec.GcmSiv.zeros]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (hti : TagInputEq) {s : State} (h : openPPC64LE.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openPPC64LE.post s s' := by
  have A := args_of_open h
  refine WP.mono (open_wp' hti A) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [openPPC64LE]
  simpa only [cxOf] using hp

end VG.Proof.AesGcmSiv.PPC64LE
