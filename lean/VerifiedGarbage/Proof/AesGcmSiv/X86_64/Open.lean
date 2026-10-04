import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Seal

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 128`, the comparison, the mask
and the restore compute `decryptWith` (RFC 8452 §5) of the arguments
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

theorem w0_keyR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ keyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 16) (k := 128) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 248) (k := 3568) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_cryR {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    ∀ r ∈ cryR W SP D n, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact (hD.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_polyR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ polyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 80) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1512) (k := 256) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_tagR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ tagR W SP 128, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 112) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem open_wp' (v : GcmImpl) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧
      openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, E₀, S₀, sv₀, f₀, rd₀, wr₀⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  have f₀' : Frame (entryR W :: mutR W SP D n) s.mem s₀.mem :=
    f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  -- The received tag, copied to `W`.
  have hTa : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₀, wr₀]; exact h
  obtain ⟨s₁, run₁, fR, hR₁, hgR, rdR, wrR⟩ := recv_ok E₀ (by rw [argT_kept f₀' Ar.argsW Ar.argsD, hT]) hTa
    ((Tb.buf (s := s) hTr).of_eq rd₀ wr₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E₀.of_saved hgR rdR wrR
  have fR' : Frame (mutR W SP D n) s₀.mem s₁.mem := fR.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, by simp, Region.sub_prefix (by decide)⟩
  have S₁ := slots_mut L Ar.data.w fR' S₀
  have rd₁ : s₁.rd = s.rd := by rw [rdR, rd₀]
  have wr₁ : s₁.wr = s.wr := by rw [wrR, wr₀]
  have f₁ : Frame (entryR W :: mutR W SP D n) s.mem s₁.mem :=
    f₀'.trans (fR'.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have f₀₁ : Frame [entryR W, ⟨W, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨W, 16⟩, by simp, fun _ h => h⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Region.sub_prefix (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Region.sub_prefix (by decide))) hRb
  have hT₁ : bytesAt s₁.mem W 16 = bytesAt s.mem T 16 := by
    rw [hR₁]; exact tag_kept Tb f₀'
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  have S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v L Ar.rounds Ky.env S₂ (bD₁.of_eq Ky.rd Ky.wr)
    (by rw [Ky.wr, wr₁]; exact Ar.dw)) fun s₃ Cr => ?_)
  have S₃ := S₂.of_frame Cr.frame (slots_cryR L Ar.data)
  have dK : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 96 → ∀ q ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
      · exact (Ar.data.w.sub_right (Lay.wSub (by omega))).symm
  have hA₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.hkey, hA₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.acc]
  have nA : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩ →
      bytesAt s₃.mem P len = bytesAt s.mem P len := fun hP hPD => by
    rw [Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.stk.symm
        · exact hPD) (by have := hP.lt; omega),
      buf_mutW (hP.of_eq rd₁ wr₁) fK, hent hP]
  -- POLYVAL of the plaintext and the tag input.
  have r₃ : s₃.rd = s₁.rd := by rw [Cr.rd, Ky.rd]
  have w₃ : s₃.wr = s₁.wr := by rw [Cr.wr, Ky.wr]
  refine WP.seq (WP.mono (polyval_ok v L Cr.env S₃ (bA₁.of_eq r₃ w₃) (bD₁.of_eq r₃ w₃) (bN₁.of_eq r₃ w₃) hG₃ hY₃)
    fun s₄ Po => ?_)
  have S₄ := slots_mut L Ar.data.w ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n)) S₃
  -- Its tag at `W + 128`.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds Po.env S₄ (o := 128) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, hm₆, hg₆, hrd₆, hwr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env K W SP s₆ := Tg.env.of_saved hg₆ hrd₆ hwr₆
  have fO : Frame [wO W] s₅.mem s₆.mem := by
    rw [hm₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have S₅ := slots_mut L Ar.data.w ((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)) S₄
  have S₆ := S₅.of_frame fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
  have r₅ : s₅.rd = s₁.rd := by rw [Tg.rd, Po.rd, r₃]
  have w₅ : s₅.wr = s₁.wr := by rw [Tg.wr, Po.wr, w₃]
  have hok : s₆.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16 = bytesAt s₅.mem W 16 then 1#64 else 0#64 := by
    rw [hm₆, Mem.readW_writeW_self64]
    by_cases hc : bytesAt s₅.mem W 16 = bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Ne.symm hc, ↓reduceIte]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ S₆ (bD₁.of_eq (by rw [hrd₆, r₅]) (by rw [hwr₆, w₅]))
    (by rw [hwr₆, w₅, wr₁]; exact Ar.dw) hok) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  have h15₇ := Mk.env.r15
  have rO := Mk.env.perm.wR (show 192 + 8 ≤ 3816 by decide)
  obtain ⟨s₈, run₈, hax₈, hm₈, hg₈, hrd₈, hwr₈⟩ : ∃ s₈ : State, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₇ =
      some s₈ ∧ s₈.gpr .rax = s₇.mem.readW (W + BitVec.ofNat 64 192) 64 ∧ s₈.mem = s₇.mem ∧
      (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by srun [h15₇, rO], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₈ : Env K W SP s₈ := Mk.env.keep (fun r hr => hg₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₈ hwr₈
  have fall : Frame (mutR W SP D n) s₁.mem s₇.mem :=
    ((((fK.sub (mutW_mut W SP D n)).trans (Cr.frame.sub (cryR_mut W SP D n))).trans
      ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n))).trans
      (((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)).trans
        (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩))).trans
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ :=
    restore_ok E₈ (by rw [hm₈]; exact saved_mut L Ar.data.w (fR'.trans fall) sv₀)
  refine WP.of_runBlock ⟨s₉, by rw [runBlock_append, run₈]; exact run₉, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, 144) (by decide)
    · exact hg₉ (.rbp, 152) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, 160) (by decide)
    · exact hg₉ (.r13, 168) (by decide)
    · exact hg₉ (.r14, 176) (by decide)
    · exact hg₉ (.r15, 184) (by decide)
  · have fall' : Frame (entryR W :: mutR W SP D n) s.mem s₇.mem :=
      f₁.trans (fall.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, hm₈, hsp]
    exact fall'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have tag₂ : bytesAt s₂.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Ky.frame (w0_keyR L) (by decide), hT₁]
    have tag₅ : bytesAt s₅.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Tg.frame (w0_tagR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame (w0_polyR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (w0_cryR L Ar.data.w) (by decide), tag₂]
    have ct₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := by
      rw [ctxCiph_frame Po.frame (key_polyR L) hRb, ctxCiph_frame Cr.frame (key_cryR L Ar.data) hRb]
    have pt₃ := Cr.data
    rw [tag₂, ct₂, ci] at pt₃
    have po := Po.out
    rw [hA₃, ← au, nA Ar.nonce Ar.nd, nA Ar.aad Ar.ad, pt₃] at po
    have tg := Tg.out
    rw [ci₄, ci, po] at tg
    have dD : ∀ q ∈ tagR W SP 128, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    have dP : ∀ q ∈ polyR W SP, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    have d₆ : bytesAt s₆.mem D n = bytesAt s₃.mem D n := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame fO (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by have := Ar.data.lt; omega),
        Proof.AesGcm.X86_64.bytesAt_frame Tg.frame dD (by have := Ar.data.lt; omega),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame dP (by have := Ar.data.lt; omega)]
    have ax : s₉.gpr .rax = s₆.mem.readW (W + BitVec.ofNat 64 192) 64 := by
      rw [hax₉, hax₈, Mk.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
        (by decide)]
    have md := Mk.data
    have ax' := ax.trans hok
    rw [tg, tag₅] at ax'
    rw [tg, tag₅, d₆, pt₃] at md
    have hdec : Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16) =
        let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        if Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
            (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
            (bytesAt s.mem A al)) = bytesAt s.mem T 16 then
          some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
        else none := by
      unfold Spec.GcmSiv.decryptWith
      rw [← Prod.mk.eta (p := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R)
        (bytesAt s.mem N 12))]
    simp only at hdec
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
      at md ax' hdec
    rw [hdec]
    refine Or.elim (Classical.em (Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
      (bytesAt s.mem A al)) = bytesAt s.mem T 16)) (fun hc => ?_) (fun hc => ?_)
    · refine openPost_some (by rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]
    · refine openPost_none (by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) {s : State} (h : openPre s) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact open_wp' v Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64
