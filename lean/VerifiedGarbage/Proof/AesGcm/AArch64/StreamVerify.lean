import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. After the entry, `tagLenOk`
checks the tag length (a public value); if §5.2.1.2 does not allow it, 0 is
returned; otherwise `tagIn` copies the received tag to `W`, `finBody 112`
writes the tag at `W + 112`, `cmpSeg` compares its first `tag_len` bytes with
the received ones without a branch, and `verRet` returns 1 or 0
(`ver_run`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes ctxCiph ctxH zeros)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem tagLenOk_le {t : Nat} (h : Spec.Gcm.tagLenOk t = true) : t ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem setWidth_ofNat_bool (b : Bool) :
    (BitVec.ofNat 64 (if b then 1 else 0)).setWidth 32 = if b then 1 else 0 := by
  cases b <;> rfl

/-- The entry of `verify`: `tag_len` in `x28` and `tag` in `x12`. -/
theorem verEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x2 = St)
    (hW : s.gpr .x7 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x7 ++ [mov .x28 .x6, mov .x12 .x5])) s fun s' => Env Ctx St W s.sp s' ∧
      Kept s'.gpr s' ∧ s'.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ s'.gpr .x26 = s.gpr .x3 ∧
      s'.gpr .x27 = s.gpr .x4 ∧ s'.gpr .x28 = s.gpr .x6 ∧ s'.gpr .x12 = s.gpr .x5 ∧
      s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x22₁, x26₁, x27₁, x5₁, x6₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  have r : Regs [.x28, .x12] s₁ s' := by subst hs'; exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  have x28' : s'.gpr .x28 = s₁.gpr .x6 := by subst hs'; simp [gpr_write]
  have x12' : s'.gpr .x12 = s₁.gpr .x5 := by subst hs'; simp [gpr_write]
  exact ⟨he₁.of_regs r, fun _ _ => rfl, by rw [r.others _ (by decide), x22₁],
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by rw [x28', x6₁],
    by rw [x12', x5₁], by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `verPre` gives. -/
theorem lay_of_ver {s : State} (hs : verPre s) :
    Lay (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) ∧ Perm (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s ∧
      rounds (s.gpr .x1) ∧ Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 2560⟩ := by
  simp only [verPre] at hs
  obtain ⟨hrd, hwr, dcs, dcw, -, dsw, dtw, wc, ws, -, ww, hR⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw,
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩, hR,
    covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- The parts of `W` that the entry and `tagIn` write. -/
theorem tag16_inv {Ctx St W : Addr} (L : Lay Ctx St W) :
    ∀ r ∈ [savedR W, ⟨W, 16⟩], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 2560⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact savedR_inv L _ (List.mem_singleton_self _)
  · exact ⟨L.sa, Region.sub_prefix (by decide)⟩

/-- One run of `stream_verify`, for a message `a`, `c` of those lengths. -/
theorem ver_run (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x3 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x4 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        let T := toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2)))
        if Spec.Gcm.tagLenOk (s.gpr .x6).toNat ∧ T.take (s.gpr .x6).toNat =
            bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat then (s'.gpr .x0).setWidth 32 = 1
        else (s'.gpr .x0).setWidth 32 = 0) := by
  have hs' : verPre s := hs
  obtain ⟨L, perm, hR, tR, dtw⟩ := lay_of_ver hs'
  generalize hT : toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
      [ofBytes (lensBlock a.length c.length)] ^^^
      ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2))) = T
  generalize htl : (s.gpr .x6).toNat = tl at tR dtw ⊢
  have htl' : tl < 2 ^ 64 := htl ▸ (s.gpr .x6).isLt
  -- The entry.
  refine WP.seq (WP.mono (verEntry_ok rfl rfl rfl perm)
    fun s₂ ⟨he₂, hk₂, x22₂, x26₂, x27₂, x28₂, x12₂, m₂, rd₂, wr₂⟩ => ?_)
  have x28₂' : s₂.gpr .x28 = BitVec.ofNat 64 tl := by rw [x28₂, ← htl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have fsv : Frame [savedR (s.gpr .x7)] s.mem s₂.mem := by rw [m₂]; exact savedMem_frame _ _ _
  refine WP.seq (WP.mono (tagLenOk_ok s₂ x28₂' htl') fun s₃ ⟨x9₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have sv₃ : SavedAt s₃.mem (s.gpr .x7) s := by
    have := savedAt_save s.mem (s.gpr .x7) s
    rwa [← m₂, ← m₃] at this
  have ev : isa.eval (.zero .x .x9) s₃ =
      some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp s₄ ∧
      SavedAt s₄.mem (s.gpr .x7) s ∧
      (Absorbed s.mem (s.gpr .x2 + BitVec.ofNat 64 16) (s.gpr .x2 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        if Spec.Gcm.tagLenOk tl ∧ T.take tl = bytesAt s.mem (s.gpr .x5) tl then (s₄.gpr .x0).setWidth 32 = 1
        else (s₄.gpr .x0).setWidth 32 = 0))
    (WP.ite _ ev (fun ht => ?_) (fun hf => ?_)) fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.run ⟨_, by arun [], rfl⟩ fun s₄ hs₄ => ?_
    subst hs₄
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, sv₃, fun _ => ?_⟩
    rw [ite_eq_right (by simp [hok])]
    simp [gpr_write]
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := tagLenOk_le hok
    have x12₃ : s₃.gpr .x12 = s.gpr .x5 := by rw [r₃.others _ (by decide), x12₂]
    have x28₃ : s₃.gpr .x28 = BitVec.ofNat 64 tl := by rw [r₃.others _ (by decide), x28₂']
    refine WP.seq (WP.mono (tagIn_ok he₃.x19 x12₃ x28₃ hle (by rw [r₃.rd, r₃.wr, rd₂, wr₂]; exact tR)
      he₃.perm.w (dtw.sub_right (Region.sub_prefix (by decide))))
      fun s₄ ⟨in₄, f₄, og₄, sp₄, rd₄, wr₄⟩ => ?_)
    have he₄ : Env (s.gpr .x0) (s.gpr .x2) (s.gpr .x7) s.sp s₄ := he₃.keep (fun r hr => og₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
    have hk₄ : Kept s₃.gpr s₄ := Kept.of_others (fun _ _ => rfl) og₄
    have F₄ : Frame [savedR (s.gpr .x7), ⟨s.gpr .x7, 16⟩] s.mem s₄.mem :=
      (fsv.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩).trans
        (by rw [← m₃]; exact f₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp,
          fun _ h => h⟩)
    obtain ⟨hc₄, hj₄, hH₄, hA₄⟩ := fin_inv L (tag16_inv L) F₄ hR (x := ghashInput a c)
    have x22₄ : s₄.gpr .x22 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [hk₄ .x22 (by decide), r₃.others _ (by decide), x22₂]
    have x26₄ : s₄.gpr .x26 = BitVec.ofNat 64 a.length := by
      rw [hk₄ .x26 (by decide), r₃.others _ (by decide), x26₂, h3]
    have x27₄ : s₄.gpr .x27 = BitVec.ofNat 64 c.length := by
      rw [hk₄ .x27 (by decide), r₃.others _ (by decide), x27₂, h4]
    refine WP.seq (WP.mono (finBody_ok L v (.inr rfl) (a := a) (c := c) (H := ctxH s.mem (s.gpr .x0)) he₄ hk₄
      x22₄ hR x26₄ x27₄ hc hH₄) fun s₅ ⟨he₅, hk₅, f₅, out₅⟩ => ?_)
    have x28₅ : s₅.gpr .x28 = BitVec.ofNat 64 tl := by rw [hk₅ .x28 (by decide), x28₃]
    refine WP.seq (WP.mono (cmpSeg_ok L he₅ hk₅ x28₅ hle) fun s₆ ⟨x10₆, he₆, _, _, f₆⟩ => ?_)
    refine WP.mono (verRet_ok
      (b := decide (bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x7) tl))
      (by rw [x10₆]; by_cases hp : bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl =
            bytesAt s₅.mem (s.gpr .x7) tl <;> simp [hp]))
      fun s₇ ⟨x0₇, r₇⟩ =>
        ⟨he₆.of_regs r₇, by
          rw [r₇.mem]
          exact (((sv₃.frame f₄ (saved_tag16 L)).frame f₅ (saved_finFrame L (.inr rfl))).frame f₆ (saved_cmp L)),
          fun ha => ?_⟩
    have hT₅ : bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) 16 = T := by
      rw [out₅ (hA₄ ha), hc₄, hj₄, ← hT]
    have hW₅ : bytesAt s₅.mem (s.gpr .x7) tl = bytesAt s.mem (s.gpr .x5) tl := by
      have dW : ∀ r ∈ finFrame (s.gpr .x2) (s.gpr .x7) 112, (⟨s.gpr .x7, tl⟩ : Region).Disjoint r := by
        intro r hr
        refine Region.Disjoint.sub_left ?_ (Region.sub_prefix hle)
        have ww : ∀ e j, 16 ≤ e → e + j ≤ 2560 →
            (⟨s.gpr .x7, 16⟩ : Region).Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 e, j⟩ := fun e j h₁ h₂ => by
          simpa using L.w_w (a := 0) (n := 16) (d := e) (k := j) (.inl h₁) (by decide) h₂
        rcases List.mem_append.mp hr with hr | hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact (L.sa.sub_left (Lay.stSub (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact (L.sa.sub_left (Region.sub_prefix (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
      rw [bytesAt_frame f₅ dW (by omega), in₄, m₃]
      refine bytesAt_frame fsv (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact dtw.sub_right (Lay.wSub (by decide))
    have hb : (bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x7) tl) ↔
        T.take tl = bytesAt s.mem (s.gpr .x5) tl := by
      rw [← bytesAt_take _ _ hle, hT₅, hW₅]
    by_cases hp : T.take tl = bytesAt s.mem (s.gpr .x5) tl
    · rw [ite_eq_left ⟨hok, hp⟩]
      have hb' := hb.mpr hp
      simp only [hb', decide_true, ite_true] at x0₇
      rw [x0₇]; rfl
    · rw [ite_eq_right (fun h => hp h.2)]
      have hb' : ¬ (bytesAt s₅.mem (s.gpr .x7 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x7) tl) :=
        fun h => hp (hb.mp h)
      simp only [hb', decide_false, Bool.false_eq_true, ite_false] at x0₇
      rw [x0₇]; rfl
  refine WP.mono (exit_ok he₄.x19 he₄.sp (covers_left he₄.perm.w) sv₄) fun s' ⟨ga, _, hx0, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hx0]
  exact post₄ ha

theorem streamVerify_wp (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧ streamVerifyAArch64.post s s' := by
  have h3 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x4 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x4).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x4).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x4).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat
  let h := ctxH s.mem (s.gpr .x0)
  let tl := (s.gpr .x6).toNat
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x2) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x3 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x4).toNat = i.2.2.length)
    (Q := fun i s' =>
      if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2).take tl = bytesAt s.mem (s.gpr .x5) tl then
        (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0)
    (ver_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x4).toNat = c.length := hc
  have hl : s.gpr .x3 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x4 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (ver_run v hs hl h4c (hc ▸ (s.gpr .x4).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have ht : Spec.Gcm.fullTag ciph h iv a c =
      toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
        [ofBytes (lensBlock a.length c.length)] ^^^
        ciphOf s.mem (s.gpr .x0) (s.gpr .x1).toNat (blockAt s.mem (s.gpr .x2))) := by
    rw [Proof.Gcm.fullTag_eq, hj]; rfl
  show if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h iv a c).take tl = _ then _ else _
  rw [ht]
  exact hout habs

end VG.Proof.AesGcm.AArch64
