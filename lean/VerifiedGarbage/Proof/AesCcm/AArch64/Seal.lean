import VerifiedGarbage.Proof.AesCcm.AArch64.Crypt

/-!
# AES-CCM on AArch64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is `entry`, `Ctr₀`
(`ctrs`), the MAC of the payload (`mac 0`), encrypted at `W` (`tag 0`),
counter mode over the data (`ctr`), the tag copied to `tag`, whose address
the entry keeps in `W` (`loadTag_ok`, `tagOut_ok`), and `restore`
(`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (SavedAt exit_ok covers_left LoopPre copyLoop_ok loopRegs Others)
open VG.Impl.AesGcm.AArch64 (mov copyLoop)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher)

/-- The entry keeps a buffer missing `W`. -/
theorem entry_buf {c : Cx} {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) {P : Addr} {len : Nat}
    (hP : Buf c s P len) : bytesAt s₁.mem P len = bytesAt s.mem P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega_arith)

theorem entry_ciph {c : Cx} (L : Lay c) {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) :
    Spec.Ccm.ctxCiph s₁.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega_arith)]

theorem frame_ctrs_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_lo (by decide)

theorem tagR_mut (c : Cx) {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.W + BitVec.ofNat 64 y, 16⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_lo (by omega_arith)
  · exact sub_hi (by decide) (by decide)

/-- The bytes of `W` below 48, kept by `ctrs`. -/
theorem ctrs_keeps {c : Cx} (L : Lay c) {d k : Nat} (h : d + k ≤ 48 ∨ (64 ≤ d ∧ d + k ≤ 2560)) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region)], (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  rcases h with h | h
  · exact L.w_w (.inl h) (by omega_arith) (by decide)
  · exact L.w_w (.inr h.1) (by omega_arith) (by decide)

/-- `Ctr₀` is kept by the MAC's pieces. -/
theorem macR_c0 {c : Cx} (L : Lay c) {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∀ r ∈ macR c.W y, (⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- `Ctr₀` is kept by `tag`. -/
theorem tagR_c0 {c : Cx} (L : Lay c) {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.W + BitVec.ofNat 64 y, 16⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

/-- The data, kept by the pieces before `ctr`. -/
theorem d_lo {c : Cx} (L : Lay c) {rs : List Region} (hs : ∀ r ∈ rs, ∃ r' ∈ [wLo c.W, wHi c.W], Region.Sub r r') :
    ∀ r ∈ rs, (⟨c.D, c.n⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨r', hr', hsub⟩ := hs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact (L.d_w.sub_right (Region.sub_prefix (by decide))).sub_right hsub
  · exact (L.d_w' (by decide)).sub_right hsub

/-- The address of the tag loaded from its slot into `r`. -/
theorem loadTag_ok {c : Cx} {s : State} (E : Env c s) (S : Slots c s.mem) (r : Reg) :
    WP isa (.block [.ldr .x r .x19 tagO]) s fun s₁ =>
      s₁.gpr r = c.T ∧ Others [r] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q := E.perm.wR (show 240 + 8 ≤ 2560 by decide)
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [tagO, E.x19, q], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true]; rw [← S.tag]; rfl
  · simp only [List.mem_singleton] at hr'; simp [gpr_write, hr']

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, in `x11`. -/
theorem tagOut_ok {c : Cx} (L : Lay c) {s : State} (E : Env c s) (hx11 : s.gpr .x11 = c.T)
    (hTw : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa tagOut s fun s' => Env c s' ∧ s'.mem = writeBytes s.mem c.T (bytesAt s.mem c.W c.tl) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x12₁, x13₁, og₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [mov .x12 .x19, mov .x13 .x20] s =
      some s₁ ∧ s₁.gpr .x12 = c.W ∧ s₁.gpr .x13 = BitVec.ofNat 64 c.tl ∧ Others [.x12, .x13] s s₁ ∧
      s₁.sp = s.sp ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, E.x19]
    · simp [gpr_write, E.x20]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env c s₁ := E.others og₁ (by decide) sp₁ rd₁ wr₁
  have x11₁ : s₁.gpr .x11 = c.T := by rw [og₁ .x11 (by decide), hx11]
  have lp : LoopPre s₁ c.W c.T c.tl :=
    ⟨by have := L.t16; omega_arith, by simpa using E₁.perm.wCR (d := 0) (n := c.tl) (by have := L.t16; omega_arith),
      by rw [wr₁]; exact hTw, (L.t_w.sub_right (Region.sub_prefix (by have := L.t16; omega_arith))).symm⟩
  refine WP.mono (copyLoop_ok s₁ x12₁ x11₁ x13₁ (by have := L.t4; omega_arith) lp)
    fun s₂ ⟨hm₂, _, _, og₂, sp₂, rd₂, wr₂⟩ => ⟨E₁.others og₂ (by decide) sp₂ rd₂ wr₂, by rw [hm₂, m₁],
      by rw [sp₂, sp₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} {N : Addr} {s : State} (Ar : Args c N s)
    (hTw : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n)
        (bytesAt s.mem c.A c.al) = (bytesAt s'.mem c.D c.n, bytesAt s'.mem c.T c.tl) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (entry_ok Ar) fun s₁ En => ?_)
  have hN₁ : Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (ctrs_ok L En.env hN₁ En.x2 En.x3) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (mutR c) s₁.mem s₂.mem := f₂.sub (frame_ctrs_mut c)
  have S₂ := En.slots.mut L f₂'
  refine WP.seq (WP.mono (mac_ok v L E₂ S₂ hnl c₂ (.inl rfl)) fun s₃ M => ?_)
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame M.frame (macR_c0 L (.inl rfl)) (by decide), c₂]
  refine WP.seq (WP.mono (tag_ok v.ctr L M.env hnl c₃ (.inl rfl)) fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₄ (tagR_c0 L (.inl rfl)) (by decide), c₃]
  refine WP.seq (WP.mono (ctr_ok v.ctr L E₄ hnl c₄) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₁₃ : Frame (mutR c) s₁.mem s₃.mem := f₂'.trans (M.frame.sub (macR_mut (.inl rfl)))
  have f₁₄ : Frame (mutR c) s₁.mem s₄.mem := f₁₃.trans (f₄.sub (tagR_mut c (.inl rfl)))
  have f₁₅ : Frame (mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (ctrR_mut c))
  have sv₅ : SavedAt s₅.mem c.W s := saved_mut L f₁₅ En.saved
  -- The tag copied to `T`.
  refine WP.seq (WP.mono (loadTag_ok E₅ (En.slots.mut L f₁₅) .x11) fun s₆ ⟨x11₆, og₆, m₆, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ : Env c s₆ := E₅.others og₆ (by decide) sp₆ rd₆ wr₆
  have rw₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, M.wr, wr₂, En.wr]
  refine WP.seq (WP.mono (tagOut_ok L E₆ x11₆ (by rw [rw₆]; exact hTw)) fun s₇ ⟨E₇, m₇, sp₇, rd₇, wr₇⟩ => ?_)
  have hx : (bytesAt s₆.mem c.W c.tl).length = c.tl := length_bytesAt _ _ _
  have f₇ : Frame [⟨c.T, c.tl⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact Proof.AesGcm.AArch64.writeBytes_frame' _ hx
  have sv₇ : SavedAt s₇.mem c.W s := (m₆ ▸ sv₅).frame f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok E₇.x19 (by rw [E₇.sp, Ar.sp]) (covers_left E₇.perm.w) sv₇)
    fun s' ⟨ga, hm, _, _, _⟩ => ⟨ga, ?_⟩
  -- The ciphertext and the tag.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₄, k₁]
  have hd₁ : bytesAt s₁.mem c.D c.n = bytesAt s.mem c.D c.n := entry_buf En.frame (L.bufD Ar.perm)
  have ha₁ : bytesAt s₁.mem c.A c.al = bytesAt s.mem c.A c.al := entry_buf En.frame (L.bufA Ar.perm)
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.n_lt; omega_arith), hd₁]
  have ha₂ : bytesAt s₂.mem c.A c.al = bytesAt s.mem c.A c.al := by rw [aad_mut L f₂', ha₁]
  have hd₄ : bytesAt s₄.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact L.d_w' (by decide)) (by have := L.n_lt; omega_arith),
      buf_macR (L.bufD M.env.perm) (by decide) M.frame, hd₂]
  have w₅ : bytesAt s₅.mem c.W c.tl = bytesAt s₄.mem c.W c.tl :=
    Proof.AesGcm.AArch64.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w0_w (by have := L.t16; omega_arith) (by decide)
      · exact L.w0_w (by have := L.t16; omega_arith) (by decide)
      · exact (L.d_w.sub_right (Region.sub_prefix (by have := L.t16; omega_arith))).symm) (by have := L.t16; omega_arith)
  have e0 : c.W + BitVec.ofNat 64 0 = c.W := BitVec.add_zero c.W
  have M' := M.out
  rw [e0] at h₄ M'
  have hY := congrArg List.length h₄
  rw [length_bytesAt, length_xorFrom] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  have d₇ : bytesAt s₇.mem c.D c.n = bytesAt s₅.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.n_lt; omega_arith), m₆]
  have t₇ : bytesAt s₇.mem c.T c.tl = bytesAt s₅.mem c.W c.tl := by
    have e := Proof.AesCcm.bytesAt_writeBytes_at s₆.mem c.T (o := 0) (n := c.tl) (bytesAt s₆.mem c.W c.tl)
      (by rw [hx]; omega_arith) (by have := L.t16; omega_arith)
    rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hx]), List.append_nil] at e
    rw [m₇, e, m₆]
  refine ⟨?_, ?_⟩
  · rw [hm, d₇, h₅, k₄, hd₄, crypt_eq (hBC _)]
  · rw [hm, t₇, w₅, Proof.AesCcm.bytesAt_prefix s₄.mem c.W L.t16, h₄, k₃,
      take_xorFrom_zero (hBC _) _ hY.symm L.t16, M', k₂, ha₂, hd₂,
      ← mac_eq _ _ (by rw [hnl]; have := L.h13; omega_arith)]

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s : State} (h : sealAArch64.pre s) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  have A := args_of_seal h
  refine WP.mono (seal_wp' v A.1 A.2) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [sealAArch64]
  simpa only [cxOf] using hp

end VG.Proof.AesCcm.AArch64
