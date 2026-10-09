import VerifiedGarbage.Proof.AesCcm.AArch64.Header

/-!
# AES-CCM on AArch64: the MAC (`aadHead y`, `mac y`)

Untrusted: everything here is checked by Lean. `aadHead y` writes the
encoding of the length `a` of the associated data to `B`, copies its first
`min (a, 16 − h)` bytes after it and chains the block (`aadHead_ok`);
the associated data is that block and the rest of it, padded, if there is
any (`aadPart_ok`): the blocks `Proof.AesCcm.adataBlocks`. `mac y` chains
`B₀`, the associated data and the payload padded (`mac_ok`): the blocks of
`Spec.Ccm.format`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (LoopPre copyLoop_ok minK_ok loopRegs minRegs Others add_ofNat_assoc eval_zero
  ofNat_sub toNat_ofNat_of_lt ofNat_add_ofNat)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks length_bytesAt bytesAt_writeBytes_at bytesAt_prefix
  bytesAt_suffix)

/-- The encoding of the length of the associated data, its first bytes and
the arguments of the chaining: what `aadHead` does before its call. -/
theorem aadHeadPre_ok {c : Cx} {s : State} (E : Env c s) {A : Addr} {a : Nat} (hA : Buf c s A a)
    (ha0 : 0 < a) (h23 : s.gpr .x23 = A) (h24 : s.gpr .x24 = BitVec.ofNat 64 a) :
    WP isa (.seq header (.seq minK (.seq (.block [.add .x .x11 .x19 .x25, ptr .x11 .x11 bO, mov .x12 .x23,
        mov .x13 .x10]) (.seq copyLoop (.block [.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10]))))) s fun s₅ =>
      Env c s₅ ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr ∧ Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₅.mem ∧
      s₅.gpr .x23 = A + BitVec.ofNat 64 (headLen a) ∧ s₅.gpr .x24 = BitVec.ofNat 64 (a - headLen a) ∧
      bytesAt s₅.mem (c.W + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a)) := by
  have ha := hA.lt
  have hh := Proof.AesCcm.hdrLen_le a
  have hh2 : 2 ≤ hdrLen a := by unfold hdrLen; split <;> [omega_arith; split <;> omega_arith]
  refine WP.seq (WP.mono (header_ok E ha0 ha h24) fun s₁ ⟨E₁, x25₁, hg₁, rd₁, wr₁, f₁, hB₁⟩ => ?_)
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 a := by rw [hg₁ _ (by decide), h24]
  have h23₁ : s₁.gpr .x23 = A := by rw [hg₁ _ (by decide), h23]
  refine WP.seq (WP.mono (minK_ok s₁ x25₁ h24₁ (by omega_arith) ha) fun s₂ ⟨x10₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = headLen a := by unfold headLen; omega_arith
  rw [hn1] at x10₂
  have hn1' : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega_arith
  have E₂ : Env c s₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  obtain ⟨s₃, run₃, x11₃, x12₃, x13₃, hg₃, hm₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
      [.add .x .x11 .x19 .x25, ptr .x11 .x11 bO, mov .x12 .x23, mov .x13 .x10] s₂ = some s₃ ∧
      s₃.gpr .x11 = c.W + BitVec.ofNat 64 (32 + hdrLen a) ∧ s₃.gpr .x12 = A ∧
      s₃.gpr .x13 = BitVec.ofNat 64 (headLen a) ∧ Others [.x11, .x12, .x13] s₂ s₃ ∧
      s₃.mem = s₂.mem ∧ s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    have x25₂ : s₂.gpr .x25 = BitVec.ofNat 64 (hdrLen a) := by rw [hg₂ _ (by decide), x25₁]
    have x23₂ : s₂.gpr .x23 = A := by rw [hg₂ _ (by decide), h23₁]
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E₂.x19, x25₂, BitVec.setWidth_eq]
      rw [BitVec.add_assoc, ofNat_add_ofNat, Nat.add_comm (hdrLen a) 32]
    · simp [gpr_write, x23₂]
    · simp [gpr_write, x10₂]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env c s₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  have hA₃ := hA.of_eq (s' := s₃) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
  have dAB : (⟨A, headLen a⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 (32 + hdrLen a), headLen a⟩ :=
    (hA.take hn1'.2.1).wd (by omega_arith)
  have lp : LoopPre s₃ A (c.W + BitVec.ofNat 64 (32 + hdrLen a)) (headLen a) :=
    ⟨by omega_arith, (hA₃.take hn1'.2.1).rd, E₃.perm.wC (by omega_arith), dAB⟩
  refine WP.seq (WP.mono (copyLoop_ok s₃ x12₃ x11₃ x13₃ hn1'.1 lp) fun s₄ ⟨hm₄, _, _, hg₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ : Env c s₄ := E₃.others hg₄ (by decide) sp₄ rd₄ wr₄
  have x23₄ : s₄.gpr .x23 = A := by
    rw [hg₄ _ (by decide), hg₃ _ (by decide), hg₂ _ (by decide), h23₁]
  have x24₄ : s₄.gpr .x24 = BitVec.ofNat 64 a := by
    rw [hg₄ _ (by decide), hg₃ _ (by decide), hg₂ _ (by decide), h24₁]
  have x10₄ : s₄.gpr .x10 = BitVec.ofNat 64 (headLen a) := by
    rw [hg₄ _ (by decide), hg₃ _ (by decide), x10₂]
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₅ hs₅ => ?_
  subst hs₅
  -- What was written.
  have fC : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains c.W (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega_arith) (by omega_arith)
        (by decide))
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← hm₂] at f₁; rw [← hm₃] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem A (headLen a) = (bytesAt s.mem A a).take (headLen a) := by
    rw [hm₃, hm₂, Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hA.take hn1'.2.1).wd (by decide)) (by omega_arith),
      bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem A a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega_arith
    rw [hm₄, show c.W + BitVec.ofNat 64 (32 + hdrLen a) = c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by
        rw [add_ofNat_assoc], bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega_arith) (by decide),
      length_bytesAt, hAk, hm₃, hm₂, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega_arith) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega_arith), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega_arith]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega_arith)
  refine ⟨E₄.others (rs := [.x23, .x24]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]) (by decide)
      rfl rfl rfl, by simp only [rd_write]; rw [rd₄, rd₃, rd₂, rd₁], by simp only [wr_write]; rw [wr₄, wr₃, wr₂, wr₁],
      fB, ?_, ?_, hB₄⟩
  · simp [gpr_write, x23₄, x10₄]
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, x24₄, x10₄]
    exact ofNat_sub hn1'.2.1 ha

/-- The first block of the associated data. -/
theorem aadHead_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : Addr} {a : Nat} (hA : Buf c s A a) (ha0 : 0 < a)
    (h23 : s.gpr .x23 = A) (h24 : s.gpr .x24 = BitVec.ofNat 64 a) :
    WP isa (aadHead v.callee y) s (Absorbed c y (A + BitVec.ofNat 64 (headLen a)) (a - headLen a) s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem A a).take (headLen a))])) := by
  refine seq_assoc5 (WP.seq (WP.mono (aadHeadPre_ok E hA ha0 h23 h24)
    fun s₅ ⟨E₅, rd₅, wr₅, fB, x23₅, x24₅, hB⟩ => ?_))
  have hY₅ : bytesAt s₅.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.AArch64.bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  refine WP.mono (updBlock_ok v L E₅ hy) fun s₆ ⟨E₆, g₆, rd₆, wr₆, f₆, h₆⟩ =>
    ⟨E₆, by rw [g₆ _ (by simp), x23₅], by rw [g₆ _ (by simp), x24₅],
      (fB.sub fun r hr => ?_).trans (f₆.sub fun r hr => ?_), ?_, by rw [rd₆, rd₅], by rw [wr₆, wr₅]⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [h₆, hY₅, hB, ciph_macR L (y := y) (by omega_arith) (fB.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)]

/-- The associated data, formatted and chained, if there is any. -/
theorem aadPart_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    {y : Nat} (hy : y = 0 ∨ y = 96) (h23 : s.gpr .x23 = c.A) (h24 : s.gpr .x24 = BitVec.ofNat 64 c.al) :
    WP isa (.ite (.zero .x .x24) (.block []) (.seq (aadHead v.callee y) (absorbPad v.callee y))) s
      (MacStep c y s (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem c.A c.al)))) := by
  have ha := L.al_lt
  have hA := L.bufA E.perm
  refine WP.ite (decide (c.al = 0)) (eval_zero h24 ha) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E, Frame.refl _ _, ?_, rfl, rfl⟩
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : c.al ≠ 0 := of_decide_eq_false hf
    refine WP.seq (WP.mono (aadHead_ok v L E hy hA (by omega_arith) h23 h24) fun s₂ A₂ => ?_)
    have hn1 : headLen c.al ≤ c.al := by unfold headLen; omega_arith
    have hT := (hA.drop hn1).of_eq (s' := s₂) A₂.rd A₂.wr
    refine WP.mono (absorbPad_ok v L A₂.env hy hT A₂.x23 A₂.x24) fun s₃ A₃ =>
      ⟨A₃.env, A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd], by rw [A₃.wr, A₂.wr]⟩
    rw [A₃.out, A₂.out, buf_macR hT (by omega_arith) A₂.frame, ciph_macR L (by omega_arith) A₂.frame,
      bytesAt_suffix _ _ hn1, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

/-- The addresses of the associated data, from their slots. -/
theorem aadLd_ok {c : Cx} {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO]) s fun s₁ =>
      s₁.gpr .x23 = c.A ∧ s₁.gpr .x24 = BitVec.ofNat 64 c.al ∧ Others [.x23, .x24] s s₁ ∧ s₁.mem = s.mem ∧
        s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := E.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have q₂ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [E.x19, q₁, q₂], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq]; rw [← S.aad]; rfl
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq]; rw [← S.alen]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]

/-- The data as the string to absorb. -/
theorem dataArgs_ok {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [mov .x23 .x27, mov .x24 .x28]) s fun s₁ =>
      s₁.gpr .x23 = c.D ∧ s₁.gpr .x24 = BitVec.ofNat 64 c.n ∧ Others [.x23, .x24] s s₁ ∧ s₁.mem = s.mem ∧
        s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨by simp [gpr_write, E.x27], by simp [gpr_write, E.x28], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) {s : State} (E : Env c s)
    (S : Slots c s.mem) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (mac v.callee y) s (MacStep c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format c.tl nonce (bytesAt s.mem c.A c.al) (bytesAt s.mem c.D c.n)))) := by
  have hy16 : y + 16 ≤ 2560 := by omega_arith
  refine WP.seq (WP.mono (aadLd_ok E S) fun s₁ ⟨x23₁, x24₁, og₁, hm₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : Env c s₁ := E.others og₁ (by decide) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (b0_ok v L E₁ (by rw [hm₁]; exact S) x24₁ hnl (by rw [hm₁]; exact hc0) hy)
    fun s₂ ⟨M₂, x23₂, x24₂⟩ => ?_)
  refine WP.seq (WP.mono (aadPart_ok v L M₂.env hy (by rw [x23₂, x23₁]) (by rw [x24₂, x24₁])) fun s₃ M₃ => ?_)
  refine WP.seq (WP.mono (dataArgs_ok M₃.env) fun s₄ ⟨x23₄, x24₄, og₄, hm₄, sp₄, rd₄, wr₄⟩ => ?_)
  have E₄ : Env c s₄ := M₃.env.others og₄ (by decide) sp₄ rd₄ wr₄
  refine WP.mono (absorbPad_ok v L E₄ hy (L.bufD E₄.perm) x23₄ x24₄) fun s₅ A₅ => ?_
  have f₃ : Frame (macR c.W y) s.mem s₃.mem := by rw [← hm₁]; exact M₂.frame.trans M₃.frame
  refine ⟨A₅.env, f₃.trans (by rw [← hm₄]; exact A₅.frame), ?_, by rw [A₅.rd, rd₄, M₃.rd, M₂.rd, rd₁],
    by rw [A₅.wr, wr₄, M₃.wr, M₂.wr, wr₁]⟩
  have hl : nonce.length ≤ 15 := by rw [hnl]; have := L.h13; omega_arith
  have f₂ : Frame (macR c.W y) s.mem s₂.mem := by rw [← hm₁]; exact M₂.frame
  rw [A₅.out, hm₄, M₃.out, M₂.out, ciph_macR L hy16 f₃, ciph_macR L hy16 f₂, hm₁, buf_macR (L.bufD E.perm) hy16 f₃,
    buf_macR (L.bufA E.perm) hy16 f₂, Proof.AesCcm.format_eq c.tl hl, length_bytesAt, length_bytesAt,
    Proof.Cmac.chain_append, Proof.Cmac.chain_append]

end VG.Proof.AesCcm.AArch64
