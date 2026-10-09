import VerifiedGarbage.Proof.AesCcm.AArch64.Chunk
import VerifiedGarbage.Proof.AesCcm.AArch64.Cmp

/-!
# AES-CCM on AArch64: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_ok`, by `chunk_ok`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_ok`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_ok`), which is its encryption (`Proof.AesCcm.crypt_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm xorLoop)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call Others add_ofNat_assoc eval_zero eval_nonzero
  LoopPre xorLoop_ok xorBytes loopRegs lsr_ofNat and15 toNat_ofNat_of_lt covers_off covers_left)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesCcm (xorFrom xorFrom_append xorFrom_tail xorFrom_zeros ctr32_ccm length_bytesAt
  bytesAt_prefix bytesAt_writeBytes_at BlockCipher)

/-- `x23`, `x24` and `x25` for the first chunk. -/
theorem ctrHeadBlk_ok {c : Cx} (L : Lay c) {nonce : List Byte} {s : State} (E : Env c s) :
    WP isa (.block [mov .x23 .x27, .lsr .x .x24 .x28 4, imm .x25 1]) s (CtrInv c nonce s 0) := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨E.others (rs := [.x23, .x24, .x25]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]) (by decide)
      rfl rfl rfl, rfl, rfl, ?_, ?_, ?_, Nat.zero_le _, Frame.refl _ _, rfl, by simp [mem_write]⟩
  · simp [gpr_write, E.x27]
  · simp [gpr_write, E.x28, lsr_ofNat c.n 4 L.n_lt]
  · simp [gpr_write]

/-- The whole blocks, in chunks. -/
theorem ctrHead_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl)
    {s : State} (E : Env c s) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (.seq (.block [mov .x23 .x27, .lsr .x .x24 .x28 4, imm .x25 1])
      (.ite (.zero .x .x24) (.block []) (.loop (ctrChunk v.callee) (.nonzero .x .x24)))) s
      (CtrInv c nonce s (c.n / 16)) := by
  have hn64 := L.n_lt
  refine WP.seq (WP.mono (ctrHeadBlk_ok L (nonce := nonce) E) fun s₁ I₀ => ?_)
  refine WP.ite (decide (c.n / 16 = 0)) (eval_zero (a := c.n / 16) (by rw [I₀.x24, Nat.sub_zero]) (by omega_arith))
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n / 16 = 0 := of_decide_eq_true ht
    exact WP.block_nil (by rw [h0]; exact I₀)
  · have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = c.n / 16 - b ∧ b < c.n / 16 ∧ CtrInv c nonce s b t) ?_
      (c.n / 16 - 0) s₁ ⟨0, rfl, by omega_arith, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (chunk_ok v L hnl hc0 I hb) fun t' ⟨k, _, hk1, hkb, I'⟩ => ?_
    have ev := eval_nonzero (r := .x24) (a := c.n / 16 - (b + k)) I'.x24 (by omega_arith)
    by_cases he : b + k = c.n / 16
    · left; exact ⟨by rw [ev]; simp [he], by rw [← he]; exact I'⟩
    · right; exact ⟨by rw [ev]; simp; omega_arith, c.n / 16 - (b + k), by omega_arith, b + k, rfl, by omega_arith, I'⟩

/-- The arguments of the call for the last bytes: `Ctrⱼ` and a zero block at
`W + 80`. -/
theorem tailSetup_ok {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {t : State}
    (E : Env c t) (hc0 : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {j : Nat}
    (hj : j < 256 ^ (15 - c.nl)) (h25 : t.gpr .x25 = BitVec.ofNat 64 j) :
    WP isa (.block (([mov .x9 .x25] : List Instr) ++ ctrAt ++ zero16 ksO ++ ctrArgs ++
        ([ptr .x3 .x19 ksO, imm .x4 1] : List Instr))) t fun t' =>
      Env c t' ∧ CtrCall t' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
      Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce j ∧
      bytesAt t'.mem (c.W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] t t' ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  have h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  have hg₁ : Others [.x9] t t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  have E₁ : Env c t₁ := E.others hg₁ (by decide) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  have h9 : t₁.gpr .x9 = BitVec.ofNat 64 j := by rw [← ht₁]; simp [gpr_write, h25]
  have hm₁ : t₁.mem = t.mem := by rw [← ht₁]; rfl
  refine WP.block_append (WP.mono (ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := j) (by rw [hnl]; exact hj) h9)
    fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  have w₁ := E₂.perm.wW (show 80 + 8 ≤ 2560 by decide)
  have w₂ := E₂.perm.wW (show 88 + 8 ≤ 2560 by decide)
  obtain ⟨t₃, run₃, hm₃, x0, x1, x2, x3, x4, x5, hg₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      (zero16 ksO ++ ctrArgs ++ [ptr .x3 .x19 ksO, imm .x4 1]) t₂ = some t₃ ∧
      t₃.mem = (t₂.mem.writeW (c.W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 88)
        (0 : BitVec 64) ∧
      t₃.gpr .x0 = c.K ∧ t₃.gpr .x1 = BitVec.ofNat 64 c.R ∧ t₃.gpr .x2 = c.W + BitVec.ofNat 64 64 ∧
      t₃.gpr .x3 = c.W + BitVec.ofNat 64 80 ∧ t₃.gpr .x4 = BitVec.ofNat 64 1 ∧
      t₃.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9] t₂ t₃ ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by carun [ctrArgs, E₂.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E₂.x21]
    · simp [gpr_write, E₂.x22]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write]
    · simp [gpr_write, E₂.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨t₃, by simpa only [List.append_assoc] using run₃, ?_⟩
  have E₃ : Env c t₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  have e88 : c.W + BitVec.ofNat 64 88 = c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have c80 : ∀ d, 80 ≤ d → d + 8 ≤ 96 →
      (⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => Offset.contains c.W (by omega_arith) (by omega_arith) (by decide)
  have fz : Frame [⟨c.W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))
  refine ⟨E₃, cargsW L E₃ (o := 64) (d := 80) (by decide) (by decide) (by decide) x0 x1 x2 x3 x4 x5, ?_, ?_, ?_,
    fun r hr => ?_, by rw [rd₃, rd₂, ← ht₁]; rfl, by rw [wr₃, wr₂, ← ht₁]; rfl⟩
  · rw [hm₃, ← hm₁]
    exact ((f₂.sub fun r hr => ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 80 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 88 (by decide) (by decide))
  · rw [Proof.AesGcm.AArch64.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c.W (.inl (by decide)) (by decide) (by decide)) (by decide), hc₂]
  · rw [hm₃, e88, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      hg₂ r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
    exact hg₁ r (by simp [hr.2.2.2.2.2.2.1])

/-- The last `n mod 16` bytes, after the whole blocks. -/
theorem tail_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State}
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {t t₀ : State}
    (I : CtrInv c nonce s (c.n / 16) t) (E₀ : Env c t₀) (hm₀ : t₀.mem = t.mem)
    (h23 : t₀.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h25 : t₀.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16)) (h26 : t₀.gpr .x26 = BitVec.ofNat 64 (c.n % 16))
    (hrd₀ : t₀.rd = t.rd) (hwr₀ : t₀.wr = t.wr) (h0 : c.n % 16 ≠ 0) :
    WP isa (ctrTail v.callee) t₀ fun t' => Env c t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (ctrR c) s.mem t'.mem ∧
      bytesAt t'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  have hq16 : c.n / 16 < 256 ^ (15 - c.nl) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) L.hn
  have hc0₀ : bytesAt t₀.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₀, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by decide))) (by decide), hc0]
  refine WP.seq (WP.mono (tailSetup_ok L hnl E₀ hc0₀ (j := 1 + c.n / 16) (by have := L.hn; omega_arith) h25)
    fun t₁ ⟨E₁, C₁, f₁, hc₁, hz₁, hg₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (ctr_call v C₁) fun t₂ h => ?_)
  have E₂ : Env c t₂ := E₁.of_saved h.saved h.sp h.rd h.wr
  have sv : ∀ r ∈ [Reg.x23, .x26], t₂.gpr r = t₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl <;> decide) (by rcases hr with rfl | rfl <;> decide),
      hg₁ r (by rcases hr with rfl | rfl <;> decide)]
  obtain ⟨t₃, run₃, x11₃, x12₃, x13₃, hg₃, hm₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      [ptr .x11 .x19 ksO, mov .x12 .x23, mov .x13 .x26] t₂ = some t₃ ∧
      t₃.gpr .x11 = c.W + BitVec.ofNat 64 80 ∧ t₃.gpr .x12 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
      t₃.gpr .x13 = BitVec.ofNat 64 (c.n % 16) ∧ Others [.x11, .x12, .x13] t₂ t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, sv .x23 (by simp), h23]
    · simp [gpr_write, sv .x26 (by simp), h26]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env c t₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  have rd₃' : t₃.rd = s.rd := by rw [rd₃, h.rd, rd₁, hrd₀, I.rd]
  have wr₃' : t₃.wr = s.wr := by rw [wr₃, h.wr, wr₁, hwr₀, I.wr]
  have hS := (L.bufD E₃.perm).slice (a := 16 * (c.n / 16)) (k := c.n % 16) (by omega_arith)
  have lp : LoopPre t₃ (c.W + BitVec.ofNat 64 80) (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) :=
    ⟨by omega_arith, E₃.perm.wCR (by omega_arith), covers_off E₃.perm.d (by omega_arith) hn64, (hS.wd (by omega_arith)).symm⟩
  refine WP.mono (xorLoop_ok t₃ x11₃ x12₃ x13₃ (by omega_arith) lp) fun t₄ ⟨hm₄, hg₄, sp₄, rd₄, wr₄⟩ => ?_
  -- What the tail wrote.
  have cT : Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₃.mem := by
    rw [hm₃, ← hm₀]
    refine (f₁.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub c.W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  have sep : ∀ {a l : Nat}, a + l ≤ c.n → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes t₃.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
      (c.W + BitVec.ofNat 64 80) (c.n % 16) := ⟨_, rfl⟩
  rw [← hxs] at hm₄
  have hxl : xs.length = c.n % 16 := by simp [hxs, xorBytes, length_bytesAt]
  have fw : Frame [⟨c.D + BitVec.ofNat 64 (16 * (c.n / 16)), c.n % 16⟩] t₃.mem t₄.mem := by
    rw [hm₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨E₃.others hg₄ (by decide) sp₄ rd₄ wr₄, by rw [rd₄, rd₃'], by rw [wr₄, wr₃'], ?_, ?_⟩
  · refine I.frame.trans ((cT.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega_arith)⟩
  · -- The bytes.
    have h₁ : bytesAt t₃.mem c.D (16 * (c.n / 16)) = bytesAt t.mem c.D (16 * (c.n / 16)) := by
      have := Proof.AesGcm.AArch64.bytesAt_frame cT (sep (a := 0) (l := 16 * (c.n / 16)) (by omega_arith)) (by omega_arith)
      rwa [BitVec.add_zero] at this
    have h₂ : bytesAt t₃.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) := by
      rw [Proof.AesGcm.AArch64.bytesAt_frame cT (sep (by omega_arith)) (by omega_arith),
        show c.n % 16 = c.n - 16 * (c.n / 16) by omega_arith, I.rest]
    have f₁' : Frame (ctrR c) s.mem t₁.mem := I.frame.trans (by
      rw [← hm₀]; exact f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩)
    have hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem c.K c.R) := fun x => Proof.Cmac.aesWith_length _ _ x
    have hks : bytesAt t₃.mem (c.W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem c.K c.R (Spec.Ccm.ctrBlock nonce (1 + c.n / 16)) := by
      have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + c.n / 16) (by rw [hnl]; have := L.h13; omega_arith)
        (fun i hi => by
          rw [show i = 0 by omega_arith, Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [hc₁]) h.out
      rw [Nat.mul_one] at hx
      rw [hm₃, hx, hz₁, ciph_ctrR L f₁', xorFrom_zeros hBC]
    have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem c.K c.R) nonce (1 + c.n / 16)
      (d := bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt, hBC] at ht
    have ht' := ht.resolve_right (by omega_arith)
    rw [hm₄, bytesAt_writeBytes_at t₃.mem c.D xs (by rw [hxl]; omega_arith) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega_arith), List.append_nil,
      ← bytesAt_prefix t₃.mem c.D (show 16 * (c.n / 16) ≤ c.n by omega_arith), h₁, I.done, hxs, xorBytes, h₂,
      bytesAt_prefix t₃.mem (c.W + BitVec.ofNat 64 80) (show c.n % 16 ≤ 16 by omega_arith), hks, ht']
    conv => rhs; rw [show c.n = 16 * (c.n / 16) + c.n % 16 from (Nat.div_add_mod c.n 16).symm]
    rw [Proof.Cmac.Stream.bytesAt_append, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 (c.n / 16)]

/-- `x26 = n mod 16`. -/
theorem lastLen_ok {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa (.block [imm .x9 15, .logic .and .x .x26 .x28 .x9]) t fun t₀ =>
      t₀.gpr .x26 = BitVec.ofNat 64 (c.n % 16) ∧ Others [.x9, .x26] t t₀ ∧ t₀.mem = t.mem ∧ t₀.sp = t.sp ∧
        t₀.rd = t.rd ∧ t₀.wr = t.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₀ ht₀ => ?_
  subst ht₀
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E.x28]
    rw [and15, toNat_ofNat_of_lt L.n_lt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (ctr v.callee) s fun s' => Env c s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame (ctrR c) s.mem s'.mem ∧
      bytesAt s'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 := L.n_lt
  refine WP.assoc (WP.seq (WP.mono (ctrHead_ok v L hnl E hc0) fun t I => ?_))
  refine WP.seq (WP.mono (lastLen_ok L I.env) fun t₀ ⟨x26₀, hg₀, hm₀, sp₀, rd₀, wr₀⟩ => ?_)
  have E₀ : Env c t₀ := I.env.others hg₀ (by decide) sp₀ rd₀ wr₀
  refine WP.ite (decide (c.n % 16 = 0)) (eval_zero x26₀ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E₀, by rw [rd₀, I.rd], by rw [wr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (c.n / 16) = c.n by omega_arith] at hd
    rw [hm₀, hd]
  · exact tail_ok v L hnl hc0 I E₀ hm₀ (by rw [hg₀ _ (by decide), I.x23]) (by rw [hg₀ _ (by decide), I.x25]) x26₀
      rd₀ wr₀ (of_decide_eq_false hf)

end VG.Proof.AesCcm.AArch64
