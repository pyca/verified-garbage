import VerifiedGarbage.Proof.AesCcm.X86.Mac

/-!
# AES-CCM on x86: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data with one call of `vg_aes_ctr32` from `Ctr₁`, whose low 32
bits do not wrap around as there are fewer than 2²⁸ blocks (`ctrWhole_ok`),
then its last `n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which
`vg_aes_ctr32` writes over a zero block (`ctrTail_ok`): the data XORed with
CCM's keystream from `Ctr₁` (`ctr_ok`), which is its encryption
(`Proof.AesCcm.crypt_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop splitWhole dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold zero4_bytes' length_bytesAt and_self_beq32
  XorPre XorPost xorLoop_ok xorBytes shr4 and15 runBlock_app_of covers_left covers_off)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `[64, 96)`, `[240, 2560)`, the stack and the data. -/
abbrev ctrR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 64, 32⟩, wC W, below SP 56, ⟨w64 D, n⟩]

/-- What `ctr` needs. -/
structure CtrCtx (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n : Nat) : Prop where
  lay : Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  hn : n < 256 ^ (15 - nonce.length)
  hn32 : n < 2 ^ 32
  c0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0
  buf : Buf W SP s D n
  dw : Covers [⟨w64 D, n⟩] s.wr
  dk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, n⟩

namespace CtrCtx

variable {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32} {n : Nat}
  (C : CtrCtx K W SP s R nonce D n)
include C

/-- The parts of `W` that `ctr` does not write. -/
theorem disj {d k : Nat} (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 240)) :
    ∀ r ∈ ctrR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rcases h with h | h
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (C.lay.stk_w' (by omega)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega))).symm

theorem slot_kept {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m W o = slotv s.mem W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (C.disj (.inr ⟨by omega, h₂⟩)) (by decide)

theorem c0_kept {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) :
    bytesAt m (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  rw [Proof.AesGcm.X86.bytesAt_frame hf (C.disj (.inl (by decide))) (by decide), C.c0]

theorem ciph_kept {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) :
    Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases C.rounds with h | h | h <;> subst h <;> decide
  refine ctxCiph_frame hf (fun r hr => ?_) hRb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.stk_k.symm
  · exact C.dk

end CtrCtx

/-- After the whole blocks. -/
structure CtrMid (K W SP : BitVec 32) (s : State) (R : Nat) (nonce : List Byte) (D : BitVec 32) (n : Nat) (t : State) :
    Prop where
  env : Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (ctrR W SP D n) s.mem t.mem
  dO : slotv t.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16))
  nO : slotv t.mem W nO = BitVec.ofNat 32 (n % 16)
  done : bytesAt t.mem (w64 D) (16 * (n / 16)) =
    xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) (16 * (n / 16)))
  rest : bytesAt t.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
    bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)

/-! ## The whole blocks -/

/-- The data and its length into `dO` and `nO`, and split. -/
theorem ctrSplit_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole) s = some s₁ ∧
      s₁.gpr .ebx = D ∧ s₁.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧
      Env K W SP s₁ ∧ Frame [wC W] s.mem s₁.mem ∧ slotv s₁.mem W dO = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      slotv s₁.mem W nO = BitVec.ofNat 32 (n % 16) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain ⟨sa, runa, hma, hbpa, hspa, hrda, hwra⟩ : ∃ sa, runBlock isa
      [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax] s =
        some sa ∧
      sa.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) D).writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 n) ∧
      sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s.rd ∧ sa.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hDp, hlen], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hDp, hlen]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have Ea : Env K W SP sa := E.keep (by rw [hbpa, E.ebp]) (by rw [hspa, E.esp]) hrda hwra
  have hda : slotv sa.mem W dO = D := by
    rw [hma, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have hna : slotv sa.mem W nO = BitVec.ofNat 32 n := by rw [hma]; exact Mem.readW_writeW_self32 _ _ _
  obtain ⟨s₁, run₁, hbx, hdi, hzf, hbp, hsp, hm₁, hrd₁, hwr₁⟩ := split_ok L Ea hda hna hn32
  have cw : ∀ d, 240 ≤ d → d + 4 ≤ 2560 → (wC W).Contains (w64 W + BitVec.ofNat 64 d) 4 := fun d h₁ h₂ =>
    Offset.contains (w64 W) h₁ (by omega) (by decide)
  refine ⟨s₁, runBlock_app_of runa run₁, hbx, hdi, hzf, Ea.keep (by rw [hbp, hbpa]) (by rw [hsp, hspa]) hrd₁ hwr₁,
    ?_, ?_, ?_, by rw [hrd₁, hrda], by rw [hwr₁, hwra]⟩
  · rw [hm₁, hma]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 276 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cw 272 (by decide) (by decide))
  · rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
  · rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _

/-- `Ctrᵢ` at `W + 64`, and the key schedule, the number of rounds and
`W + 64` in `eax`, `ecx`, `edx`, for `vg_aes_ctr32`. -/
theorem ctrArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : Lay K W SP) (E₁ : Env K W SP s₁) {R : Nat}
    (hK₁ : slotv s₁.mem W ctxO = K) (hR₁ : slotv s₁.mem W roundsO = BitVec.ofNat 32 R) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) {Q : BitVec 32} {b : BitVec 32}
    (hbx : s₁.gpr .ebx = Q) (hdi : s₁.gpr .edi = b) :
    ∃ sc, runBlock isa (([.mov .eax (imm i)] : List Instr) ++ ctrAt ++ keyArgs c1O) s₁ = some sc ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s₁.mem sc.mem ∧
      bytesAt sc.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i ∧
      sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧ sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = Q ∧
      sc.gpr .edi = b ∧ sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = s₁.rd ∧ sc.wr = s₁.wr := by
  obtain ⟨sa, runa, hma, haxa, hbxa, hdia, hbpa, hspa, hrda, hwra⟩ : ∃ sa, runBlock isa [.mov .eax (imm i)] s₁ =
      some sa ∧ sa.mem = s₁.mem ∧ sa.gpr .eax = BitVec.ofNat 32 i ∧ sa.gpr .ebx = Q ∧
      sa.gpr .edi = b ∧ sa.gpr .ebp = W ∧ sa.gpr .esp = SP ∧ sa.rd = s₁.rd ∧ sa.wr = s₁.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs []
    · cregs [hbx]
    · cregs [hdi]
    · cregs [E₁.ebp]
    · cregs [E₁.esp]
    all_goals cmems []
  have Ea : Env K W SP sa := E₁.keep (by rw [hbpa, E₁.ebp]) (by rw [hspa, E₁.esp]) hrda hwra
  obtain ⟨sb, runb, fb, hcb, hgb, hrdb, hwrb⟩ := ctrAt_ok L Ea h7 h13 (by rw [hma]; exact hc0) hi hi32 haxa
  have Eb : Env K W SP sb := Ea.keep (by rw [hgb .ebp (by decide) (by decide)]) (by rw [hgb .esp (by decide) (by decide)])
    hrdb hwrb
  have kb : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv sb.mem W o = slotv s₁.mem W o := fun o h₁ h₂ => by
    show sb.mem.readW (w64 W + BitVec.ofNat 64 o) 32 = _
    rw [fb.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide), hma]
  have hKb : slotv sb.mem W ctxO = K := by rw [kb _ (by decide) (by decide)]; exact hK₁
  have hRb' : slotv sb.mem W roundsO = BitVec.ofNat 32 R := by rw [kb _ (by decide) (by decide)]; exact hR₁
  obtain ⟨sc, runc, hmc, hax, hcx, hdx, hbxc, hdic, hbpc, hspc, hrdc, hwrc⟩ : ∃ sc, runBlock isa (keyArgs c1O) sb =
      some sc ∧ sc.mem = sb.mem ∧ sc.gpr .eax = K ∧ sc.gpr .ecx = BitVec.ofNat 32 R ∧
      sc.gpr .edx = W + BitVec.ofNat 32 64 ∧ sc.gpr .ebx = Q ∧ sc.gpr .edi = b ∧
      sc.gpr .ebp = W ∧ sc.gpr .esp = SP ∧ sc.rd = sb.rd ∧ sc.wr = sb.wr := by
    refine ⟨_, by crun [keyArgs, Eb.ebp, L.aW, Eb.perm.wR, hKb, hRb'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hKb]
    · cregs [hRb']
    · cregs [Eb.ebp]
    · cregs [hgb .ebx (by decide) (by decide), hbxa]
    · cregs [hgb .edi (by decide) (by decide), hdia]
    · cregs [Eb.ebp]
    · cregs [Eb.esp]
    all_goals cmems []
  exact ⟨sc, runBlock_app_of (runBlock_app_of runa runb) runc, by rw [hmc, ← hma]; exact fb, by rw [hmc]; exact hcb,
    hax, hcx, hdx, hbxc, hdic, hbpc, hspc, by rw [hrdc, hrdb, hrda], by rw [hwrc, hwrb, hwra]⟩

/-- The whole blocks of the data, by one call of `vg_aes_ctr32` from `Ctr₁`. -/
theorem ctrWhole_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (.seq (.block (([.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp nO) .eax] : List Instr) ++ splitWhole))
      (.ite .e (.block []) (.seq (.block (([.mov .eax (imm 1)] : List Instr) ++ ctrAt ++ keyArgs c1O)) (ctrCall v.callee)))) s
      (CtrMid K W SP s R nonce D n) := by
  have L := C.lay
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain ⟨s₁, run₁, hbx, hdi, hzf, E₁, f₁, hd₁, hn₁, hrd₁, hwr₁⟩ := ctrSplit_ok L E hDp hlen C.hn32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have fr₁ : Frame (ctrR W SP D n) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, fun _ h => h⟩
  have dD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [wC W], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (C.buf.w.sub_left (Offset.sub_base _ h)).sub_right (Lay.wSub (by decide))
  have hrest₁ : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (dD (by omega)) (by omega)
  refine WP.ite (decide (n / 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, hrd₁, hwr₁, fr₁, hd₁, hn₁, ?_, hrest₁⟩
    rw [h0, Nat.mul_zero]; rfl
  · have h0 : n / 16 ≠ 0 := of_decide_eq_false hf
    have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ => C.slot_kept fr₁ h₁ h₂
    obtain ⟨sc, runc, fc, hcc, hax, hcx, hdx, hbxc, hdic, hbpc, hspc, hrdc, hwrc⟩ :=
      ctrArgs_ok L E₁ (by rw [k₁ _ (by decide) (by decide)]; exact hK) (by rw [k₁ _ (by decide) (by decide)]; exact hRo)
        C.h7 C.h13 (C.c0_kept fr₁) (i := 1) (by
          have : 1 ≤ 256 ^ (15 - nonce.length) := Nat.pow_pos (by decide)
          have := C.hn
          omega) (by decide) hbx hdi
    refine WP.seq (WP.of_runBlock ⟨sc, runc, ?_⟩)
    have Ec : Env K W SP sc := E₁.keep (by rw [hbpc, E₁.ebp]) (by rw [hspc, E₁.esp]) hrdc hwrc
    have rdc : sc.rd = s.rd := by rw [hrdc, hrd₁]
    have wrc : sc.wr = s.wr := by rw [hwrc, hwr₁]
    have hq := srcBuf ((C.buf.take hb).of_eq rdc wrc)
    have hqc : (⟨w64 D, 16 * (n / 16)⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ :=
      (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide))
    have hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * (n / 16)⟩ := C.dk.sub_right (Region.sub_prefix hb)
    have hqw : Covers [⟨w64 D, 16 * (n / 16)⟩] sc.wr := by
      rw [wrc]
      intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      exact C.dw a k ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
    refine WP.mono (ctrCall_ok v L Ec C.rounds (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbxc hdic)
      fun s₄ ⟨E₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_
    -- What was written.
    have fsc : Frame (ctrR W SP D n) s.mem sc.mem :=
      fr₁.trans (fc.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    have f₄' : Frame (ctrR W SP D n) sc.mem s₄.mem := f₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨w64 D, n⟩, by simp, Region.sub_prefix hb⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
    have k₄ : ∀ o, 240 ≤ o → o + 4 ≤ 384 → slotv s₄.mem W o = slotv sc.mem W o := fun o h₁ h₂ =>
      f₄.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact ((C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega))).symm
        · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
        · exact (L.stk_w' (by omega)).symm) (by decide)
    have kc : ∀ o, 240 ≤ o → o + 4 ≤ 384 → slotv sc.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
      fc.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
        (by decide)
    refine ⟨E₄, by rw [rd₄, rdc], by rw [wr₄, wrc], fsc.trans f₄', by rw [k₄ _ (by decide) (by decide),
      kc _ (by decide) (by decide), hd₁], by rw [k₄ _ (by decide) (by decide), kc _ (by decide) (by decide), hn₁],
      ?_, ?_⟩
    · have hDsc : bytesAt sc.mem (w64 D) (16 * (n / 16)) = bytesAt s.mem (w64 D) (16 * (n / 16)) := by
        rw [Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)))
            (by have := C.hn32; omega),
          Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (C.buf.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)))
            (by have := C.hn32; omega)]
      have hc := Proof.AesCcm.ctr32_ccm (m := sc.mem) (m' := s₄.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
        (D := w64 D) (R := R) (nonce := nonce) (by have := C.h13; omega) (j := 1) (k := n / 16)
        (fun i hi => by
          rw [show Spec.Gcm.blockAt sc.mem (w64 W + BitVec.ofNat 64 64) = Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce 1)
            from by show Spec.Gcm.ofBytes _ = _; rw [hcc]]
          exact Proof.AesCcm.repeat_inc32_ctrBlock C.h7 C.h13 (j := 1) (k := n / 16)
            (by have := C.hn32; omega) (by have := C.hn; omega) i hi) o₄
      rw [hc, C.ciph_kept fsc, hDsc]
    · have sR : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
        Offset.sub_base (w64 D) (d := 16 * (n / 16)) (n := n % 16) (k := n) (by omega)
      have hlt : n % 16 ≤ 2 ^ 64 := by omega
      rw [Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))
        · simpa using Offset.disjoint (w64 D) (d := 16 * (n / 16)) (n := n % 16) (e := 0) (k := 16 * (n / 16))
            (.inr (by omega)) (by have := C.hn32; omega) (by have := C.hn32; omega)
        · exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))
        · exact (C.buf.stk.sub_right sR).symm) hlt,
        Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (C.buf.w.sub_left sR).sub_right (Lay.wSub (by decide))) hlt, hrest₁]

/-! ## The last bytes -/

/-- `Ctrⱼ`, `j = ⌊n / 16⌋ + 1`, at `W + 64`, the keystream block at `W + 80`
zeroed, and the arguments of `vg_aes_ctr32` to encrypt it. -/
theorem ctrTailArgs_ok {K W SP : BitVec 32} {t₀ : State} (L : Lay K W SP) (E₀ : Env K W SP t₀) {R : Nat}
    (hK₀ : slotv t₀.mem W ctxO = K) (hR₀ : slotv t₀.mem W roundsO = BitVec.ofNat 32 R) {n : Nat}
    (hl₀ : slotv t₀.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t₀.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (hj : n / 16 + 1 < 256 ^ (15 - nonce.length)) :
    ∃ tc, runBlock isa (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
        keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)) t₀ = some tc ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩] t₀.mem tc.mem ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (n / 16 + 1) ∧
      bytesAt tc.mem (w64 W + BitVec.ofNat 64 80) 16 = Spec.Gcm.zeros 16 ∧
      tc.gpr .eax = K ∧ tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = t₀.rd ∧ tc.wr = t₀.wr := by
  have hbp₀ := E₀.ebp
  have hsp₀ := E₀.esp
  obtain ⟨ta, runa, hma, haxa, hbpa, hspa, hrda, hwra⟩ : ∃ ta, runBlock isa
      [.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] t₀ = some ta ∧ ta.mem = t₀.mem ∧
      ta.gpr .eax = BitVec.ofNat 32 (n / 16 + 1) ∧ ta.gpr .ebp = W ∧ ta.gpr .esp = SP ∧ ta.rd = t₀.rd ∧
      ta.wr = t₀.wr := by
    refine ⟨_, by crun [hbp₀, L.aW, E₀.perm.wR, hl₀], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hl₀, shr4 hn32]; exact (BitVec.ofNat_add _ _).symm
    · cregs [hbp₀]
    · cregs [hsp₀]
    all_goals cmems []
  have Ea : Env K W SP ta := E₀.keep (by rw [hbpa, hbp₀]) (by rw [hspa, hsp₀]) hrda hwra
  obtain ⟨tb, runb, fb, hcb, hgb, hrdb, hwrb⟩ := ctrAt_ok L Ea h7 h13 (by rw [hma]; exact hc0) hj (by omega) haxa
  have hbpb : tb.gpr .ebp = W := by rw [hgb .ebp (by decide) (by decide), hbpa]
  have hspb : tb.gpr .esp = SP := by rw [hgb .esp (by decide) (by decide), hspa]
  have Eb : Env K W SP tb := Ea.keep (by rw [hbpb, hbpa]) (by rw [hspb, hspa]) hrdb hwrb
  have kb : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv tb.mem W o = slotv t₀.mem W o := fun o h₁ h₂ => by
    show tb.mem.readW (w64 W + BitVec.ofNat 64 o) 32 = _
    rw [fb.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide), hma]
  have hKb : slotv tb.mem W ctxO = K := by rw [kb _ (by decide) (by decide)]; exact hK₀
  have hRb' : slotv tb.mem W roundsO = BitVec.ofNat 32 R := by rw [kb _ (by decide) (by decide)]; exact hR₀
  have hz := zero4_fold tb.mem W 80
  simp only [Nat.reduceAdd] at hz
  obtain ⟨tc, runc, hmc, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ : ∃ tc, runBlock isa
      (zero4 ksO ++ (keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr))) tb =
        some tc ∧ tc.mem = Cmac.zero4 tb.mem (w64 W + BitVec.ofNat 64 80) ∧ tc.gpr .eax = K ∧
      tc.gpr .ecx = BitVec.ofNat 32 R ∧ tc.gpr .edx = W + BitVec.ofNat 32 64 ∧
      tc.gpr .ebx = W + BitVec.ofNat 32 80 ∧ tc.gpr .edi = BitVec.ofNat 32 1 ∧ tc.gpr .ebp = W ∧
      tc.gpr .esp = SP ∧ tc.rd = tb.rd ∧ tc.wr = tb.wr := by
    refine ⟨_, by crun [zero4, keyArgs, hbpb, L.aW, Eb.perm.wW, Eb.perm.wR, hKb, hRb'], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · cmems [hz]
    · cregs [hKb]
    · cregs [hRb']
    · cregs [hbpb]
    · cregs [hbpb]
    · cregs []
    · cregs [hbpb]
    · cregs [hspb]
    all_goals cmems []
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 80, 16⟩] tb.mem tc.mem := by rw [hmc]; exact Cmac.frame_store4 _ _ _ _ _
  refine ⟨tc, by
      simp only [List.append_assoc]
      exact runBlock_app_of runa (runBlock_app_of runb runc), ?_, ?_, by rw [hmc, zero4_bytes'],
    hax, hcx, hdx, hbx, hdi, hbpc, hspc, by rw [hrdc, hrdb, hrda], by rw [hwrc, hwrb, hwra]⟩
  · rw [← hma]
    exact (fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩).trans
      (fz.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩)
  · rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), hcb]

/-- The arguments of the XOR of the last bytes with the keystream block. -/
theorem xorArgs_ok {K W SP : BitVec 32} {td : State} (L : Lay K W SP) (Ed : Env K W SP td) {P : BitVec 32} {t : Nat}
    (hdd : slotv td.mem W dO = P) (hnd : slotv td.mem W nO = BitVec.ofNat 32 t) :
    ∃ te, runBlock isa
      [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)] td = some te ∧
      te.mem = td.mem ∧ te.gpr .edi = P ∧ te.gpr .edx = W + BitVec.ofNat 32 80 ∧
      te.gpr .ecx = BitVec.ofNat 32 t ∧ te.gpr .ebp = W ∧ te.gpr .esp = SP ∧ te.rd = td.rd ∧ te.wr = td.wr := by
  have hbpd := Ed.ebp
  refine ⟨_, by crun [hbpd, L.aW, Ed.perm.wR, hdd, hnd], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hdd]
  · cregs [hbpd]
  · cregs [hnd]
  · cregs [hbpd]
  · cregs [Ed.esp]
  all_goals cmems []

/-- The last `n mod 16` bytes, with `CIPH_K(Ctr₁₊ₙ/₁₆)`, after the whole blocks. -/
theorem ctrTail_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : CtrCtx K W SP s R nonce D n) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) {t : State}
    (I : CtrMid K W SP s R nonce D n t) :
    WP isa (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
      (.ite .e (.block [])
        (.seq (.block (([.mov .eax (slot lenO), .shift .shr .eax 4, .alu .add .eax (imm 1)] : List Instr) ++ ctrAt ++ zero4 ksO ++
            keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksO), .mov .edi (imm 1)] : List Instr)))
        (.seq (ctrCall v.callee)
          (.seq (.block [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm ksO), .mov .ecx (slot nO)])
            xorLoop))))) t
      fun t' => Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (ctrR W SP D n) s.mem t'.mem ∧
        bytesAt t'.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n) := by
  have L := C.lay
  have E := I.env
  have hn32 := C.hn32
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have k₀ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv t.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    C.slot_kept I.frame h₁ h₂
  obtain ⟨t₀, run₀, hm₀, hzf, hbp₀, hsp₀, hrd₀, hwr₀⟩ := testN_ok L E (r := n % 16) (by omega) I.nO
  refine WP.seq (WP.of_runBlock ⟨t₀, run₀, ?_⟩)
  have E₀ : Env K W SP t₀ := E.keep (by rw [hbp₀, E.ebp]) (by rw [hsp₀, E.esp]) hrd₀ hwr₀
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨t₀, rfl, E₀, by rw [hrd₀, I.rd], by rw [hwr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (n / 16) = n by omega] at hd
    rw [hm₀, hd]
  · have h0 : n % 16 ≠ 0 := of_decide_eq_false hf
    have hj : n / 16 + 1 < 256 ^ (15 - nonce.length) := by have := C.hn; omega
    obtain ⟨tc, runc, ft, hcc, hz80, hax, hcx, hdx, hbx, hdi, hbpc, hspc, hrdc, hwrc⟩ :=
      ctrTailArgs_ok L E₀ (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hK)
        (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hRo) (by rw [hm₀, k₀ _ (by decide) (by decide)]; exact hlen)
        hn32 C.h7 C.h13 (by rw [hm₀]; exact C.c0_kept I.frame) hj
    refine WP.seq (WP.of_runBlock ⟨tc, runc, ?_⟩)
    have Ec : Env K W SP tc := E₀.keep (by rw [hbpc, hbp₀]) (by rw [hspc, hsp₀]) hrdc hwrc
    -- The keystream block.
    have hq := srcW (s := tc) L Ec.perm (t := 80) (k := 16 * 1) (by decide)
    have a80 : w64 (W + BitVec.ofNat 32 80) = w64 W + BitVec.ofNat 64 80 := L.aW (by decide)
    have hqc : (⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ := by
      rw [a80]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    have hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩ := by
      rw [a80]; exact L.k_w.sub_right (Lay.wSub (by decide))
    have hqw : Covers [⟨w64 (W + BitVec.ofNat 32 80), 16 * 1⟩] tc.wr := by rw [a80]; exact Ec.perm.wC (by decide)
    refine WP.seq (WP.mono (ctrCall_ok v L Ec C.rounds (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbx hdi)
      fun td ⟨Ed, rdd, wrd, _, fd, od⟩ => ?_)
    -- What was written before the XOR.
    have fd' := fd
    rw [a80] at fd'
    have fbd : Frame [⟨w64 W + BitVec.ofNat 64 64, 32⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56]
        t.mem td.mem := by
      rw [← hm₀]
      refine (ft.sub fun r hr => ?_).trans (fd'.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨w64 W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨below SP 56, by simp, fun _ h => h⟩
    have fR : Frame (ctrR W SP D n) s.mem td.mem := I.frame.trans (fbd.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
    have kd : ∀ o, 96 ≤ o → o + 4 ≤ 384 → slotv td.mem W o = slotv t.mem W o := fun o h₁ h₂ =>
      fbd.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
        · exact (L.stk_w' (by omega)).symm) (by decide)
    have hbpd : td.gpr .ebp = W := Ed.ebp
    -- The XOR.
    obtain ⟨te, rune, hme, hdie, hdxe, hcxe, hbpe, hspe, hrde, hwre⟩ :=
      xorArgs_ok L Ed (P := D + BitVec.ofNat 32 (16 * (n / 16))) (t := n % 16) (by rw [kd _ (by decide) (by decide)]; exact I.dO)
        (by rw [kd _ (by decide) (by decide)]; exact I.nO)
    refine WP.seq (WP.of_runBlock ⟨te, rune, ?_⟩)
    have rde : te.rd = s.rd := by rw [hrde, rdd, hrdc, hrd₀, I.rd]
    have wre : te.wr = s.wr := by rw [hwre, wrd, hwrc, hwr₀, I.wr]
    have hw : D.toNat + 16 * (n / 16) < 2 ^ 32 := by have := C.buf.wrap; omega
    have pT : w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) := Buf.ptr hw
    have sR : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
      Offset.sub_base (w64 D) (d := 16 * (n / 16)) (n := n % 16) (k := n) (by omega)
    have xp : XorPre te (W + BitVec.ofNat 32 80) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨hdxe, hdie, hcxe, by omega, by omega, by rw [L.nW (by decide)]; have := L.fw; omega,
        by rw [toNat_add32 hw]; have := C.buf.wrap; omega, ?_, ?_, ?_⟩
      · rw [a80]; exact covers_left (Perm.wC (Ed.perm.of_eq hrde hwre) (d := 80) (n := n % 16) (by omega))
      · rw [pT, wre]; exact covers_off C.dw (by omega) (by have := C.buf.lt; omega)
      · rw [a80, pT]; exact ((C.buf.w.sub_left sR).sub_right (Lay.wSub (d := 80) (n := n % 16) (by omega))).symm
    refine WP.mono (xorLoop_ok te xp) fun tf P => ?_
    obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes te.mem (w64 (D + BitVec.ofNat 32 (16 * (n / 16))))
        (w64 (W + BitVec.ofNat 32 80)) (n % 16) := ⟨_, rfl⟩
    have hm₄ := P.mem
    rw [← hxs] at hm₄
    have hxl : xs.length = n % 16 := by simp [hxs, xorBytes, length_bytesAt]
    have fw : Frame [⟨w64 D, n⟩] te.mem tf.mem := by
      rw [hm₄, pT]
      exact writeBytes_frame _ _ _ (by
        rw [hxl]; exact Offset.contains_base (w64 D) (show 16 * (n / 16) + n % 16 ≤ n by omega)
          (by have := C.buf.lt; omega))
    refine ⟨E.keep (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hbpe, E.ebp])
        (by rw [P.other _ (by decide) (by decide) (by decide) (by decide) (by decide), hspe, E.esp])
        (by rw [P.rd, rde, I.rd]) (by rw [P.wr, wre, I.wr]), by rw [P.rd, rde], by rw [P.wr, wre], ?_, ?_⟩
    · rw [← hme] at fR
      exact fR.trans (fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    · -- The bytes.
      have dD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 64, 32⟩ : Region),
          ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
        intro a l hl r hr
        have sA : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base (w64 D) hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.w.sub_left sA).sub_right (Lay.wSub (by decide))
        · exact (C.buf.stk.sub_right sA).symm
      have h₁ : bytesAt te.mem (w64 D) (16 * (n / 16)) = bytesAt t.mem (w64 D) (16 * (n / 16)) := by
        rw [hme]
        have := Proof.AesGcm.X86.bytesAt_frame fbd (dD (a := 0) (l := 16 * (n / 16)) (by omega)) (by omega)
        rwa [BitVec.add_zero] at this
      have h₂ : bytesAt te.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
          bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
        rw [hme, Proof.AesGcm.X86.bytesAt_frame fbd (dD (by omega)) (by omega), I.rest]
      have hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem (w64 K) R) := fun x => Proof.Cmac.aesWith_length _ _ x
      have fRc : Frame (ctrR W SP D n) s.mem tc.mem := I.frame.trans (by
        rw [← hm₀]
        exact ft.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
      have hks : bytesAt te.mem (w64 W + BitVec.ofNat 64 80) 16 =
          Spec.Ccm.ctxCiph s.mem (w64 K) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1)) := by
        have hx := Proof.AesCcm.ctr32_ccm (m := tc.mem) (m' := td.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
          (D := w64 (W + BitVec.ofNat 32 80)) (R := R) (nonce := nonce) (by have := C.h13; omega) (k := 1)
          (j := n / 16 + 1) (fun i hi => by
            rw [show i = 0 by omega, Nat.add_zero]
            show Spec.Gcm.ofBytes _ = _
            rw [hcc]) od
        rw [Nat.mul_one, a80] at hx
        rw [hme, hx, hz80, C.ciph_kept fRc]
        exact Proof.AesCcm.xorFrom_zeros hBC _ _
      have ht := Proof.AesCcm.xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce (n / 16 + 1)
        (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) (by rw [length_bytesAt]; omega)
      rw [length_bytesAt, hBC] at ht
      have ht' := ht.resolve_right (by omega)
      rw [hm₄, pT, bytesAt_writeBytes_at te.mem (w64 D) xs (by rw [hxl]; omega) (by have := C.buf.lt; omega),
        List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega), List.append_nil,
        ← Proof.AesCcm.bytesAt_prefix te.mem (w64 D) hb, h₁, I.done, hxs, xorBytes, pT, a80, h₂,
        Proof.AesCcm.bytesAt_prefix te.mem (w64 W + BitVec.ofNat 64 80) (show n % 16 ≤ 16 by omega), hks, ht']
      conv => rhs; rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
      rw [Proof.Cmac.Stream.bytesAt_append, Proof.AesCcm.xorFrom_append _ _ _ (length_bytesAt _ _ _),
        Nat.add_comm 1 (n / 16)]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} {R : Nat} {nonce : List Byte} {D : BitVec 32}
    {n : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (hK : slotv s.mem W ctxO = K)
    (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hDp : slotv s.mem W dataO = D)
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    WP isa (ctr v.callee) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n = xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 1 (bytesAt s.mem (w64 D) n) :=
  seq_assoc (WP.seq (WP.mono (ctrWhole_ok v C E hK hRo hDp hlen) fun _ I => ctrTail_ok v C hK hRo hlen I))


end VG.Proof.AesCcm.X86
