import VerifiedGarbage.Proof.AesCcm.X86.Aad

/-!
# AES-CCM on x86: `B₀`, the CBC-MAC and the tag (`b0 y`, `mac y`, `tag y`)

Untrusted: everything here is checked by Lean. `b0 y` builds `B₀` in `B`
from `Ctr₀` and the flags, zeroes the MAC state at `W + y` and chains `B₀`
into it (`b0_ok`); `mac y` chains the formatted associated data and payload
after it (`mac_ok`): the CBC-MAC of the formatted input (§6.1 steps 1–4);
`tag y` XORs `CIPH_K(Ctr₀)` into it (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 tglO dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv zero4_fold zero4_bytes' length_bytesAt and_self_beq32)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

/-! ## `B₀` -/

/-- The flags, without `64 [a > 0]`, and ZF for `a = 0`. -/
theorem b0Flags_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {nl al tl : Nat}
    (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (hal : al < 2 ^ 32)
    (htl : slotv s.mem W tglO = BitVec.ofNat 32 tl) (hnlv : slotv s.mem W nlenO = BitVec.ofNat 32 nl)
    (halv : slotv s.mem W alenO = BitVec.ofNat 32 al) :
    ∃ s₁, runBlock isa
      [.mov .eax (slot tglO), .alu .sub .eax (imm 2), .alu .add .eax (.reg .eax),
        .alu .add .eax (.reg .eax), .mov .ecx (imm 14), .alu .sub .ecx (slot nlenO), .alu .add .eax (.reg .ecx),
        .mov .ecx (slot alenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .eax = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl)) ∧
      s₁.zf = some (decide (al = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, htl, hnlv, halv], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [htl, hnlv]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · cmems [halv]; rw [and_self_beq32 hal]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `B₀` in `B`, and the MAC state at `W + y` zeroed. -/
theorem b0Pre_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {nonce : List Byte}
    {nl al n tl : Nat} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32)
    (htl : slotv s.mem W tglO = BitVec.ofNat 32 tl) (hnlv : slotv s.mem W nlenO = BitVec.ofNat 32 nl)
    (halv : slotv s.mem W alenO = BitVec.ofNat 32 al) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.seq (.block [.mov .eax (slot tglO), .alu .sub .eax (imm 2), .alu .add .eax (.reg .eax),
        .alu .add .eax (.reg .eax), .mov .ecx (imm 14), .alu .sub .ecx (slot nlenO), .alu .add .eax (.reg .ecx),
        .mov .ecx (slot alenO), .alu .test .ecx (.reg .ecx)])
      (.seq (.ite .e (.block []) (.block [.alu .add .eax (imm 64)]))
      (.block (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y)))) s fun s' =>
      Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
  -- The flags, without `64 [a > 0]`, and ZF for `a = 0`.
  obtain ⟨s₁, run₁, hm₁, hax₁, hzf₁, hbp₁, hsp₁, hrd₁, hwr₁⟩ := b0Flags_ok L E h13 ht4 hal htl hnlv halv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- `64 [a > 0]`.
  have hite : WP isa (.ite .e (.block []) (.block [.alu .add .eax (imm 64)])) s₁ fun s₂ =>
      s₂.mem = s.mem ∧ s₂.gpr .eax = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine WP.ite (decide (al = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : al = 0 := of_decide_eq_true ht
      exact WP.of_runBlock ⟨s₁, rfl, hm₁, by rw [hax₁, h0]; rfl, hbp₁, hsp₁, hrd₁, hwr₁⟩
    · have h0 : al ≠ 0 := of_decide_eq_false hf
      refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · cmems [hm₁]
      · cregs [hax₁, h0]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0, ↓reduceIte]
        omega
      · cregs [hbp₁]
      · cregs [hsp₁]
      · cmems [hrd₁]
      · cmems [hwr₁]
  refine WP.seq (WP.mono hite fun s₂ ⟨hm₂, hax₂, hbp₂, hsp₂, hrd₂, hwr₂⟩ => ?_)
  -- `B₀`, and the state zeroed.
  have hlen₂ : slotv s₂.mem W lenO = BitVec.ofNat 32 n := by rw [hm₂]; exact hlen
  have hf := flags_val32 (al := al) ht4 ht16 hte h7 h13
  have hz := zero4_fold (((((s.mem.writeW (w64 W + BitVec.ofNat 64 32) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).writeW
    (w64 W + BitVec.ofNat 64 36) (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32)).writeW
    (w64 W + BitVec.ofNat 64 40) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).writeW
    (w64 W + BitVec.ofNat 64 32) (Spec.Ccm.flags tl (15 - nl) al)).writeW (w64 W + BitVec.ofNat 64 44)
    (bswap (BitVec.ofNat 32 n) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32)) W y
  obtain ⟨s₃, run₃, hm₃, hbp₃, hsp₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      (([.mov .ecx (slot c0O), .store (at_ .ebp blkO) .ecx, .mov .ecx (slot (c0O + 4)),
        .store (at_ .ebp (blkO + 4)) .ecx, .mov .ecx (slot (c0O + 8)), .store (at_ .ebp (blkO + 8)) .ecx,
        .store8 (at_ .ebp blkO) .al, .mov .eax (slot lenO), .bswap .eax, .alu .or .eax (slot (c0O + 12)),
        .store (at_ .ebp (blkO + 12)) .eax] : List Instr) ++ zero4 y) s₂ = some s₃ ∧
      s₃.mem = Cmac.zero4 (((((s.mem.writeW (w64 W + BitVec.ofNat 64 32) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).writeW
        (w64 W + BitVec.ofNat 64 36) (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32)).writeW
        (w64 W + BitVec.ofNat 64 40) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).writeW
        (w64 W + BitVec.ofNat 64 32) (Spec.Ccm.flags tl (15 - nl) al)).writeW (w64 W + BitVec.ofNat 64 44)
        (bswap (BitVec.ofNat 32 n) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32)) (w64 W + BitVec.ofNat 64 y) ∧
      s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [zero4, hbp₂, L.aW, E.perm.wW, E.perm.wR, hrd₂, hwr₂, hm₂, hlen₂], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hm₂, hax₂, hf, hlen, ← hz]
    · cregs [hbp₂]
    · cregs [hsp₂]
    all_goals cmems []
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have E₃ : Env K W SP s₃ := ⟨hbp₃, hsp₃, E.perm.of_eq (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂])⟩
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = ((((s.mem.writeW (w64 W + BitVec.ofNat 64 32) (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).writeW
      (w64 W + BitVec.ofNat 64 36) (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32)).writeW
      (w64 W + BitVec.ofNat 64 40) (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).writeW
      (w64 W + BitVec.ofNat 64 32) (Spec.Ccm.flags tl (15 - nl) al)).writeW (w64 W + BitVec.ofNat 64 44)
      (bswap (BitVec.ofNat 32 n) ||| s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) := ⟨_, rfl⟩
  rw [← hmB] at hm₃
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains (w64 W) h₁ (by omega) (by decide)
  have fB : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩] s.mem mB := by
    rw [hmB]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 36 4 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 4 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide)) |>.writeW
      (List.mem_singleton_self _) _ (cB 44 4 (by decide) (by decide))
  have dYB : (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨E₃, by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂], ?_, ?_, ?_⟩
  · rw [hm₃]
    exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  · rw [hm₃, zero4_bytes']; rfl
  · -- `B₀`.
    have fZ : Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩] mB (Cmac.zero4 mB (w64 W + BitVec.ofNat 64 y)) :=
      Cmac.frame_store4 _ _ _ _ _
    rw [hm₃, Proof.AesGcm.X86.bytesAt_frame fZ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dYB) (by decide), hmB]
    rw [show w64 W + BitVec.ofNat 64 36 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 4 by rw [add_ofNat_assoc],
      show w64 W + BitVec.ofNat 64 40 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
      show w64 W + BitVec.ofNat 64 44 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 12 by rw [add_ofNat_assoc],
      b0_bytes]
    have e := bytesAt_words s.mem (w64 W) 48
    simp only [Nat.reduceAdd] at e
    rw [hc0] at e
    have l12 : (le4 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32) ++ le4 (s.mem.readW (w64 W + BitVec.ofNat 64 52) 32) ++
        le4 (s.mem.readW (w64 W + BitVec.ofNat 64 56) 32)).length = 12 := by
      simp only [List.length_append, Proof.Cmac.length_le4]
    have hw : le4 (s.mem.readW (w64 W + BitVec.ofNat 64 60) 32) = (Spec.Ccm.ctrBlock nonce 0).drop 12 := by
      rw [e, List.drop_left' l12]
    have h7' : 7 ≤ nonce.length := by omega
    have h13' : nonce.length ≤ 13 := by omega
    rw [show bswap (BitVec.ofNat 32 n) = byteRev32 (BitVec.ofNat 32 n) from rfl,
      ctr_or32 h7' h13' hw (by rw [hnl]; exact hn) hn32]
    have hb0 : Spec.Ccm.b0 tl nonce al n = Spec.Ccm.flags tl (15 - nl) al :: (Spec.Ccm.ctrBlock nonce n).drop 1 := by
      simp [Spec.Ccm.b0, Spec.Ccm.ctrBlock, hnl]
    have ht : (Spec.Ccm.ctrBlock nonce n).take 12 = (Spec.Ccm.ctrBlock nonce 0).take 12 := ctrBlock_take12 h7' h13' hn32
    rw [hb0]
    conv_rhs => rw [← List.take_append_drop 12 (Spec.Ccm.ctrBlock nonce n)]
    rw [ht, e, List.take_left' l12, List.drop_append_of_le_length (by rw [l12]; decide)]
    simp only [List.cons_append, List.append_assoc, List.drop_append_of_le_length
      (show 1 ≤ (le4 (s.mem.readW (w64 W + BitVec.ofNat 64 48) 32)).length by rw [Proof.Cmac.length_le4]; decide)]

/-- The slots, after code that writes only `macR`. -/
theorem Slots.macR {K W SP : BitVec 32} (L : Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (hf : Frame (macR W SP y) m m') {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat}
    (S : Slots W K R N A D T nl al n tl m) : Slots W K R N A D T nl al n tl m' :=
  ⟨by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.ctx,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.rounds,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.nonce,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.nlen,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.aad,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.alen,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.data,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.len,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.tl,
    by rw [slot_kept L hy hf (by decide) (by decide)]; exact S.tp⟩

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D T : BitVec 32} {nl al n tl : Nat} (S : Slots W K R N A D T nl al n tl s.mem)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 v.callee v.suffix y) s fun s' => Env K W SP s' ∧ Frame (macR W SP y) s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n] ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine seq_assoc3 (WP.seq (WP.mono (b0Pre_ok L E hnl h7 h13 ht4 ht16 hte hal hn hn32 S.tl S.nlen S.alen S.len hc0 hy)
    fun s₃ ⟨E₃, rd₃, wr₃, f₃, hz, hB⟩ => ?_))
  have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · rcases hy with rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok v L E₃ hR (by rw [k₃ _ (by decide) (by decide)]; exact S.ctx)
    (by rw [k₃ _ (by decide) (by decide)]; exact S.rounds) hy) fun s₄ ⟨E₄, hrd₄, hwr₄, f₄, h₄⟩ =>
    ⟨E₄, ?_, ?_, by rw [hrd₄, rd₃], by rw [hwr₄, wr₃]⟩
  · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_mac (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_mac (by simp)
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact sub_mac (by simp)
  · rw [h₄, hz, hB, ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Lay.wSub (by omega))) hRb]

/-! ## The CBC-MAC -/

/-- The data, as the string to chain: its address and length at `dO`, `nO`. -/
theorem dataArgs_ok {K W SP : BitVec 32} {s₂ : State} (L : Lay K W SP) (E₂ : Env K W SP s₂) {D : BitVec 32} {n : Nat}
    (hD : slotv s₂.mem W dataO = D) (hn : slotv s₂.mem W lenO = BitVec.ofNat 32 n) :
    ∃ s₃, runBlock isa
      [.mov .eax (slot dataO), .store (at_ .ebp dO) .eax, .mov .eax (slot lenO), .store (at_ .ebp nO) .eax] s₂ =
        some s₃ ∧
      s₃.mem = (s₂.mem.writeW (w64 W + BitVec.ofNat 64 dO) D).writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 n) ∧
      s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
  refine ⟨_, by crun [E₂.ebp, L.aW, E₂.perm.wW, E₂.perm.wR, hD, hn], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hD, hn]
  · cregs [E₂.ebp]
  · cregs [E₂.esp]
  all_goals cmems []


/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D T : BitVec 32} {nl al n tl : Nat} (S : Slots W K R N A D T nl al n tl s.mem)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn : n < 256 ^ (15 - nl)) (hn32 : n < 2 ^ 32)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : Buf W SP s A al) (hD : Buf W SP s D n) :
    WP isa (mac v.callee v.suffix y) s (Absorbed K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem (w64 A) al) (bytesAt s.mem (w64 D) n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega
  refine WP.seq (WP.mono (b0_ok v L E hR S hnl h7 h13 ht4 ht16 hte hal hn hn32 hc0 hy)
    fun s₁ ⟨E₁, f₁, h₁, hrd₁, hwr₁⟩ => ?_)
  have S₁ := S.macR L hy f₁
  refine WP.seq (WP.mono (aad_ok v L E₁ hR S₁.ctx S₁.rounds hy S₁.aad S₁.alen (hA.of_eq hrd₁ hwr₁) hal)
    fun s₂ M₂ => ?_)
  have S₂ := S₁.macR L hy M₂.frame
  have E₂ := M₂.env
  obtain ⟨s₃, run₃, hm₃, hbp, hsp, hrd₃, hwr₃⟩ := dataArgs_ok L E₂ S₂.data S₂.len
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env K W SP s₃ := E₂.keep (by rw [hbp, E₂.ebp]) (by rw [hsp, E₂.esp]) hrd₃ hwr₃
  have f₃ : Frame [wC W] s₂.mem s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have fm₃ : Frame (macR W SP y) s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
  have S₃ := S₂.macR L hy fm₃
  have rd₃ : s₃.rd = s.rd := by rw [hrd₃, M₂.rd, hrd₁]
  have wr₃ : s₃.wr = s.wr := by rw [hwr₃, M₂.wr, hwr₁]
  have hd₃ : slotv s₃.mem W dO = D := by
    rw [hm₃, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have hn₃ : slotv s₃.mem W nO = BitVec.ofNat 32 n := by rw [hm₃]; exact Mem.readW_writeW_self32 _ _ _
  refine WP.mono (absorbPad_ok v L E₃ hR S₃.ctx S₃.rounds hy (fun _ => hD.of_eq rd₃ wr₃) hn32 hd₃ hn₃) fun s₄ A₄ => ?_
  have f₂ : Frame (macR W SP y) s.mem s₂.mem := f₁.trans M₂.frame
  have hk := k_macR L hy16
  have hY₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s₂.mem (w64 W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  refine ⟨A₄.env, (f₂.trans fm₃).trans A₄.frame, ?_, by rw [A₄.rd, rd₃], by rw [A₄.wr, wr₃]⟩
  have hl : nonce.length ≤ 15 := by omega
  rw [A₄.out, hY₃, M₂.out, h₁, ctxCiph_frame (f₂.trans fm₃) hk hRb, ctxCiph_frame f₁ hk hRb,
    buf_kept hD hy16 (f₂.trans fm₃), buf_kept hA hy16 f₁, Proof.AesCcm.format_eq tl hl, length_bytesAt,
    length_bytesAt, Proof.Cmac.chain_append, Proof.Cmac.chain_append]

/-! ## The tag -/

/-- The arguments of the call of `vg_aes_ctr32` making the tag: `Ctr₀` at
`W + 64`. -/
theorem tagArgs_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) (y : Nat) :
    ∃ s₃, runBlock isa (([.mov .eax (imm 0)] : List Instr) ++ ctrAt ++ keyArgs c1O ++
        ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s = some s₃ ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (w64 W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 ∧
      s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr := by
  obtain ⟨s₁, run₁, hm₁, hax₁, hbp₁, hsp₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .eax (imm 0)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .eax = BitVec.ofNat 32 0 ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs []
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp₁, E.ebp]) (by rw [hsp₁, E.esp]) hrd₁ hwr₁
  obtain ⟨s₂, run₂, f₂, hc₂, hg₂, hrd₂, hwr₂⟩ :=
    ctrAt_ok L E₁ h7 h13 (by rw [hm₁]; exact hc0) (Nat.pow_pos (by decide)) (by decide) hax₁
  have hbp₂ : s₂.gpr .ebp = W := by rw [hg₂ _ (by decide) (by decide), hbp₁]
  have hsp₂ : s₂.gpr .esp = SP := by rw [hg₂ _ (by decide) (by decide), hsp₁]
  have k₂ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₂.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
    rw [← hm₁]
    exact f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  have hK₂ : slotv s₂.mem W ctxO = K := by rw [k₂ _ (by decide) (by decide)]; exact hK
  have hR₂ : slotv s₂.mem W roundsO = BitVec.ofNat 32 R := by rw [k₂ _ (by decide) (by decide)]; exact hRo
  have E₂ : Env K W SP s₂ := E₁.keep (by rw [hbp₂, hbp₁]) (by rw [hsp₂, hsp₁]) hrd₂ hwr₂
  obtain ⟨s₃, run₃, hm₃, hax, hcx, hdx, hbx, hdi, hbp₃, hsp₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      (keyArgs c1O ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm y), .mov .edi (imm 1)] : List Instr)) s₂ = some s₃ ∧
      s₃.mem = s₂.mem ∧ s₃.gpr .eax = K ∧ s₃.gpr .ecx = BitVec.ofNat 32 R ∧ s₃.gpr .edx = W + BitVec.ofNat 32 64 ∧
      s₃.gpr .ebx = W + BitVec.ofNat 32 y ∧ s₃.gpr .edi = BitVec.ofNat 32 1 ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [keyArgs, hbp₂, L.aW, E₂.perm.wR, hK₂, hR₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hK₂]
    · cregs [hR₂]
    · cregs [hbp₂]
    · cregs [hbp₂]
    · cregs []
    · cregs [hbp₂]
    · cregs [hsp₂]
    all_goals cmems []
  refine ⟨s₃, by
    rw [List.append_assoc]
    exact Proof.AesGcm.X86.runBlock_app_of (Proof.AesGcm.X86.runBlock_app_of run₁ run₂) run₃,
    by rw [hm₃, ← hm₁]; exact f₂, by rw [hm₃]; exact hc₂, hax, hcx, hdx, hbx, hdi, hbp₃, hsp₃,
    by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁]⟩

/-- The arguments of `tag`'s call, as `ctrCall_ok` and `ctrCall_ct` take them. -/
theorem tagCall_pre {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {y : Nat}
    (hy : y = 0 ∨ y = 96) :
    Src W SP s (W + BitVec.ofNat 32 y) (16 * 1) ∧ Covers [⟨w64 (W + BitVec.ofNat 32 y), 16 * 1⟩] s.wr ∧
      (⟨w64 (W + BitVec.ofNat 32 y), 16 * 1⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 64, 16⟩ ∧
      (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 (W + BitVec.ofNat 32 y), 16 * 1⟩ := by
  have hy' : y + 16 ≤ 384 := by rcases hy with rfl | rfl <;> decide
  have aY : w64 (W + BitVec.ofNat 32 y) = w64 W + BitVec.ofNat 64 y := L.aW (by omega)
  refine ⟨srcW L E.perm (t := y) (k := 16 * 1) (by omega), by rw [aY]; exact E.perm.wC (by omega), ?_,
    by rw [aY]; exact L.k_w.sub_right (Lay.wSub (by omega))⟩
  rw [aY]
  rcases hy with rfl | rfl
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)

/-- The MAC state at `W + y` XORed with `CIPH_K(Ctr₀)`. -/
theorem tag_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (tag v.callee y) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem (w64 K) R) nonce 0 (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16) := by
  obtain ⟨s₃, run₃, f₃, hc₃, hax, hcx, hdx, hbx, hdi, hbp₃, hsp₃, hrd₃, hwr₃⟩ :=
    tagArgs_ok L E hK hRo h7 h13 hc0 y
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env K W SP s₃ := E.keep (by rw [hbp₃, E.ebp]) (by rw [hsp₃, E.esp]) hrd₃ hwr₃
  have aY : w64 (W + BitVec.ofNat 32 y) = w64 W + BitVec.ofNat 64 y := L.aW (by omega)
  obtain ⟨hq, hqw, hqc, hqk⟩ := tagCall_pre L E₃ hy
  refine WP.mono (ctrCall_ok v L E₃ hR (c := 64) (by decide) hq hqc hqk hqw hax hcx hdx hbx hdi)
    fun s₄ ⟨E₄, rd₄, wr₄, _, f₄, o₄⟩ => ⟨E₄, by rw [rd₄, hrd₃], by rw [wr₄, hwr₃], ?_, ?_⟩
  · have f₄' := f₄
    rw [aY] at f₄'
    refine (f₃.sub fun r hr => ?_).trans (f₄'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 y, 16⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    have hc := Proof.AesCcm.ctr32_ccm (m := s₃.mem) (m' := s₄.mem) (K := w64 K) (C := w64 W + BitVec.ofNat 64 64)
      (D := w64 (W + BitVec.ofNat 32 y)) (R := R) (nonce := nonce) (by omega) (j := 0) (k := 1)
      (fun i hi => by
        rw [show i = 0 by omega, Nat.zero_add]
        show Spec.Gcm.ofBytes _ = _
        rw [hc₃]) o₄
    rw [Nat.mul_one, aY] at hc
    rw [hc, ctxCiph_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb,
      Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← aY]; exact hqc) (by decide)]

end VG.Proof.AesCcm.X86
