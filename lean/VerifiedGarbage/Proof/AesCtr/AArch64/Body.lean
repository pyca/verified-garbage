import VerifiedGarbage.Proof.AesCtr.AArch64.Steps
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-!
# AES-CTR on AArch64: the code before the call

`pre_wp`: from AES-CBC's loop invariant for `ctrMode`
(`Proof/AesCbc/AArch64/Loop.lean`) after `k` blocks, `count` and `args`
set up a call of `vg_aes_ctr32` (AES-GCM's `CtrCall`) on the next
`mOf s₀ k` blocks: what is left, but no further than where the last 32
bits of the counter block wrap around.
-/

namespace VG.Proof.AesCtr.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCtr.AArch64
open VG.Impl.AesCbc.AArch64 (cOff)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.AArch64
open VG.Proof.AesGcm.AArch64 (CtrCall)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The blocks of the call after `k` blocks: what is left, but no further
than where the last 32 bits of the counter block wrap around. -/
def mOf (s₀ : State) (k : Nat) : Nat := min (N s₀ - k) (2 ^ 32 - (toNat (iv0 s₀) + k) % 2 ^ 32)

theorem length_iv0 (s₀ : State) : (iv0 s₀).length = 16 := Proof.Cmac.bytesAt_length _ _ _

theorem mOf_pos {s₀ : State} {k : Nat} (hk : k < N s₀) : 0 < mOf s₀ k := by
  unfold mOf; have := Nat.mod_lt (toNat (iv0 s₀) + k) (show 0 < 2 ^ 32 by decide); omega

theorem mOf_le (s₀ : State) (k : Nat) : mOf s₀ k ≤ N s₀ - k := Nat.min_le_left _ _

theorem lo32_mOf (s₀ : State) (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k ≤ 2 ^ 32 := by
  rw [AesCtr.lo32_next (length_iv0 s₀)]; unfold mOf; omega

theorem chainK_ctr (s₀ : State) {k : Nat} (hk : k ≤ N s₀) : chainK AesCtr.ctrMode s₀ k = next (iv0 s₀) k := by
  rw [chainK, AesCtr.ctrMode_chain, List.length_take, Proof.AesCbc.length_blocksAt, Nat.min_eq_left hk]

theorem cIv12 {s₀ : State} : (ivR s₀).Contains (Iv s₀ + BitVec.ofNat 64 12) 4 :=
  Offset.contains_base _ (by decide) (by decide)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.seg_wrap {k m : Nat} (hk : k < N s₀) (hkm : k + m ≤ N s₀) : (blk s₀ k).toNat + 16 * m ≤ 2 ^ 64 := by
  have := hp.data_wrap
  rw [hp.blk_toNat hk]
  omega

omit hp in
theorem UPre.seg_sub {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

/-- The arguments of the call after `k` blocks. -/
theorem UPre.ctrCall {k : Nat} (hk : k < N s₀) {s : State}
    (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = Iv s₀)
    (x3 : s.gpr .x3 = blk s₀ k) (x4 : s.gpr .x4 = BitVec.ofNat 64 (mOf s₀ k)) (x5 : s.gpr .x5 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := hp.rounds
  wrap := UPre.seg_wrap hp hk (by have := mOf_le s₀ k; omega)
  n_lt := by have := mOf_le s₀ k; have : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt; omega
  kc := hp.sch_iv
  kd := hp.sch_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))
  ks := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  cd := hp.iv_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))
  cs := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))).sub_right
    (Region.sub_prefix (by decide))
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure Pre (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  call : CtrCall s₁ (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = s.mem.writeW (S s₀ + BitVec.ofNat 64 2048) (BitVec.ofNat 64 (mOf s₀ k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

omit hp in
theorem count_eq : count ++ args = ([.ldr .w .x9 .x21 12, .rev32 .x9 .x9] : List Instr) ++
    (([.movz .x .x10 1 2, .sub .x .x10 .x10 .x9] : List Instr) ++
      (([.subs .x .x11 .x23 .x10, .csel .x .x10 .x10 .x23] : List Instr) ++
        (([.str .x .x10 .x24 cOff] : List Instr) ++ args))) := rfl

omit hp in
theorem preserved_ne3 {r : Reg} (hr : r ∈ preserved) : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pre_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block (count ++ args)) s (Pre s₀ k s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  have hb : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ⟨s₁, run₁, x9₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ := countA_ok s h.x21
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) cIv12)
  obtain ⟨s₂, run₂, x10₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ := countB1_ok s₁ x9₁
  obtain ⟨s₃, run₃, x10₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := countB2_ok s₂
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h.x23]) x10₂
  obtain ⟨s₄, run₄, gpr₄, sp₄, mem₄, rd₄, wr₄⟩ := store_ok s₃ (S := S s₀)
    (by rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide), h.x24])
    (by rw [wr₃, wr₂, wr₁, hW]; exact in_rw (by simp) cSv0)
  obtain ⟨s₅, run₅, x0₅, x1₅, x2₅, x3₅, x4₅, x5₅, cs₅, sp₅, mem₅, rd₅, wr₅⟩ := args_ok s₄
  rw [count_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  -- The number of blocks.
  have hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega)]
  have hlo := AesCtr.lo32_bytesAt s.mem (Iv s₀)
  rw [hiv, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  have hm : s₃.gpr .x10 = BitVec.ofNat 64 (mOf s₀ k) := by
    rw [x10₃]
    generalize hc : rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32) = c at hlo
    have e := AesCtr.sub32_toNat c
    have hl : (BitVec.ofNat 64 (N s₀ - k)).toNat = N s₀ - k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold mOf
    rw [e, hl, hlo]
    have hcl := c.isLt
    by_cases hlt : N s₀ - k < 2 ^ 32 - c.toNat
    · simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_left (by omega)]
    · simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_right (by omega)]
      apply BitVec.eq_of_toNat_eq
      rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have g4 (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s.gpr r := by
    have := preserved_ne3 hr
    rw [gpr₄, g₃ r this.2.1 this.2.2, g₂ r this.2.1, g₁ r this.1]
  have keep (r : Reg) (hr : r ∈ preserved) : s₅.gpr r = s.gpr r := by rw [cs₅ r hr, g4 r hr]
  refine ⟨UPre.ctrCall hp hk
    (by rw [x0₅, g4 .x19 (by simp [preserved]), h.x19]) (by rw [x1₅, g4 .x20 (by simp [preserved]), h.x20])
    (by rw [x2₅, g4 .x21 (by simp [preserved]), h.x21]) (by rw [x3₅, g4 .x22 (by simp [preserved]), h.x22])
    (by rw [x4₅, gpr₄, hm]) (by rw [x5₅, g4 .x24 (by simp [preserved]), h.x24])
    (by rw [rd₅, rd₄, rd₃, rd₂, rd₁, h.rd]) (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, h.wr]), keep,
    by rw [sp₅, sp₄, sp₃, sp₂, sp₁], ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  rw [mem₅, mem₄, hm, mem₃, mem₂, mem₁]

end

end VG.Proof.AesCtr.AArch64
