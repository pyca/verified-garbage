import VerifiedGarbage.Proof.AesCtr.X86_64.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# AES-CTR on x86-64: one call

`iter_wp`: one run of `body` takes AES-CBC's loop invariant for `ctrMode`
(`Proof/AesCbc/X86_64/Loop.lean`) from `k` blocks to `k + mOf s₀ k`, the
blocks of the call, for any implementation of `vg_aes_ctr32` (`Ctr32Impl`),
and sets ZF if no blocks are left. The call gives CTR's output on its
blocks (`AesCtr.ctr32_crypt`), and the counter block it leaves, with the
carry into the first 96 bits if its last 32 bits wrapped around, is CTR's
(`AesCtr.ctr32_next`, `AesCtr.ctr32_wrap`).
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (save setup restore at_ cOff)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesGcm.X86_64 (CtrCall CtrPost ctr_call)
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

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.seg_wrap {k m : Nat} (hk : k < N s₀) (hkm : k + m ≤ N s₀) : (blk s₀ k).toNat + 16 * m ≤ 2 ^ 64 := by
  have := hp.data_wrap
  have : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  omega

omit hp in
theorem UPre.seg_sub {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

/-- The arguments of the call after `k` blocks. -/
theorem UPre.ctrCall {k : Nat} (hk : k < N s₀) {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = Iv s₀)
    (rcx : s.gpr .rcx = blk s₀ k) (r8 : s.gpr .r8 = BitVec.ofNat 64 (mOf s₀ k)) (r9 : s.gpr .r9 = S s₀)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hp.rounds
  wrap := UPre.seg_wrap hp hk (by have := mOf_le s₀ k; omega)
  kc := hp.sch_iv
  kd := hp.sch_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))
  ks := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  cd := hp.iv_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))
  cs := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))).sub_right (Region.sub_prefix (by decide))
  stkK := by rw [rsp]; exact hp.stk_sch
  stkC := by rw [rsp]; exact hp.stk_iv
  stkD := by rw [rsp]; exact hp.stk_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega))
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
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
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = s.mem.writeW (S s₀ + BitVec.ofNat 64 2048) (BitVec.ofNat 64 (mOf s₀ k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

omit hp in
theorem count_eq : count ++ args = [.mov32 .rax (.mem (at_ .r12 12)), .bswap32 .rax] ++
    ([.movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .rax)] ++ ([.alu .cmp .r14 (.reg .rcx),
      .cmov .b .rcx (.reg .r14)] ++ ([.store (at_ .r15 cOff) .rcx] ++ args))) := rfl

theorem pre_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block (count ++ args)) s (Pre s₀ k s) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hb : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rax₁, g₁, mem₁, rd₁, wr₁⟩ := countA_ok s h.r12
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
  obtain ⟨s₂, run₂, rcx₂, g₂, mem₂, rd₂, wr₂⟩ := countB1_ok s₁ rax₁
  obtain ⟨s₃, run₃, rcx₃, g₃, mem₃, rd₃, wr₃⟩ := countB2_ok s₂
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h.r14]) rcx₂
  obtain ⟨s₄, run₄, gpr₄, mem₄, rd₄, wr₄⟩ := store_ok s₃ (S := S s₀)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.r15])
    (by rw [wr₃, wr₂, wr₁, hW]; exact in_rw (by simp) cSv0)
  obtain ⟨s₅, run₅, rdi₅, rsi₅, rdx₅, r8₅, rcx₅, r9₅, cs₅, mem₅, rd₅, wr₅⟩ := args_ok s₄
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
  have hlo := lo32_bytesAt s.mem (Iv s₀)
  rw [hiv, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  have hm : s₃.gpr .rcx = BitVec.ofNat 64 (mOf s₀ k) := by
    rw [rcx₃]
    generalize hc : rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32) = c at hlo
    have e := sub32_toNat c
    have hl : (BitVec.ofNat 64 (N s₀ - k)).toNat = N s₀ - k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold mOf
    rw [e, hl, hlo]
    have hcl := c.isLt
    by_cases hlt : N s₀ - k < 2 ^ 32 - c.toNat
    · rw [if_pos hlt, Nat.min_eq_left (by omega)]
    · rw [if_neg hlt, Nat.min_eq_right (by omega)]
      apply BitVec.eq_of_toNat_eq
      rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₅.gpr r = s.gpr r := by
    have h1 : r ≠ .rax := calleeSaved_ne_rax hr
    have h2 : r ≠ .rcx := by rintro rfl; simp [calleeSaved] at hr
    rw [cs₅ r hr, gpr₄, g₃ r h2, g₂ r h2, g₁ r h1]
  have g4 (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s.gpr r := by
    have h1 : r ≠ .rax := calleeSaved_ne_rax hr
    have h2 : r ≠ .rcx := by rintro rfl; simp [calleeSaved] at hr
    rw [gpr₄, g₃ r h2, g₂ r h2, g₁ r h1]
  refine ⟨UPre.ctrCall hp hk
    (by rw [rdi₅, g4 .rbx (by simp [calleeSaved]), h.rbx]) (by rw [rsi₅, g4 .rbp (by simp [calleeSaved]), h.rbp])
    (by rw [rdx₅, g4 .r12 (by simp [calleeSaved]), h.r12]) (by rw [rcx₅, g4 .r13 (by simp [calleeSaved]), h.r13])
    (by rw [r8₅, gpr₄, hm]) (by rw [r9₅, g4 .r15 (by simp [calleeSaved]), h.r15])
    (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₅, rd₄, rd₃, rd₂, rd₁, h.rd])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, h.wr]), keep, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  rw [mem₅, mem₄, hm, mem₃, mem₂, mem₁]

end

end VG.Proof.AesCtr.X86_64
