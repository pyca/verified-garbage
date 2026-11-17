module

import VerifiedGarbage.Proof.AesCtr.Arm.Steps
public import VerifiedGarbage.Proof.AesCbc.Arm.CT
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.AesCtr.Ctr32
public import VerifiedGarbage.Proof.AesGcm.Arm.Callee
public import VerifiedGarbage.Impl.AesCtr.Arm
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesCtr.Arm.Steps
meta import VerifiedGarbage.Proof.AesCbc.Arm.CT
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesGcm.Arm.Callee
meta import VerifiedGarbage.Impl.AesCtr.Arm
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-CTR on ARMv7: one call of `vg_aes_ctr32`, and the whole function

`iter_wp`: one run of `body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/Arm/Loop.lean`), for `ctrMode`, from `k` blocks to
`k + mOf s₀ k`: `count` and `args` set up a call of `vg_aes_ctr32`
(AES-GCM's `CtrCall`) on the next `mOf s₀ k` blocks, what is left but no
further than where the last 32 bits of the counter block wrap around; the
call gives CTR's output on them (`AesCtr.ctr32_crypt`), and the counter block
it leaves, with the carry into the first 96 bits if its last 32 bits wrapped
around, is CTR's (`AesCtr.ctr32_next`, `AesCtr.ctr32_wrap`). `crypt_wp`: the
whole function, with AES-CBC's prologue and epilogue.
-/

@[expose] public section

namespace VG.Proof.AesCtr.Arm

open VG VG.Arm VG.Impl.AesCtr.Arm
open VG.Impl.CmacAes.Arm (save setup restore)
open VG.Impl.AesCbc.Arm (whole)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem add0)
open VG.Proof.AesGcm.Arm (below CtrCall CtrPost ctr_call ctr_rel)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_cmp cmp0 eval_eq eval_ne sub_ofNat)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The blocks of the call after `k` blocks: what is left, but no further
than where the last 32 bits of the counter block wrap around. -/
def mOf (s₀ : State) (k : Nat) : Nat := min (N s₀ - k) (2 ^ 32 - (toNat (iv0 s₀) + k) % 2 ^ 32)

theorem length_iv0 (s₀ : State) : (iv0 s₀).length = 16 := Proof.Cmac.bytesAt_length _ _ _

theorem mOf_pos {s₀ : State} {k : Nat} (hk : k < N s₀) : 0 < mOf s₀ k := by
  unfold mOf
  have hm := Nat.mod_lt (toNat (iv0 s₀) + k) (show 0 < 2 ^ 32 by decide)
  omega_using [hk, hm]

theorem mOf_le (s₀ : State) (k : Nat) : mOf s₀ k ≤ N s₀ - k := Nat.min_le_left _ _

theorem lo32_mOf (s₀ : State) (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k ≤ 2 ^ 32 := by
  rw [AesCtr.lo32_next (length_iv0 s₀)]; unfold mOf; omega_using []

theorem chainK_ctr (s₀ : State) {k : Nat} (hk : k ≤ N s₀) : chainK AesCtr.ctrMode s₀ k = next (iv0 s₀) k := by
  rw [chainK, AesCtr.ctrMode_chain, List.length_take, Proof.AesCbc.length_blocksAt, Nat.min_eq_left hk]

theorem N_lt (s₀ : State) : N s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt

theorem UPre.seg_sub {s₀ : State} {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hkm])

/-- The arguments of the call after `k` blocks. -/
theorem UPre.ctrCall {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = Iv s₀)
    (r3 : s.gpr .r3 = D32 s₀ k) (r12 : s.gpr .r12 = BitVec.ofNat 32 (mOf s₀ k)) (lr : s.gpr .lr = S s₀)
    (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (D32 s₀ k) (S s₀) (R s₀) (mOf s₀ k) := by
  obtain hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  obtain hd := hp.dataA hk
  obtain qN := hp.dataN hk
  have hsc := hp.scr_fit
  have hdf := hp.data_fit
  have hle := mOf_le s₀ k
  obtain seg : Region.Sub ⟨blk s₀ k, 16 * mOf s₀ k⟩ (dataR s₀) := UPre.seg_sub (by omega_using [hk, hle])
  refine ⟨r0, by rw [r1]; simp [R], r2, r3, r12, lr, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit, hp.iv_fit,
    by rw [qN]; omega_using [hk, hle, hdf], by omega_using [hsc], hp.sch_iv, by rw [hd]; exact hp.sch_data.sub_right seg,
    hp.sch_scr.sub_right (Region.sub_prefix (by decide)), by rw [hd]; exact hp.iv_data.sub_right seg,
    hp.iv_scr.sub_right (Region.sub_prefix (by decide)),
    by rw [hd]; exact (hp.data_scr.sub_left seg).sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_sch, by rw [hb]; exact hp.b_iv, by rw [hb, hd]; exact hp.b_data.sub_right seg,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega_using [hk, hle]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-! ## The code before the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  call : CtrCall s₁ (W s₀) (Iv s₀) (D32 s₀ k) (S s₀) (R s₀) (mOf s₀ k)
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  r9 : s₁.gpr .r9 = BitVec.ofNat 32 (mOf s₀ k)
  sp : s₁.sp = s.sp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem args_eq : args = [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r6), .mov .r3 (.reg .r7),
    .mov .r12 (.reg .r9), .mov .lr (.reg .r10)] := rfl

theorem pre_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv AesCtr.ctrMode s₀ k s) : WP isa (.block (count ++ args)) s (PreA s₀ k s) := by
  have hiv := hp.iv_fit
  obtain rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₁, run₁, r9₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ := count_ok s (Q := State.addr (Iv s₀)) (by rw [h.r6])
    (by rw [h.r6]; exact hiv)
    (by rw [rw₀]; exact ⟨ivR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [args_eq]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    WP.block_nil ?_
  -- The number of blocks.
  have hN := N_lt s₀
  have hle := mOf_le s₀ k
  obtain hivb : bytesAt s.mem (State.addr (Iv s₀)) 16 = next (iv0 s₀) k := by
    rw [h.iv, chainK_ctr s₀ (by omega_using [hk])]
  have hlo := AesCtr.lo32_bytesAt s.mem (State.addr (Iv s₀))
  rw [hivb, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  obtain hm : s₁.gpr .r9 = BitVec.ofNat 32 (mOf s₀ k) := by
    rw [r9₁, h.r8]
    apply BitVec.eq_of_toNat_eq
    have hl : (BitVec.ofNat 32 (N s₀ - k)).toNat = N s₀ - k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hN])]
    rw [mWord_toNat _ _ (by rw [hl]; omega_using [hk]), hl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hN, hle])]
    unfold mOf
    rw [hlo]
    rfl
  have g7 (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h12 : r ≠ .r12)
      (hlr : r ≠ .lr) : s₇.gpr r = s₁.gpr r := by
    rw [u₇.other _ hlr, u₆.other _ h12, u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, u₂.other _ h0]
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r12 → r ≠ .lr → s₇.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h9 h12 hlr => by rw [g7 r h0 h1 h2 h3 h12 hlr, g₁ r h0 h1 h2 h3 h9]
  have sp₇ : s₇.sp = s.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  refine ⟨UPre.ctrCall hp hk ?_ ?_ ?_ ?_ ?_ ?_ (by rw [sp₇, h.sp]) (by rw [rd₇, h.rd]) (by rw [wr₇, h.wr]), keep,
    by rw [g7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hm], sp₇,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁], rd₇, wr₇⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r6]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r7]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), hm]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]

/-! ## The call -/

/-- The registers the invariant pins, with the call's number of blocks in
`r9`. -/
structure MRegs (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = Iv s₀
  r7 : s.gpr .r7 = D32 s₀ k
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (mOf s₀ k)
  r10 : s.gpr .r10 = S s₀
  r11 : s.gpr .r11 = s₀.gpr .r11
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the call leaves, after `k` blocks. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : MRegs s₀ k s
  frame : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) =
    outK AesCtr.ctrMode s₀ (k + mOf s₀ k) ++ (blks s₀).drop (k + mOf s₀ k)
  /-- The counter block: `t + k + m`, less `2³²` if its last 32 bits
  wrapped around. -/
  iv : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k < 2 ^ 32 →
    bytesAt s.mem (State.addr (Iv s₀)) 16 = next (iv0 s₀) (k + mOf s₀ k)
  ivw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32 →
    bytesAt s.mem (State.addr (Iv s₀)) 16 = ofNat (toNat (next (iv0 s₀) k) + mOf s₀ k - 2 ^ 32) 16

theorem ctrFrame_eq : ctrFrame = Impl.AesGcm.Arm.ctrFrame := rfl

/-- The call, after the code before it. -/
theorem mid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    (h : LInv AesCtr.ctrMode s₀ k s) (a : PreA s₀ k s s₁) : WP isa ctrFrame s₁ (Mid s₀ k) := by
  rw [ctrFrame_eq]
  refine WP.mono (ctr_call a.call) fun s₂ c => ?_
  have g (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) (h9 : r ≠ .r9) : s₂.gpr r = s.gpr r := by
    rw [c.saved r hr hlr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hlr
      | exact absurd rfl h9
      | exact a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain r9₂ : s₂.gpr .r9 = BitVec.ofNat 32 (mOf s₀ k) := by
    rw [c.saved .r9 (by simp [preserved]) (by decide), a.r9]
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  have hdf := hp.data_fit
  obtain hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  obtain hD : State.addr (D32 s₀ k) = blk s₀ k := hp.dataA hk
  obtain fc₀ := c.frame
  obtain co := c.out
  obtain cc := c.ctr
  rw [hb, hD, a.mem] at fc₀
  rw [hD, a.mem] at co
  rw [a.mem] at cc
  generalize hmd : mOf s₀ k = m at hm0 hle fc₀ co cc
  obtain segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := UPre.seg_sub (by omega_arith)
  have fc : Frame [ivR s₀, ⟨blk s₀ k, 16 * m⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s.mem s₂.mem := fc₀
  obtain fAll : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem :=
    fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨belowR s₀, by simp, fun _ h => h⟩
  obtain hiv : bytesAt s.mem (State.addr (Iv s₀)) 16 = next (iv0 s₀) k := by
    rw [h.iv, chainK_ctr s₀ (by omega_arith)]
  obtain sched : bytesAt s.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) = wK s₀ :=
    UPre.sched_bytes hp (UPre.big_of h.frame)
  obtain hlen : (blks s₀).length = N s₀ := Proof.AesCbc.length_blocksAt _ _ _
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [ivR s₀, ⟨blk s₀ k, 16 * m⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀],
        (⟨State.addr (Dp s₀) + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    obtain dj : Region.Sub ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) :=
      Offset.sub_base _ (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_data.symm.sub_left dj
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.data_scr.sub_left dj).sub_right (Region.sub_prefix (by decide))
    · exact hp.b_data.symm.sub_left dj
  have keepBlocks {p : Addr} {a n : Nat} (hp' : p = State.addr (Dp s₀) + BitVec.ofNat 64 (16 * a))
      (hn : a + n ≤ N s₀) (ho : a + n ≤ k ∨ k + m ≤ a) :
      Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    exact AesCtr.blocksAt_frame fc fun j hj r hr => by
      rw [Offset.add_add, show 16 * a + 16 * j = 16 * (a + j) by omega_arith]
      exact outside (a + j) (by omega_arith) (by omega_arith) r hr
  have dataS := h.data
  rw [outK, AesCtr.ctrMode_out] at dataS
  -- The call's blocks.
  obtain segIn : Spec.Cbc.blocksAt s.mem (blk s₀ k) m = ((blks s₀).drop k).take m := by
    rw [← AesCtr.blocksAt_take _ _ (show m ≤ N s₀ - k by omega_arith), ← AesCtr.blocksAt_drop _ _ (by omega_arith),
      dataS, List.drop_left' (by rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)])]
  obtain seg := AesCtr.ctr32_crypt (k := m) (by rw [hiv, ← hmd]; exact lo32_mOf s₀ k) co
  rw [sched, hiv, segIn] at seg
  refine ⟨⟨by rw [g _ (by simp [preserved]) (by decide) (by decide), h.r4],
    by rw [g _ (by simp [preserved]) (by decide) (by decide), h.r5],
    by rw [g _ (by simp [preserved]) (by decide) (by decide), h.r6],
    by rw [g _ (by simp [preserved]) (by decide) (by decide), h.r7],
    by rw [g _ (by simp [preserved]) (by decide) (by decide), h.r8], r9₂,
    by rw [g _ (by simp [preserved]) (by decide) (by decide), h.r10],
    by rw [g _ (by simp [preserved]) (by decide) (by decide), h.r11],
    by rw [c.sp, a.sp, h.sp], by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr]⟩,
    h.frame.trans fAll, ?_, ?_, ?_⟩
  · -- The data: the first `k` blocks and those after the call's as they were, and the call's.
    obtain hlc : (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k)).length = k := by
      rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)]
    obtain hA : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) k =
        Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k) := by
      rw [← AesCtr.blocksAt_take _ _ (show k ≤ N s₀ by omega_arith), dataS, List.take_left' hlc]
    obtain hC : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * (k + m))) (N s₀ - (k + m)) =
        (blks s₀).drop (k + m) := by
      rw [← AesCtr.blocksAt_drop _ _ (show k + m ≤ N s₀ by omega_arith), dataS]
      conv => lhs; rw [show k + m = (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀)
        ((blks s₀).take k)).length + m by rw [hlc]]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega_arith), List.nil_append, hlc, Nat.add_sub_cancel_left]
      exact List.drop_drop
    rw [hmd, AesCtr.blocksAt_three s₂.mem (State.addr (Dp s₀)) (a := k) (b := m) (by omega_arith),
      keepBlocks (a := 0) (by simp) (by omega_arith) (by omega_arith),
      keepBlocks (a := k + m) rfl (by omega_arith) (by omega_arith),
      show State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k) = blk s₀ k from rfl, seg, hA, hC, outK,
      AesCtr.ctrMode_out]
    exact AesCtr.crypt_step _ _ _ (by omega_arith)
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_next (by rw [hiv]; omega_arith) cc, hiv, AesCtr.next_add]
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_wrap (by rw [hiv]; omega_arith) cc, hiv]

/-! ## After the call -/

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {s₀ : State} (hp : UPre s₀) {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid s₀ k s)
    (hmd : mOf s₀ k = m)
    (g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → s'.gpr r = s.gpr r)
    (r7 : s'.gpr .r7 = D32 s₀ (k + m)) (r8 : s'.gpr .r8 = BitVec.ofNat 32 (N s₀ - (k + m)))
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (State.addr (Iv s₀)) 16 = next (iv0 s₀) (k + m)) :
    LInv AesCtr.ctrMode s₀ (k + m) s' where
  r4 := by rw [g .r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r4]
  r5 := by rw [g .r5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r5]
  r6 := by rw [g .r6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r6]
  r7 := r7
  r8 := r8
  r10 := by rw [g .r10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r10]
  r11 := by rw [g .r11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r11]
  sp := by rw [hsp, h.regs.sp]
  rd := by rw [hrd, h.regs.rd]
  wr := by rw [hwr, h.regs.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    have hdf := hp.data_fit
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm.sub_left (Offset.sub_base _ (by omega_arith))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

/-- What `adv` leaves. -/
structure After (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  gpr : ∀ r, r ≠ .r0 → r ≠ .r7 → r ≠ .r8 → s₂.gpr r = s.gpr r
  r7 : s₂.gpr .r7 = D32 s₀ (k + mOf s₀ k)
  r8 : s₂.gpr .r8 = BitVec.ofNat 32 (N s₀ - (k + mOf s₀ k))
  sp : s₂.sp = s.sp
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  wrap : isa.eval .eq s₂ = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32))

/-- On past the call's blocks, with the counter's last 32 bits tested. -/
theorem adv_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) :
    WP isa (.block adv) s (After s₀ k s) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain hlo := lo32_mOf s₀ k
  have hdf := hp.data_fit
  have hN := N_lt s₀
  obtain hR : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.regs.rd, h.regs.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₂, run₂, r8₂, r7₂, z₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ := adv_ok s (Q := State.addr (Iv s₀))
    (by rw [h.regs.r6]) (by rw [h.regs.r6]; exact hp.iv_fit)
    (by rw [hR]; exact ⟨ivR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine ⟨g₂, ?_, ?_, sp₂, mem₂, rd₂, wr₂, ?_⟩
  · have e : (BitVec.ofNat 32 (mOf s₀ k) <<< 4 : BitVec 32) = BitVec.ofNat 32 (16 * mOf s₀ k) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_arith
    rw [r7₂, h.regs.r7, h.regs.r9, e, D32, D32, Offset.add_add_eq _ (c := 16 * (k + mOf s₀ k)) (by omega_arith)]
  · rw [r8₂, h.regs.r8, h.regs.r9, sub_ofNat (by omega_arith), Nat.sub_sub]
  · show VG.Arm.eval .eq s₂ = _
    rw [eval_eq, z₂]
    obtain hlo2 := AesCtr.lo32_bytesAt s.mem (State.addr (Iv s₀))
    obtain hb := AesCtr.toNat_lt (show (next (iv0 s₀) k).length = 16 by
      rw [AesCtr.next_eq (length_iv0 s₀)]; exact AesCtr.length_ofNat _ _)
    by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
    · have e := h.ivw hw
      rw [e, AesCtr.lo32, AesCtr.toNat_ofNat] at hlo2
      have hw' := hw
      unfold AesCtr.lo32 at hw'
      have z0 : (AesCtr.rv32 (s.mem.readW (State.addr (Iv s₀) + BitVec.ofNat 64 12) 32)).toNat = 0 := by
        rw [← hlo2]; omega_arith
      obtain h0 := AesCtr.rv32_eq_zero.mp (BitVec.eq_of_toNat_eq z0)
      simp [h0, hw]
    · have e := h.iv (by omega_arith)
      rw [e, AesCtr.lo32_next (length_iv0 s₀)] at hlo2
      rw [AesCtr.lo32_next (length_iv0 s₀)] at hw hlo
      have nz : (AesCtr.rv32 (s.mem.readW (State.addr (Iv s₀) + BitVec.ofNat 64 12) 32)).toNat ≠ 0 := by
        rw [← hlo2]; omega_arith
      obtain h0 : s.mem.readW (State.addr (Iv s₀) + BitVec.ofNat 64 12) 32 ≠ 0 := fun h0 => nz (by rw [h0]; rfl)
      rw [AesCtr.lo32_next (length_iv0 s₀)]
      simp only [hw, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
      have z' (x : BitVec 32) : x - 0 = x := by simp
      rw [z']
      exact h0

/-- The carry if the counter wrapped around. -/
theorem fin_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State} (h : Mid s₀ k s)
    (a : After s₀ k s s₂) :
    WP isa (.ite .eq (.block carry) (.block [])) s₂ (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain hR : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.regs.rd, h.regs.wr, hp.rd, hp.wr]; rfl
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.regs.wr, hp.wr]
  obtain r6₂ : s₂.gpr .r6 = Iv s₀ := by rw [a.gpr _ (by decide) (by decide) (by decide), h.regs.r6]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · refine WP.ite true (by rw [a.wrap]; simp [hw]) (fun _ => ?_) (fun h => by cases h)
    obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := carry_ok s₂ (Q := State.addr (Iv s₀)) (by rw [r6₂])
      (by rw [r6₂]; exact hp.iv_fit)
      (fun d n hdn => by
        rw [a.rd, a.wr, hR]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega_arith)⟩)
      (fun d n hdn => by
        rw [a.wr, hW]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega_arith)⟩)
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    refine finish hp (by omega_arith) h rfl
      (fun r h0 h1 h2 h7 h8 h12 => by rw [g₃ r h0 h1 h2 h12, a.gpr r h0 h7 h8])
      (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), a.r7])
      (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), a.r8])
      (by rw [sp₃, a.sp]) (by rw [rd₃, a.rd]) (by rw [wr₃, a.wr])
      (by rw [mem₃, a.mem]; exact carryMem_frame _ _) ?_
    rw [mem₃, carryMem_bytes, a.mem, h.ivw hw]
    exact AesCtr.carry_next (length_iv0 s₀) hw
  · refine WP.ite false (by rw [a.wrap]; simp [hw]) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    exact finish hp (by omega_arith) h rfl (fun r h0 _ _ h7 h8 _ => a.gpr r h0 h7 h8) a.r7 a.r8 a.sp a.rd a.wr
      (by rw [a.mem]; exact Frame.refl _ _) (by rw [a.mem, h.iv (by have := lo32_mOf s₀ k; omega_arith)])

/-- Z set if no blocks are left. -/
theorem test_wp {s₀ : State} {j : Nat} {s : State} (h : LInv AesCtr.ctrMode s₀ j s) :
    WP isa (.block test) s fun s' => LInv AesCtr.ctrMode s₀ j s' ∧ s'.z = decide (N s₀ - j = 0) := by
  rw [show test = [.cmp .r8 (.imm 0)] from rfl]
  refine wp_cmp (op2_imm (by decide)) fun s' f hz => WP.block_nil ⟨?_, ?_⟩
  · exact ⟨by rw [f.gpr, h.r4], by rw [f.gpr, h.r5], by rw [f.gpr, h.r6], by rw [f.gpr, h.r7],
      by rw [f.gpr, h.r8], by rw [f.gpr, h.r10], by rw [f.gpr, h.r11], by rw [f.sp, h.sp], by rw [f.rd, h.rd],
      by rw [f.wr, h.wr], by rw [f.mem]; exact h.frame, by rw [f.mem]; exact h.data, by rw [f.mem]; exact h.iv⟩
  · rw [hz, h.r8]; exact cmp0 (by have := N_lt s₀; omega_arith)

/-- One iteration. -/
theorem iter_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa body s fun s' =>
      LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.z = decide (N s₀ - (k + mOf s₀ k) = 0) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp hk h a) fun _ hm =>
      WP.seq (WP.mono (adv_wp hp hk hm) fun _ a' =>
        WP.seq (WP.mono (fin_wp hp hk hm a') fun _ hl => test_wp hl))))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv AesCtr.ctrMode s₀ k s) : WP isa (.loop body .ne) s (LInv AesCtr.ctrMode s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv AesCtr.ctrMode s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv AesCtr.ctrMode s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp hj h) fun s' ⟨h', hz⟩ => ?_
  obtain hm0 := mOf_pos hj
  obtain hle := mOf_le s₀ j
  have ev : isa.eval .ne s' = some !decide (N s₀ - (j + mOf s₀ j) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N s₀ - (j + mOf s₀ j) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N s₀ = j + mOf s₀ j by omega_arith]
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (j + mOf s₀ j), by omega_arith, j + mOf s₀ j, rfl, by omega_arith, h'⟩

/-- The whole function. -/
theorem crypt_wp {s₀ : State} (h0 : (modeArm AesCtr.ctrMode).pre s₀) :
    WP isa crypt s₀ fun s' => abiPreserved s₀ s' ∧ (modeArm AesCtr.ctrMode).post s₀ s' := by
  have hp := UPre.of h0
  refine WP.seq (WP.mono (prologue_wp (M := AesCtr.ctrMode) hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono ?_ fun _ h₂ => epilogue_wp hp h₂))
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h₁
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_wp hp (by omega_using [hn]) h₁

/-! ## Constant time

Two runs from states that agree on the public arguments and on the last 32
bits of the counter block (`ctrPub`, which the contract's `leak` declares)
are related piece by piece (`RelCT`): the taint analysis covers the code
between the call and the branches, from the registers the correctness proof
pins to the public arguments; the call is constant time by its own proof
(AES-GCM's `ctr_rel`), with the same arguments in both runs, since the
number of blocks it takes depends only on the public data (`mOf_eq`); and
the branches (the carry, the loop) are on facts the correctness proof gives
in terms of the public data (`After.wrap`, the loop's Z). -/

/-- What two runs agree on: the public arguments, and the last 32 bits of the
counter block. -/
def ctrPub (s₀ s₀' : State) : Prop :=
  (modeArm AesCtr.ctrMode).pub s₀ s₀' ∧ AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀')

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block (count ++ args)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8, .r9]) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (Taint.ofRegs [.r6]) (.block carry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem left_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block test) h).isSome = true := ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modeArm AesCtr.ctrMode).pub s₀ s₀')
  (hl : AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀'))
include hq hl

omit hq in
theorem lo32_next_eq (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) = AesCtr.lo32 (next (iv0 s₀') k) := by
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)]
  unfold AesCtr.lo32 at hl
  omega_using [hl]

theorem mOf_eq (k : Nat) : mOf s₀ k = mOf s₀' k := by
  have e := lo32_next_eq hl k
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)] at e
  unfold mOf
  rw [e, pub_N hq]

/-- One iteration, in two runs. -/
theorem body_rel (hp : UPre s₀) (hp' : UPre s₀') {k : Nat} (hk : k < N s₀) :
    RelCT isa (fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b) body
      fun a b =>
        (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) a ∧ a.z = decide (N s₀ - (k + mOf s₀ k) = 0)) ∧
        (LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) b ∧ b.z = decide (N s₀' - (k + mOf s₀' k) = 0)) := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  -- The code before the call.
  have p1 := rel_agree (F := fun s => LInv AesCtr.ctrMode s₀ k s) (F' := fun s => LInv AesCtr.ctrMode s₀' k s)
    (G := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀ k s ∧ PreA s₀ k s s₁)
    (G' := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀' k s ∧ PreA s₀' k s s₁)
    (Taint.ofRegs vars) (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h h')) pre_taint
    (fun a h => WP.mono (pre_wp hp hk h) fun _ x => ⟨a, h, x⟩)
    (fun b h => WP.mono (pre_wp hp' hk' h) fun _ x => ⟨b, h, x⟩)
  -- The call, with the same arguments in both runs.
  have p2 := rel_wp (F := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀ k s ∧ PreA s₀ k s s₁)
    (F' := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀' k s ∧ PreA s₀' k s s₁) (G := Mid s₀ k) (G' := Mid s₀' k)
    (c := ctrFrame)
    (by
      rw [ctrFrame_eq]
      exact ctr_rel fun a b h => by
        obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
        refine ⟨_, _, _, _, _, _, pa.call, ?_, ?_⟩
        · rw [pub_W hq, pub_Iv hq, pub_D32 hq, pub_S hq, pub_R hq, mOf_eq hq hl]; exact pb.call
        · rw [pa.sp, pb.sp, hs.sp, ht.sp, pub_sp hq])
    (fun _ ⟨_, hs, pa⟩ => mid_wp hp hk hs pa) (fun _ ⟨_, ht, pb⟩ => mid_wp hp' hk' ht pb)
  -- On past the call's blocks.
  have p3 := rel_agree (F := Mid s₀ k) (F' := Mid s₀' k)
    (G := fun s₂ => ∃ s, Mid s₀ k s ∧ After s₀ k s s₂) (G' := fun s₂ => ∃ s, Mid s₀' k s ∧ After s₀' k s s₂)
    (Taint.ofRegs [.r6, .r7, .r8, .r9]) (fun a b h h' => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.regs.r6, h'.regs.r6, pub_Iv hq]
      · rw [h.regs.r7, h'.regs.r7, pub_D32 hq]
      · rw [h.regs.r8, h'.regs.r8, pub_N hq]
      · rw [h.regs.r9, h'.regs.r9, mOf_eq hq hl]) adv_taint
    (fun a h => WP.mono (adv_wp hp hk h) fun _ x => ⟨a, h, x⟩)
    (fun b h => WP.mono (adv_wp hp' hk' h) fun _ x => ⟨b, h, x⟩)
  -- The carry if the counter wrapped around in both runs.
  have p4 : RelCT isa (fun a b => (∃ s, Mid s₀ k s ∧ After s₀ k s a) ∧ (∃ s, Mid s₀' k s ∧ After s₀' k s b))
      (.ite .eq (.block carry) (.block [])) fun _ _ => True := by
    obtain ⟨_, hc⟩ := carry_taint
    obtain ⟨_, hn⟩ := nil_taint
    refine RelCT.ite (fun a b h => ?_)
      (RelCT.taint (A := taint) _ (fun a b h => Taint.agree_ofRegs fun r hr => ?_) hc)
      (RelCT.taint (A := taint) _ (fun a b h => Taint.agree_ofRegs fun r hr => by simp at hr) hn)
    · obtain ⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩ := h
      rw [xa.wrap, xb.wrap, lo32_next_eq hl, mOf_eq hq hl]
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩, _⟩ := h
      simp only [List.mem_singleton] at hr; subst hr
      rw [xa.gpr _ (by decide) (by decide) (by decide), xb.gpr _ (by decide) (by decide) (by decide), hs.regs.r6,
        ht'.regs.r6, pub_Iv hq]
  have p5 := rel_wp (F := fun s₂ => ∃ s, Mid s₀ k s ∧ After s₀ k s s₂)
    (F' := fun s₂ => ∃ s, Mid s₀' k s ∧ After s₀' k s s₂)
    (G := LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) (G' := LInv AesCtr.ctrMode s₀' (k + mOf s₀' k)) p4
    (fun _ ⟨_, hs, xa⟩ => fin_wp hp hk hs xa) (fun _ ⟨_, ht, xb⟩ => fin_wp hp' hk' ht xb)
  -- Whether blocks are left.
  have p6 := rel_agree (F := LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) (F' := LInv AesCtr.ctrMode s₀' (k + mOf s₀' k))
    (G := fun s => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s ∧ s.z = decide (N s₀ - (k + mOf s₀ k) = 0))
    (G' := fun s => LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) s ∧ s.z = decide (N s₀' - (k + mOf s₀' k) = 0))
    (Taint.ofRegs []) (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) left_taint
    (fun _ h => test_wp h) (fun _ h => test_wp h)
  exact p1.seq (p2.seq (p3.seq (p5.seq p6)))

/-- The loop's relation, with the number of blocks left. -/
def LRel (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b

theorem loop_rel (hp : UPre s₀) (hp' : UPre s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop body .ne)
      fun a b => LInv AesCtr.ctrMode s₀ (N s₀) a ∧ LInv AesCtr.ctrMode s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have hm := mOf_eq hq hl k
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  refine (body_rel hq hl hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hm] at l₂ z₂
  have e₁ : isa.eval .ne s₁ = some !decide (N s₀ - (k + mOf s₀ k) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N s₀ - (k + mOf s₀ k) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + mOf s₀ k = N s₀ := by
      have : N s₀ - (k + mOf s₀ k) = 0 := by simpa using hf
      omega_using [hk, hle, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + mOf s₀ k) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + mOf s₀ k), by omega_using [hk, hm0], k + mOf s₀ k, rfl, by omega_using [h0], l₁, l₂⟩

end

/-- The whole function, in two runs that agree on the public data. -/
theorem crypt_rel {s₀ s₀' : State} (h0 : (modeArm AesCtr.ctrMode).pre s₀)
    (h0' : (modeArm AesCtr.ctrMode).pre s₀') (hq : ctrPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') crypt fun _ _ => True :=
  ends_rel h0 h0' hq.1 fun hp hp' hN =>
    (loop_rel hq.1 hq.2 hp hp' (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h

theorem crypt_ct : ConstantTime isa (modeArm AesCtr.ctrMode).pre ctrPub crypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCtr.Arm
