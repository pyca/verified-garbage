module

public import VerifiedGarbage.Proof.AesCtr.RISCV64.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.AesCtr.RISCV64.Steps
import VerifiedGarbage.Proof.AesCtr.RISCV64.Words

/-!
# AES-CTR on RISC-V: one iteration, and the loop

As on PPC64LE (`Proof/AesCtr/PPC64LE/Iter.lean`): `iter_wp`, one run of
`body` takes AES-CBC's loop invariant for `ctrMode` from `k` blocks to
`k + mOf s₀ k`. The call gives CTR's output on its blocks
(`AesCtr.ctr32_crypt`), and the counter block it leaves, with the carry into
the first 96 bits if its last 32 bits wrapped around, is CTR's
(`AesCtr.ctr32_next`, `AesCtr.ctr32_wrap`, `AesCtr.carry_next`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.ByteLoad VG.Impl.AesCtr.RISCV64
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The slot of the call's number of blocks. -/
abbrev slotR (s₀ : State) : Region := ⟨sv s₀, 8⟩

/-- What the call leaves, after `k` blocks. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = W s₀
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (Mut s₀) (savedMem s₀) s.mem
  slot : s.mem.readW (sv s₀) 64 = BitVec.ofNat 64 (mOf s₀ k)
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) =
    outK AesCtr.ctrMode s₀ (k + mOf s₀ k) ++ (blks s₀).drop (k + mOf s₀ k)
  /-- The counter block: `t + k + m`, less `2³²` if its last 32 bits
  wrapped around. -/
  iv : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k < 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) (k + mOf s₀ k)
  ivw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = ofNat (toNat (next (iv0 s₀) k) + mOf s₀ k - 2 ^ 32) 16

theorem slot_sub (s₀ : State) : Region.Sub (slotR s₀) (cR s₀) := Region.sub_prefix (by decide)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The call, after the code before it. -/
theorem mid_wp {k : Nat} (hk : k < N s₀) {s s₁ : State} (h : LInv AesCtr.ctrMode s₀ k s)
    (a : Pre s₀ k s s₁) : WP isa ctrCall s₁ (Mid s₀ k) := by
  refine WP.mono (ctr_call a.call) fun s₂ c => ?_
  have g (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  generalize hmd : mOf s₀ k = m at hm0 hle a c
  have slotScr : Region.Sub (slotR s₀) (scrR s₀) := fun _ h => cR_sub _ (slot_sub s₀ _ h)
  -- The memory before the call: the slot written.
  have f₁ : Frame [slotR s₀] s.mem s₁.mem := by
    rw [a.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := UPre.seg_sub (by omega_arith)
  have fc : Frame [ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀] s₁.mem s₂.mem := c.frame
  have fAll : Frame (Mut s₀) s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨cR s₀, by simp, slot_sub s₀⟩).trans
    (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨wsR s₀, by simp, fun _ h => h⟩)
  -- The slot after the call.
  have dSlot : ∀ r ∈ [ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀], (slotR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left slotScr
    · exact (hp.data_scr.symm.sub_left slotScr).sub_right segSub
    · exact hp.cR_wsR.sub_left (slot_sub s₀)
  have slot : s₂.mem.readW (sv s₀) 64 = BitVec.ofNat 64 m := by
    rw [fc.readW (r := slotR s₀) (Region.contains_self _ _) dSlot (by decide),
      a.mem, Mem.readW_writeW_self64, hmd]
  -- The data and the counter block before the call.
  have hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega_arith)]
  have ivIn : bytesAt s₁.mem (Iv s₀) 16 = next (iv0 s₀) k := by
    rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right slotScr) (by decide), hiv]
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, slotScr⟩)
  have sched : bytesAt s₁.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp big₁
  have hlen : (blks s₀).length = N s₀ := Proof.AesCbc.length_blocksAt _ _ _
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [slotR s₀, ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    have dj : Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) := Offset.sub_base _ (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left dj).sub_right slotScr
    · exact (hp.iv_data.symm.sub_left dj)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.data_scr.sub_left dj).sub_right wsR_sub
  have keepBlocks {p : Addr} {a n : Nat} (hp' : p = Dp s₀ + BitVec.ofNat 64 (16 * a)) (hn : a + n ≤ N s₀)
      (ho : a + n ≤ k ∨ k + m ≤ a) : Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    have hd : ∀ j < n, ∀ r ∈ [slotR s₀, ivR s₀, ⟨blk s₀ k, 16 * m⟩, wsR s₀],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
      fun j hj => by
        rw [Offset.add_add, show 16 * a + 16 * j = 16 * (a + j) by omega_arith]
        exact outside (a + j) (by omega_arith) (by omega_arith)
    rw [AesCtr.blocksAt_frame fc (fun j hj r hr => hd j hj r (List.mem_cons_of_mem _ hr)),
      AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd j hj _ (by simp))]
  have dataS := h.data
  rw [outK, AesCtr.ctrMode_out] at dataS
  -- The call's blocks.
  have segIn : Spec.Cbc.blocksAt s₁.mem (blk s₀ k) m = ((blks s₀).drop k).take m := by
    rw [AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add, show 16 * k + 16 * j = 16 * (k + j) by omega_arith]
      exact (hp.data_scr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right slotScr),
      ← AesCtr.blocksAt_take _ _ (show m ≤ N s₀ - k by omega_arith), ← AesCtr.blocksAt_drop _ _ (by omega_arith), dataS,
      List.drop_left' (by rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)])]
  have seg := AesCtr.ctr32_crypt (k := m) (by rw [ivIn, ← hmd]; exact lo32_mOf s₀ k) c.out
  rw [sched, ivIn, segIn] at seg
  refine ⟨by rw [g .s1 (by decide), h.s1], by rw [g .s2 (by decide), h.s2],
    by rw [g .s3 (by decide), h.s3], by rw [g .s4 (by decide), h.s4],
    by rw [g .s5 (by decide), h.s5], by rw [g .s6 (by decide), h.s6],
    fun r hr hv => by rw [g r hr, h.keep r hr hv], by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr],
    by rw [c.sp, a.sp, h.sp], h.frame.trans fAll, by rw [hmd]; exact slot, ?_, ?_, ?_⟩
  · -- The data: the first `k` blocks and those after the call's as they were, and the call's.
    have hlc : (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k)).length = k := by
      rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)]
    have hA : Spec.Cbc.blocksAt s.mem (Dp s₀) k =
        Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k) := by
      rw [← AesCtr.blocksAt_take _ _ (show k ≤ N s₀ by omega_arith), dataS, List.take_left' hlc]
    have hC : Spec.Cbc.blocksAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * (k + m))) (N s₀ - (k + m)) =
        (blks s₀).drop (k + m) := by
      rw [← AesCtr.blocksAt_drop _ _ (show k + m ≤ N s₀ by omega_arith), dataS]
      conv => lhs; rw [show k + m = (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀)
        ((blks s₀).take k)).length + m by rw [hlc]]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega_arith), List.nil_append, hlc, Nat.add_sub_cancel_left]
      exact List.drop_drop
    rw [hmd, AesCtr.blocksAt_three s₂.mem (Dp s₀) (a := k) (b := m) (by omega_arith),
      keepBlocks (a := 0) (by simp) (by omega_arith) (by omega_arith), keepBlocks (a := k + m) rfl (by omega_arith) (by omega_arith),
      show Dp s₀ + BitVec.ofNat 64 (16 * k) = blk s₀ k from rfl, seg, hA, hC, outK, AesCtr.ctrMode_out]
    exact AesCtr.crypt_step _ _ _ (by omega_arith)
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_next (by rw [ivIn]; omega_arith) c.ctr, ivIn, AesCtr.next_add]
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_wrap (by rw [ivIn]; omega_arith) c.ctr, ivIn]

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid s₀ k s) (hmd : mOf s₀ k = m)
    (g : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .s4 → r ≠ .s5 → s'.gpr r = s.gpr r)
    (s4 : s'.gpr .s4 = blk s₀ (k + m)) (s5 : s'.gpr .s5 = BitVec.ofNat 64 (N s₀ - (k + m)))
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = next (iv0 s₀) (k + m)) :
    LInv AesCtr.ctrMode s₀ (k + m) s' where
  s1 := by rw [g .s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s1]
  s2 := by rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s2]
  s3 := by rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s3]
  s4 := s4
  s5 := s5
  s6 := by rw [g .s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.s6]
  keep r hr hv := by
    obtain ⟨-, -, -, -, -, -, h0, h1, h2, h3, -⟩ := preserved_ne' hr
    rw [g r h0 h1 h2 h3 (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  sp := by rw [hsp, h.sp]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm.sub_left (Offset.sub_base _ (by omega_arith))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

omit hp in
theorem setWidth_beq_zero (y : BitVec 32) : (y.setWidth 64 == 0) = (y == 0) := by
  by_cases h : y = 0
  · subst h; rfl
  · have h' : y.setWidth 64 ≠ 0 := fun e => h (by
      have e' := congrArg BitVec.toNat e
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans y.isLt (by decide))] at e'
      exact BitVec.eq_of_toNat_eq e')
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

/-- What `adv` leaves. -/
structure After (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  gpr : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s4 → r ≠ .s5 → s₂.gpr r = s.gpr r
  s4 : s₂.gpr .s4 = blk s₀ (k + mOf s₀ k)
  s5 : s₂.gpr .s5 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k))
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  ev : isa.eval (.zero .t1) s₂ = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32))

/-- On past the call's blocks, with the wrap of the counter in `t1`. -/
theorem adv_wp' {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) : WP isa (.block adv) s (After s₀ k s) := by
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have hlo := lo32_mOf s₀ k
  have hdw := hp.data_wrap
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine adv_wp (Q := Iv s₀) (S := S s₀) (P := blk s₀ k) (left := N s₀ - k) (m := mOf s₀ k)
    h.s3 h.s4 h.s5 h.s6 h.slot hle (by omega_arith) (by rw [hR]; exact in_rw (r := scrR s₀) (by simp) (cSv s₀))
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) (cIv s₀ (by decide)))
    fun s₂ s5₂ s4₂ t1₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine ⟨g₂, ?_, by rw [s5₂, Nat.sub_sub], m₂, rd₂, wr₂, sp₂, ?_⟩
  · rw [s4₂, Offset.add_add, show 16 * k + 16 * mOf s₀ k = 16 * (k + mOf s₀ k) by omega_arith]
  have hlo2 := lo32_beWord s.mem (Iv s₀)
  rw [eval_zero, t1₂, setWidth_beq_zero]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · have e := h.ivw hw
    rw [e, AesCtr.lo32, AesCtr.toNat_ofNat] at hlo2
    have hw' := hw
    unfold AesCtr.lo32 at hw'
    have : (beWord s.mem (Iv s₀) 12).toNat = 0 := by rw [← hlo2]; omega_arith
    have h0 := BitVec.eq_of_toNat_eq (y := (0 : BitVec 32)) this
    simp [h0, hw]
  · have e := h.iv (by omega_arith)
    rw [e, AesCtr.lo32_next (length_iv0 s₀)] at hlo2
    rw [AesCtr.lo32_next (length_iv0 s₀)] at hw hlo
    have : (beWord s.mem (Iv s₀) 12).toNat ≠ 0 := by rw [← hlo2]; omega_arith
    have h0 : beWord s.mem (Iv s₀) 12 ≠ 0 := fun h0 => this (by rw [h0]; rfl)
    rw [AesCtr.lo32_next (length_iv0 s₀)]
    simp only [hw, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
    exact h0

/-- The carry if the counter wrapped around. -/
theorem fin_wp {k : Nat} (hk : k < N s₀) {s s₂ : State} (h : Mid s₀ k s) (a : After s₀ k s s₂) :
    WP isa (.ite (.zero .t1) (.block carry) (.block [])) s₂ (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) := by
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have s3₂ : s₂.gpr .s3 = Iv s₀ := by
    rw [a.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), h.s3]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · refine WP.ite true (by rw [a.ev]; simp [hw]) (fun _ => ?_) (fun h => by cases h)
    refine carry_wp s3₂ (by rw [a.wr, h.wr, hp.wr]; simp) fun s₃ g₃ bytes₃ f₃ rd₃ wr₃ sp₃ => ?_
    refine finish hp (by omega_arith) h rfl
      (fun r h0 h1 h2 h3 h4 h5 => by rw [g₃ r h1 h2 h3, a.gpr r h0 h1 h2 h4 h5])
      (by rw [g₃ _ (by decide) (by decide) (by decide), a.s4])
      (by rw [g₃ _ (by decide) (by decide) (by decide), a.s5])
      (by rw [rd₃, a.rd]) (by rw [wr₃, a.wr]) (by rw [sp₃, a.sp]) (by rw [← a.mem]; exact f₃) ?_
    rw [bytes₃, a.mem, h.ivw hw]
    exact AesCtr.carry_next (length_iv0 s₀) hw
  · refine WP.ite false (by rw [a.ev]; simp [hw]) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    exact finish hp (by omega_arith) h rfl (fun r h0 h1 h2 _ h4 h5 => a.gpr r h0 h1 h2 h4 h5) a.s4 a.s5
      a.rd a.wr a.sp (by rw [a.mem]; exact Frame.refl _ _)
      (by rw [a.mem, h.iv (by have := lo32_mOf s₀ k; omega_arith)])

/-- One iteration. -/
theorem iter_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa body s (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp hk h a) fun _ hm =>
      WP.seq (WP.mono (adv_wp' hp hk hm) fun _ a => fin_wp hp hk hm a)))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.loop body (.nonzero .s5)) s (LInv AesCtr.ctrMode s₀ (N s₀)) := by
  have hN := (s₀.gpr .a4).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .s5) (Q := LInv AesCtr.ctrMode s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv AesCtr.ctrMode s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp hj h) fun s' h' => ?_
  have hm0 := mOf_pos hj
  have hle := mOf_le s₀ j
  have ev := eval_nonzero_ofNat s' .s5 (k := N s₀ - (j + mOf s₀ j))
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.s5
  by_cases hz' : j + mOf s₀ j = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp; omega_arith, N s₀ - (j + mOf s₀ j), by omega_arith, j + mOf s₀ j, rfl, by omega_arith, h'⟩

end

/-- The whole function. -/
theorem crypt_wp {s₀ : State} (h0 : (modeRISCV64 AesCtr.ctrMode).pre s₀) :
    WP isa crypt s₀ (Done AesCtr.ctrMode s₀) :=
  ends_wp h0 fun hp hN _ h => loop_wp hp hN h

end VG.Proof.AesCtr.RISCV64
