import VerifiedGarbage.Proof.AesCtr.AArch64.Body

/-!
# AES-CTR on AArch64: one iteration, and the whole function

`iter_wp`: one run of `body` takes AES-CBC's loop invariant for `ctrMode`
from `k` blocks to `k + mOf s₀ k`, for any implementation of
`vg_aes_ctr32` (`Ctr32Impl`). The call gives CTR's output on its blocks
(`AesCtr.ctr32_crypt`), and the counter block it leaves, with the carry into
the first 96 bits if its last 32 bits wrapped around, is CTR's
(`AesCtr.ctr32_next`, `AesCtr.ctr32_wrap`).
-/

namespace VG.Proof.AesCtr.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCtr.AArch64
open VG.Impl.AesCbc.AArch64 (cOff)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

theorem preserved_ne4 {r : Reg} (hr : r ∈ preserved) : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The registers the invariant pins, in a state after `k` blocks. -/
structure Regs (s₀ : State) (k : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = blk s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
    r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The registers after a step that keeps the callee-saved ones but `x30`. -/
theorem Regs.of {M : AesCbc.Mode} {s₀ : State} {k : Nat} {s s' : State} (h : LInv M s₀ k s)
    (g : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Regs s₀ k s' where
  x19 := by rw [g .x19 (by simp [preserved]) (by decide), h.x19]
  x20 := by rw [g .x20 (by simp [preserved]) (by decide), h.x20]
  x21 := by rw [g .x21 (by simp [preserved]) (by decide), h.x21]
  x22 := by rw [g .x22 (by simp [preserved]) (by decide), h.x22]
  x23 := by rw [g .x23 (by simp [preserved]) (by decide), h.x23]
  x24 := by rw [g .x24 (by simp [preserved]) (by decide), h.x24]
  other r hr h19 h20 h21 h22 h23 h24 h30 := by rw [g r hr h30, h.other r hr h19 h20 h21 h22 h23 h24 h30]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- What the call leaves, after `k` blocks. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  regs : Regs s₀ k s
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  slot : s.mem.readW (S s₀ + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 (mOf s₀ k)
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) =
    outK AesCtr.ctrMode s₀ (k + mOf s₀ k) ++ (blks s₀).drop (k + mOf s₀ k)
  /-- The counter block: `t + k + m`, less `2³²` if its last 32 bits
  wrapped around. -/
  iv : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k < 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) (k + mOf s₀ k)
  ivw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = ofNat (toNat (next (iv0 s₀) k) + mOf s₀ k - 2 ^ 32) 16

/-- The call, after the code before it. -/
theorem mid_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s s₁ : State} (h : LInv AesCtr.ctrMode s₀ k s)
    (a : Pre s₀ k s s₁) : WP isa (.call v.callee.name v.callee.code) s₁ (Mid s₀ k) := by
  refine WP.mono (ctr_call v a.call) fun s₂ c => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s.gpr r := by
    rw [c.saved r hr h30, a.saved r hr]
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  generalize hmd : mOf s₀ k = m at hm0 hle a c
  -- The memory before the call: the slot written.
  have f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩] s.mem s₁.mem := by
    rw [a.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have slotSub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := UPre.seg_sub (by omega)
  have fc : Frame [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩] s₁.mem s₂.mem := c.frame
  have fAll : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, slotSub⟩).trans
    (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩)
  -- The slot after the call.
  have dSlot : ∀ r ∈ [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩],
      (⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
    · exact (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right segSub
    · exact Offset.disjoint_base _ (by decide) (by omega)
  have slot : s₂.mem.readW (S s₀ + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 m := by
    rw [fc.readW (r := ⟨S s₀ + BitVec.ofNat 64 2048, 8⟩) (Region.contains_self _ _) dSlot (by decide),
      a.mem, Mem.readW_writeW_self64, hmd]
  -- The data and the counter block before the call.
  have hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega)]
  have ivIn : bytesAt s₁.mem (Iv s₀) 16 = next (iv0 s₀) k := by
    rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))) (by decide), hiv]
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  have sched : bytesAt s₁.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp big₁
  have hlen : (blks s₀).length = N s₀ := Proof.AesCbc.length_blocksAt _ _ _
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    have dj : Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left dj).sub_right (UPre.scr_sub (by decide))
    · exact (hp.iv_data.symm.sub_left dj)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.data_scr.sub_left dj).sub_right (Region.sub_prefix (by decide))
  have keepBlocks {p : Addr} {a n : Nat} (hp' : p = Dp s₀ + BitVec.ofNat 64 (16 * a)) (hn : a + n ≤ N s₀)
      (ho : a + n ≤ k ∨ k + m ≤ a) : Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    have hd : ∀ j < n, ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩,
        ⟨S s₀, 2048⟩], (⟨Dp s₀ + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
      fun j hj => by
        rw [Offset.add_add, show 16 * a + 16 * j = 16 * (a + j) by omega]
        exact outside (a + j) (by omega) (by omega)
    rw [AesCtr.blocksAt_frame fc (fun j hj r hr => hd j hj r (List.mem_cons_of_mem _ hr)),
      AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd j hj _ (by simp))]
  have dataS := h.data
  rw [outK, AesCtr.ctrMode_out] at dataS
  -- The call's blocks.
  have segIn : Spec.Cbc.blocksAt s₁.mem (blk s₀ k) m = ((blks s₀).drop k).take m := by
    rw [AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add, show 16 * k + 16 * j = 16 * (k + j) by omega]
      exact (hp.data_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (UPre.scr_sub (by decide))),
      ← AesCtr.blocksAt_take _ _ (show m ≤ N s₀ - k by omega), ← AesCtr.blocksAt_drop _ _ (by omega), dataS,
      List.drop_left' (by rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega)])]
  have seg := AesCtr.ctr32_crypt (k := m) (by rw [ivIn, ← hmd]; exact lo32_mOf s₀ k) c.out
  rw [sched, ivIn, segIn] at seg
  refine ⟨Regs.of h g (by rw [c.sp, a.sp]) (by rw [c.rd, a.rd]) (by rw [c.wr, a.wr]),
    h.frame.trans fAll, by rw [hmd]; exact slot, ?_, ?_, ?_⟩
  · -- The data: the first `k` blocks and those after the call's as they were, and the call's.
    have hlc : (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k)).length = k := by
      rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega)]
    have hA : Spec.Cbc.blocksAt s.mem (Dp s₀) k =
        Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k) := by
      rw [← AesCtr.blocksAt_take _ _ (show k ≤ N s₀ by omega), dataS, List.take_left' hlc]
    have hC : Spec.Cbc.blocksAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * (k + m))) (N s₀ - (k + m)) =
        (blks s₀).drop (k + m) := by
      rw [← AesCtr.blocksAt_drop _ _ (show k + m ≤ N s₀ by omega), dataS]
      conv => lhs; rw [show k + m = (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀)
        ((blks s₀).take k)).length + m by rw [hlc]]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hlc, Nat.add_sub_cancel_left]
      exact List.drop_drop
    rw [hmd, AesCtr.blocksAt_three s₂.mem (Dp s₀) (a := k) (b := m) (by omega),
      keepBlocks (a := 0) (by simp) (by omega) (by omega), keepBlocks (a := k + m) rfl (by omega) (by omega),
      show Dp s₀ + BitVec.ofNat 64 (16 * k) = blk s₀ k from rfl, seg, hA, hC, outK, AesCtr.ctrMode_out]
    exact AesCtr.crypt_step _ _ _ (by omega)
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_next (by rw [ivIn]; omega) c.ctr, ivIn, AesCtr.next_add]
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_wrap (by rw [ivIn]; omega) c.ctr, ivIn]

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid s₀ k s) (hmd : mOf s₀ k = m)
    (g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r)
    (x22 : s'.gpr .x22 = blk s₀ (k + m)) (x23 : s'.gpr .x23 = BitVec.ofNat 64 (N s₀ - (k + m)))
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = next (iv0 s₀) (k + m)) :
    LInv AesCtr.ctrMode s₀ (k + m) s' where
  x19 := by rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.x19]
  x20 := by rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.x20]
  x21 := by rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.x21]
  x22 := x22
  x23 := x23
  x24 := by rw [g .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.x24]
  other r hr h19 h20 h21 h22 h23 h24 h30 := by
    have := preserved_ne4 hr
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2 h22 h23, h.regs.other r hr h19 h20 h21 h22 h23 h24 h30]
  sp := by rw [hsp, h.regs.sp]
  rd := by rw [hrd, h.regs.rd]
  wr := by rw [hwr, h.regs.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm.sub_left (Offset.sub_base _ (by omega))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

omit hp in
theorem adv_eq : adv = ([.ldr .x .x9 .x24 cOff, .sub .x .x23 .x23 .x9, .lsl .x .x9 .x9 4,
    .add .x .x22 .x22 .x9] : List Instr) ++ ([.ldr .w .x9 .x21 12] : List Instr) := rfl

/-- What `adv` leaves. -/
structure After (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → r ≠ .x22 → r ≠ .x23 → s₂.gpr r = s.gpr r
  x22 : s₂.gpr .x22 = blk s₀ (k + mOf s₀ k)
  x23 : s₂.gpr .x23 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k))
  sp : s₂.sp = s.sp
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  wrap : isa.eval (.zero .w .x9) s₂ = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32))

/-- On past the call's blocks, with the counter's last 32 bits read back. -/
theorem adv_wp {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) : WP isa (.block adv) s (After s₀ k s) := by
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have hlo := lo32_mOf s₀ k
  have hdw := hp.data_wrap
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.regs.rd, h.regs.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₁, run₁, x23₁, x22₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ := advA_ok s h.regs.x24 h.regs.x22 h.regs.x23 h.slot
    (by omega) (by omega) (by rw [hR]; exact in_rw (by simp) cSv0)
  obtain ⟨s₂, run₂, w9₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ := advB_ok s₁ (Q := Iv s₀)
    (by rw [g₁ _ (by decide) (by decide) (by decide), h.regs.x21])
    (by rw [rd₁, wr₁, hR]; exact in_rw (r := ivR s₀) (by simp) cIv12)
  rw [adv_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .x9) (h22 : r ≠ .x22) (h23 : r ≠ .x23) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h1, g₁ r h1 h22 h23]
  have x22₂ : s₂.gpr .x22 = blk s₀ (k + mOf s₀ k) := by
    rw [g₂ _ (by decide), x22₁, Offset.add_add,
      show 16 * k + 16 * mOf s₀ k = 16 * (k + mOf s₀ k) by omega]
  have x23₂ : s₂.gpr .x23 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k)) := by rw [g₂ _ (by decide), x23₁, Nat.sub_sub]
  have m₂ : s₂.mem = s.mem := by rw [mem₂, mem₁]
  have hb := AesCtr.toNat_lt (show (next (iv0 s₀) k).length = 16 by
    rw [AesCtr.next_eq (length_iv0 s₀)]; exact AesCtr.length_ofNat _ _)
  have hlo2 := AesCtr.lo32_bytesAt s.mem (Iv s₀)
  have wrapE : isa.eval (.zero .w .x9) s₂ =
      some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32)) := by
    show some (s₂.read .w .x9 == 0) = _
    rw [w9₂, mem₁]
    by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
    · have e := h.ivw hw
      rw [e, AesCtr.lo32, AesCtr.toNat_ofNat] at hlo2
      have hw' := hw
      unfold AesCtr.lo32 at hw'
      have : (rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32)).toNat = 0 := by rw [← hlo2]; omega
      have h0 := AesCtr.rv32_eq_zero.mp (BitVec.eq_of_toNat_eq this)
      simp [h0, hw]
    · have e := h.iv (by omega)
      rw [e, AesCtr.lo32_next (length_iv0 s₀)] at hlo2
      rw [AesCtr.lo32_next (length_iv0 s₀)] at hw hlo
      have : (rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32)).toNat ≠ 0 := by rw [← hlo2]; omega
      have h0 : s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32 ≠ 0 := fun h0 => this (by rw [h0]; rfl)
      rw [AesCtr.lo32_next (length_iv0 s₀)]
      simp only [hw, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
      exact h0
  exact ⟨g, x22₂, x23₂, by rw [sp₂, sp₁], m₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], wrapE⟩

/-- The carry if the counter wrapped around. -/
theorem fin_wp {k : Nat} (hk : k < N s₀) {s s₂ : State} (h : Mid s₀ k s) (a : After s₀ k s s₂) :
    WP isa (.ite (.zero .w .x9) (.block carry) (.block [])) s₂ (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) := by
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.regs.rd, h.regs.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.regs.wr, hp.wr]
  have x21₂ : s₂.gpr .x21 = Iv s₀ := by rw [a.gpr _ (by decide) (by decide) (by decide), h.regs.x21]
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · refine WP.ite true (by rw [a.wrap]; simp [hw]) (fun _ => ?_) (fun h => by cases h)
    obtain ⟨s₃, run₃, g₃, sp₃, bytes₃, f₃, rd₃, wr₃⟩ := carry_ok s₂ x21₂
      (by rw [a.rd, a.wr, hR]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [a.rd, a.wr, hR]; exact in_rw (r := ivR s₀) (by simp) cIv8)
      (by rw [a.wr, hW]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [a.wr, hW]; exact in_rw (r := ivR s₀) (by simp) cIv8)
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    refine finish hp (by omega) h rfl (fun r h9 h10 h11 h12 h22 h23 => by rw [g₃ r h9 h10 h11 h12, a.gpr r h9 h22 h23])
      (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), a.x22])
      (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), a.x23])
      (by rw [sp₃, a.sp]) (by rw [rd₃, a.rd]) (by rw [wr₃, a.wr]) (by rw [← a.mem]; exact f₃) ?_
    rw [bytes₃, a.mem, h.ivw hw]
    exact AesCtr.carry_next (length_iv0 s₀) hw
  · refine WP.ite false (by rw [a.wrap]; simp [hw]) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    exact finish hp (by omega) h rfl (fun r h9 _ _ _ h22 h23 => a.gpr r h9 h22 h23) a.x22 a.x23 a.sp a.rd a.wr
      (by rw [a.mem]; exact Frame.refl _ _) (by rw [a.mem, h.iv (by have := lo32_mOf s₀ k; omega)])

/-- One iteration. -/
theorem iter_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (body v.callee) s (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k)) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp v hk h a) fun _ hm =>
      WP.seq (WP.mono (adv_wp hp hk hm) fun _ a => fin_wp hp hk hm a)))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.loop (body v.callee) (.nonzero .x .x23)) s (LInv AesCtr.ctrMode s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body v.callee) (c := .nonzero .x .x23) (Q := LInv AesCtr.ctrMode s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv AesCtr.ctrMode s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp v hj h) fun s' h' => ?_
  have hm0 := mOf_pos hj
  have hle := mOf_le s₀ j
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := eval_x23 (x := N s₀ - (j + mOf s₀ j)) (by omega) h'.x23
  by_cases hz : N s₀ - (j + mOf s₀ j) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = j + mOf s₀ j by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (j + mOf s₀ j), by omega, j + mOf s₀ j, rfl, by omega, h'⟩

end

/-- The whole function. -/
theorem crypt_wp (v : Ctr32Impl) {s₀ : State} (h0 : (modeAArch64 AesCtr.ctrMode).pre s₀) :
    WP isa (crypt v.callee) s₀ fun s' => GprAbi s₀ s' ∧ (modeAArch64 AesCtr.ctrMode).post s₀ s' :=
  ends_wp h0 fun hp hN _ h => loop_wp hp v hN h

end VG.Proof.AesCtr.AArch64
