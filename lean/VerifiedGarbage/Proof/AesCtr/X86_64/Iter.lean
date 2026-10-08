import VerifiedGarbage.Proof.AesCtr.X86_64.Body

/-!
# AES-CTR on x86-64: one iteration

`iter_wp`: one run of `body` takes AES-CBC's loop invariant for `ctrMode`
from `k` blocks to `k + mOf s₀ k`, and sets ZF if no blocks are left.
-/

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (at_ cOff)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesGcm.X86_64 (CtrCall CtrPost ctr_call)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- What the call leaves, after `k` blocks. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
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
  have g (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  generalize hmd : mOf s₀ k = m at hm0 hle a c
  have hrsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  -- The memory before the call: the slot written.
  have f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩] s.mem s₁.mem := by
    rw [a.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have slotSub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := UPre.seg_sub (by omega)
  have fc : Frame [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩, below (s₁.gpr .rsp) 8] s₁.mem s₂.mem := c.frame
  rw [hrsp] at fc
  have fAll : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, slotSub⟩).trans
    (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  -- The slot after the call.
  have dSlot : ∀ r ∈ [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩, stkR s₀],
      (⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
    · exact (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right segSub
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact hp.stk_scr.symm.sub_left (UPre.scr_sub (by decide))
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
  have hlk : (outK AesCtr.ctrMode s₀ k).length = k := by
    rw [outK, AesCtr.ctrMode_out, AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega)]
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩, stkR s₀],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    have dj : Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left dj).sub_right (UPre.scr_sub (by decide))
    · exact (hp.iv_data.symm.sub_left dj)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.data_scr.sub_left dj).sub_right (Region.sub_prefix (by decide))
    · exact hp.stk_data.symm.sub_left dj
  have keepBlocks {p : Addr} {a n : Nat} (hp' : p = Dp s₀ + BitVec.ofNat 64 (16 * a)) (hn : a + n ≤ N s₀)
      (ho : a + n ≤ k ∨ k + m ≤ a) : Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    have hd : ∀ j < n, ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩,
        stkR s₀], (⟨Dp s₀ + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
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
  have hctr := c.ctr
  rw [show Spec.Gcm.blockAt s₁.mem (Iv s₀) = Spec.Gcm.ofBytes (bytesAt s₁.mem (Iv s₀) 16) from rfl] at hctr
  refine ⟨by rw [g .rbx (by simp [calleeSaved]), h.rbx], by rw [g .rbp (by simp [calleeSaved]), h.rbp],
    by rw [g .r12 (by simp [calleeSaved]), h.r12], by rw [g .r13 (by simp [calleeSaved]), h.r13],
    by rw [g .r14 (by simp [calleeSaved]), h.r14], by rw [g .r15 (by simp [calleeSaved]), h.r15],
    by rw [g .rsp (by simp [calleeSaved]), h.rsp], by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr],
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

omit hp in
theorem test_ok (s : State) :
    ∃ s', runBlock isa [.alu .test .r14 (.reg .r14)] s = some s' ∧ s'.zf = some (s.gpr .r14 == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]; exact rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, BitVec.and_self]
  all_goals rfl

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid s₀ k s) (hmd : mOf s₀ k = m)
    (g : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r)
    (r13 : s'.gpr .r13 = blk s₀ (k + m)) (r14 : s'.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + m)))
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = next (iv0 s₀) (k + m)) :
    LInv AesCtr.ctrMode s₀ (k + m) s' where
  rbx := by rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide), h.rbx]
  rbp := by rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]
  r12 := by rw [g .r12 (by decide) (by decide) (by decide) (by decide) (by decide), h.r12]
  r13 := r13
  r14 := r14
  r15 := by rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h.r15]
  rsp := by rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide), h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm.sub_left (Offset.sub_base _ (by omega))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

omit hp in
theorem adv_eq : adv = [.mov .rax (.mem (at_ .r15 cOff)), .alu .sub .r14 (.reg .rax), .shift .shl .rax 4,
    .alu .add .r13 (.reg .rax)] ++ [.mov32 .rax (.mem (at_ .r12 12)), .alu32 .test .rax (.reg .rax)] := rfl

/-- On past the call's blocks, the carry if the counter wrapped around, and
ZF set if no blocks are left. -/
theorem tail_wp {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) :
    WP isa (.seq (.block adv) (.seq (.ite .e (.block carry) (.block [])) (.block [.alu .test .r14 (.reg .r14)]))) s
      fun s' => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)) := by
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  have hlo := lo32_mOf s₀ k
  have hdw := hp.data_wrap
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain ⟨s₁, run₁, r14₁, r13₁, g₁, mem₁, rd₁, wr₁⟩ := advA_ok s h.r15 h.r13 h.r14 h.slot (by omega) (by omega)
    (by rw [hR]; exact in_rw (by simp) cSv0)
  obtain ⟨s₂, run₂, zf₂, g₂, mem₂, rd₂, wr₂⟩ := advB_ok s₁ (Q := Iv s₀)
    (by rw [g₁ _ (by decide) (by decide) (by decide), h.r12])
    (by rw [rd₁, wr₁, hR]; exact in_rw (r := ivR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
  rw [adv_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .rax) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h1, g₁ r h1 h13 h14]
  have r13₂ : s₂.gpr .r13 = blk s₀ (k + mOf s₀ k) := by
    rw [g₂ _ (by decide), r13₁, Offset.add_add, show 16 * k + 16 * mOf s₀ k = 16 * (k + mOf s₀ k) by omega]
  have r14₂ : s₂.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k)) := by rw [g₂ _ (by decide), r14₁, Nat.sub_sub]
  have m₂ : s₂.mem = s.mem := by rw [mem₂, mem₁]
  have hb := AesCtr.toNat_lt (show (next (iv0 s₀) k).length = 16 by
    rw [AesCtr.next_eq (length_iv0 s₀)]; exact AesCtr.length_ofNat _ _)
  have hlo2 := lo32_bytesAt s.mem (Iv s₀)
  have zfE : s₂.zf = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32)) := by
    rw [zf₂, mem₁]
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
  have hNb : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have r12₂ : s₂.gpr .r12 = Iv s₀ := by rw [g _ (by decide) (by decide) (by decide), h.r12]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have zfEnd (t : State) (h14 : t.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k))) :
      some (t.gpr .r14 == 0) = some (decide (k + mOf s₀ k = N s₀)) := by
    rw [h14, AesCbc.X86_64.beq_zero (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega
  refine WP.seq ?_
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · have ev : isa.eval .e s₂ = some true := by
      show s₂.zf = _; rw [zfE]; simp [hw]
    refine WP.ite true ev (fun _ => ?_) (fun h => by cases h)
    obtain ⟨s₃, run₃, g₃, bytes₃, f₃, rd₃, wr₃⟩ := carry_ok s₂ r12₂
      (by rw [rd₂', wr₂', hR]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [rd₂', wr₂', hR]; exact in_rw (r := ivR s₀) (by simp) cIv8)
      (by rw [wr₂', hW]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [wr₂', hW]; exact in_rw (r := ivR s₀) (by simp) cIv8)
    obtain ⟨s₄, run₄, zf₄, gpr₄, mem₄, rd₄, wr₄⟩ := test_ok s₃
    refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, ?_⟩⟩
    have g4 (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .rdx) : s₄.gpr r = s₂.gpr r := by
      rw [gpr₄, g₃ r h1 h2 h3]
    refine ⟨finish hp (by omega) h rfl (fun r h1 h2 h3 h13 h14 => by rw [g4 r h1 h2 h3, g r h1 h13 h14])
      (by rw [g4 _ (by decide) (by decide) (by decide), r13₂]) (by rw [g4 _ (by decide) (by decide) (by decide), r14₂])
      (by rw [rd₄, rd₃, rd₂']) (by rw [wr₄, wr₃, wr₂']) ?_ ?_, ?_⟩
    · rw [mem₄, ← m₂]; exact f₃
    · rw [mem₄, bytes₃, m₂, h.ivw hw]
      exact AesCtr.carry_next (length_iv0 s₀) hw
    · rw [zf₄, zfEnd s₃ (by rw [g₃ _ (by decide) (by decide) (by decide), r14₂])]
  · have ev : isa.eval .e s₂ = some false := by
      show s₂.zf = _; rw [zfE]; simp [hw]
    refine WP.ite false ev (fun h => by cases h) (fun _ => WP.block_nil ?_)
    obtain ⟨s₄, run₄, zf₄, gpr₄, mem₄, rd₄, wr₄⟩ := test_ok s₂
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    refine ⟨finish hp (by omega) h rfl (fun r h1 h2 h3 h13 h14 => by rw [gpr₄, g r h1 h13 h14])
      (by rw [gpr₄, r13₂]) (by rw [gpr₄, r14₂]) (by rw [rd₄, rd₂']) (by rw [wr₄, wr₂'])
      (by rw [mem₄, m₂]; exact Frame.refl _ _) ?_, ?_⟩
    · rw [mem₄, m₂, h.iv (by have := lo32_mOf s₀ k; omega)]
    · rw [zf₄, zfEnd s₂ r14₂]

/-- One iteration. -/
theorem iter_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (body v.callee) s
      fun s' => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp v hk h a) fun _ hm => tail_wp hp hk hm))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.loop (body v.callee) .ne) s (LInv AesCtr.ctrMode s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body v.callee) (c := .ne) (Q := LInv AesCtr.ctrMode s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv AesCtr.ctrMode s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp v hj h) fun s' ⟨h', hz⟩ => ?_
  have hm0 := mOf_pos hj
  have hle := mOf_le s₀ j
  have ev : isa.eval .ne s' = some !decide (j + mOf s₀ j = N s₀) := by
    show VG.X86_64.eval .ne s' = _; simp [VG.X86_64.eval, hz]
  by_cases hz' : j + mOf s₀ j = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (j + mOf s₀ j), by omega, j + mOf s₀ j, rfl, by omega, h'⟩

end

/-- The whole function. -/
theorem crypt_wp (v : Ctr32Impl) {s₀ : State} (h0 : (modeX86_64 AesCtr.ctrMode).pre s₀) :
    WP isa (crypt v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ (modeX86_64 AesCtr.ctrMode).post s₀ s' :=
  ends_wp h0 fun hp hN _ h => loop_wp hp v hN h

end VG.Proof.AesCtr.X86_64
