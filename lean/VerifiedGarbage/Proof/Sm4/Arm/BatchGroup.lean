module

import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
public import VerifiedGarbage.Proof.Sm4.Arm.BatchXor
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # One complete batch of SM4-CTR on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchGroup

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR lsrOp)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- Block `j` of an ECB batch. -/
theorem blockAt_of_ecb {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Sm4.blocksAt m' D n = Spec.Sm4.ecb K d (Spec.Sm4.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Sm4.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Sm4.blockFn K d (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have h' := congrArg (fun l => l[j]?) h
  rw [Proof.Sm4.ecb_eq] at h'
  simpa [Spec.Sm4.blocksAt, hj] using h'

theorem encrypted_lane {K : Spec.Sm4.Schedule} {m m' : Mem} {B : BitVec 32}
    (h : Spec.Sm4.blocksAt m' (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb K .encrypt (Spec.Sm4.blocksAt m (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks))
    {j : Nat} (hj : j < 8) :
    bytesAt m' (bufferAddr B j) 16 = Spec.Sm4.cipher K (bytesAt m (bufferAddr B j) 16) := by
  have hb := blockAt_of_ecb h hj
  have ha : State.addr B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) = bufferAddr B j := by
    rw [Offset.add_add]; rfl
  rw [ha] at hb
  rw [Proof.Sm4.bytesAt_eq_blockAt, hb]
  rw [Spec.Sm4.cipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]
  rfl

/-- The key table survives writes disjoint from its one contiguous range. -/
theorem table_frame {m m' : Mem} {B : BitVec 32} {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    {rs : List Region} (h : Holds layout m (State.addr B) K d) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr B + BitVec.ofNat 64 384, 1024⟩ r) :
    Holds layout m' (State.addr B) K d := by
  intro r hr i hi
  rw [layout_table, List.mem_singleton] at hr
  subst hr
  dsimp only at hi ⊢
  rw [← Offset.add_add, hf.bytes hd (by change 1024 ≤ 2 ^ 64; decide) hi]
  change m (State.addr B + BitVec.ofNat 64 384 + BitVec.ofNat 64 i) = _
  rw [Offset.add_add]
  exact h (384, 1024) (by rw [layout_table]; simp) i hi

/-- Choose `min(n, 8)` useful counter lanes. -/
theorem count_wp {s : State} {v : Nat} (hn : s.gpr .r7 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa BatchCtr.count s fun s' => s'.gpr .r11 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r11 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₂ := s.setReg .r10 (s.gpr .r7 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr .r10) 0
  have e₂₃ : runBlock isa [.mov .r10 (lsrOp .r7 3), .cmp .r10 (.imm 0)] s = some s₃ := by
    rw [runBlock_cons, show exec (.mov .r10 (lsrOp .r7 3)) s = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp .r10 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  have z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr .r10 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, hn]
  have o₃ : ∀ r, r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  have r7₃ : s₃.gpr .r7 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), hn]
  unfold BatchCtr.count
  refine WP.seq (WP.of_runBlock ⟨s₃, e₂₃, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_arith)) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r11 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega_arith)]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r11 .r7
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, r7₃, Nat.min_eq_left (by simp at h; omega_arith)]

/-- Writes of one batch: the core's workspace, its running counter, and
the useful data blocks. The saved mode registers lie outside all three. -/
def batchRegions (B D : BitVec 32) (g : Nat) : List Region :=
  [⟨State.addr B, 4 * slots⟩, ⟨counterAddr B, 16⟩, ⟨State.addr D, 16 * g⟩]

structure BatchPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (g : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r7, .r8, .r11], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * g)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D g) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) g
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) k))

theorem batch_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {g : Nat}
    (hg : 1 ≤ g) (hg8 : g ≤ 8) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hG : s.gpr .r11 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr.batch s (BatchPost s B D K g) := by
  refine WP.seq (WP.mono (fill_wp hg hg8 hB hG fitB hw) fun s₁ f₁ => ?_)
  have sb₁ : s₁.gpr sb = B := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hB
  have r6₁ : s₁.gpr .r6 = D := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hD
  have r11₁ : s₁.gpr .r11 = BitVec.ofNat 32 g :=
    (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hG
  have hH₁ : Holds layout s₁.mem (State.addr B) K .encrypt := table_frame hH f₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 16 * g ≤ 384; rw [tailSlot]; omega_arith
      · decide
      · change 4 * tailSlot + 16 * 0 + 16 * g ≤ 2 ^ 64; rw [tailSlot]; omega_arith
    · apply Offset.disjoint (State.addr B)
      · left; change 384 + 1024 ≤ 4 * BatchCtr.counterSlot; decide
      · decide
      · decide
  have f₁wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.mem s₁.mem :=
    f₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_arith)⟩
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by decide)⟩
  have f₁batch : Frame (batchRegions B D g) s.mem s₁.mem := f₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr B, 4 * slots⟩, List.mem_cons_self,
        Offset.sub_base _ (by rw [tailSlot, slots_eq]; omega_arith)⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
  have wc₁ : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f₁.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots) (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_arith)
  refine WP.seq (WP.mono (BatchCalls.crypt_wp sb₁ (by rw [total_eq] at fitB; rw [slots_eq]; omega_arith) wc₁ hH₁)
    fun s₂ ⟨c₂, table₂, ecb₂⟩ => ?_)
  have sb₂ : s₂.gpr sb = B := (c₂.regs _ (by decide) (by decide)).trans sb₁
  have r6₂ : s₂.gpr .r6 = D := (c₂.regs _ (by decide) (by decide)).trans r6₁
  have r11₂ : s₂.gpr .r11 = BitVec.ofNat 32 g := (c₂.regs _ (by decide) (by decide)).trans r11₁
  have c₂wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₁.mem s₂.mem :=
    c₂.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
        Region.sub_prefix (by rw [slots_eq, total_eq]; omega_arith)⟩
  have c₂batch : Frame (batchRegions B D g) s₁.mem s₂.mem :=
    c₂.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  have phaseFrame := f₁wide.trans c₂wide
  have counter₂ : bytesAt s₂.mem (counterAddr B) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) g := by
    rw [bytes_frame c₂.frame (fun r hr => ?_), f₁.counter]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by rw [slots_eq, counter_eq]; omega_arith) (by decide)
  have cipher₂ : ∀ k < g, bytesAt s₂.mem (bufferAddr B k) 16 =
      Spec.Sm4.cipher K (Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) k) := by
    intro k hk
    rw [encrypted_lane ecb₂ (by omega_arith), f₁.lanes k hk]
  have plain₂ : ∀ k < g, bytesAt s₂.mem (dataAddr D k) 16 = bytesAt s.mem (dataAddr D k) 16 := by
    intro k hk
    apply bytes_frame phaseFrame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.sub_left (Offset.sub_base _ (by omega_arith))
  refine WP.mono (xor_wp hg hg8 sb₂ r6₂ r11₂ fitB fitD
    (by rw [c₂.wr, f₁.wr]; exact hw) (by rw [c₂.wr, f₁.wr]; exact wd) sep) fun s₃ x₃ => ?_
  have table₃ : Holds layout s₃.mem (State.addr B) K .encrypt := table_frame table₂ x₃.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.symm.sub_left (Offset.sub_base _ (by change 384 + 1024 ≤ 4 * BatchCtr.totalSlots; rw [total_eq]; omega_arith))
  have counter₃ : bytesAt s₃.mem (counterAddr B) 16 = bytesAt s₂.mem (counterAddr B) 16 := by
    apply bytes_frame x₃.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.symm.sub_left (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
  refine ⟨fun r hr => ?_, x₃.data, x₃.rd.trans (c₂.rd.trans f₁.rd), x₃.wr.trans (c₂.wr.trans f₁.wr),
    x₃.sp.trans (c₂.sp.trans f₁.sp),
    (f₁batch.trans c₂batch).trans (x₃.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]), table₃,
    counter₃.trans counter₂, fun k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [x₃.regs _ (by decide) (by decide) (by decide) (by decide) (by decide),
        c₂.regs _ (by decide) (by decide), f₁.regs _ (by decide) (by decide) (by decide) (by decide)]
  · rw [x₃.blocks k hk, plain₂ k hk, cipher₂ k hk]

theorem difference_zero {n g : Nat} (hn : n < 2 ^ 32) (hg : g ≤ n) :
    (BitVec.ofNat 32 n - BitVec.ofNat 32 g == 0) = decide (n = g) := by
  rw [Offset.ofNat_sub_ofNat hg, Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at hnat
    have : (0 : BitVec 32).toNat = 0 := rfl
    rw [this] at hnat
    omega_arith
  · intro h; subst h; simp

structure GroupPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * min n 8)
  left : s'.gpr .r7 = BitVec.ofNat 32 (n - min n 8)
  z : s'.z = decide (n = min n 8)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D (min n 8)) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) (min n 8)
  blocks : ∀ k < min n 8, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) k))

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr.group s (GroupPost s B D K n) := by
  have hgN : min n 8 ≤ n := Nat.min_le_left _ _
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  have hg : 1 ≤ min n 8 := by omega_arith
  refine WP.seq (WP.mono (count_wp hN hn32) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans hB
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans hD
  have n₁ : s₁.gpr .r7 = BitVec.ofNat 32 n := (o₁ _ (by decide) (by decide)).trans hN
  have wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero],
      by change 0 + 16 * min n 8 ≤ 16 * n; omega_arith⟩
  refine WP.seq (WP.mono (batch_wp hg hg8 b₁ d₁ g₁ fitB (by omega_arith)
    (by rw [wr₁]; exact hw) wd₁ (sep.sub_left (Region.sub_prefix (by omega_arith)))
    (by rw [m₁]; exact hH)) fun s₂ b₂ => ?_)
  have n₂ : s₂.gpr .r7 = BitVec.ofNat 32 n := (b₂.regs _ (by simp)).trans n₁
  have g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (min n 8) := (b₂.regs _ (by simp)).trans g₁
  obtain ⟨s₃, e₃, r₃, z₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := subsR_ok s₂ .r7 .r7 .r11
  refine WP.of_runBlock ⟨s₃, e₃, fun r hr => ?_, ?_, ?_, ?_,
    rd₃.trans (b₂.rd.trans rd₁), wr₃.trans (b₂.wr.trans wr₁), sp₃.trans (b₂.sp.trans sp₁), ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [o₃ _ (by decide), b₂.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [o₃ _ (by decide)]; exact b₂.data
  · rw [r₃, n₂, g₂]; exact Offset.ofNat_sub_ofNat hgN
  · rw [z₃, n₂, g₂]; exact difference_zero hn32 hgN
  · rw [m₃, ← m₁]; exact b₂.frame
  · rw [m₃]; exact b₂.table
  · rw [m₃, ← m₁]; exact b₂.counter
  · intro k hk
    rw [m₃, b₂.blocks k hk, m₁]

end VG.Proof.Sm4.Arm.BatchGroup
