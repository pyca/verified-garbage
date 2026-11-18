module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCfb
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedVerified
import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.Prepared
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Spec.Sm4.Cfb
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Proof.Modes.Fb
import VerifiedGarbage.Proof.Sm4.Arm.CfbGroup
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.MdStream.Arm.Common

/-! ### `Sm4.Arm.SerialCfbLoop`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.SerialCfbGroup`, which this module and modules that import it used -/

section

/-! # One prepared-key CFB encryption block -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCfbGroup

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions table_frame difference_zero)
open VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Modes.Arm
open VG.Impl.Modes.Arm (copyWord)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

structure GroupPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + 16
  left : s'.gpr .r7 = BitVec.ofNat 32 (n - 1)
  z : s'.z = decide (n = 1)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D 1) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 =
    Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (Spec.Sm4.cipher K (bytesAt s.mem (counterAddr B) 16))
  block : bytesAt s'.mem (State.addr D) 16 = bytesAt s'.mem (counterAddr B) 16

theorem save_wp {s : State} {B D : BitVec 32}
    (hB : s.gpr sb = B) (hD : s.gpr .r6 = D + 16)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩) :
    WP isa (.block SerialCfb.saveCipher) s fun s' =>
      (∀ r, r ≠ .r0 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨counterAddr B, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (State.addr D) 16 := by
  let a := s.setReg .r0 (s.gpr .r6 - 16)
  have ha : runBlock isa [.dp .sub .r0 .r6 (.imm 16)] s = some a := by rfl
  have h0 : a.gpr .r0 = D := by
    change s.gpr .r6 - 16 = D
    rw [hD, BitVec.add_sub_cancel]
  apply (WP.block_append_iff (M := isa) (l₁ := [.dp .sub .r0 .r6 (.imm 16)])
    (l₂ := (List.range 4).flatMap (copyWord sb .r0 (4 * BatchCtr.counterSlot) 0))).mpr
  refine WP.of_runBlock ⟨a, ha, ?_⟩
  have h8 : a.gpr sb = B := by simpa [a, State.setReg, sb] using hB
  have cp : NPre 4 a sb .r0 (4 * BatchCtr.counterSlot) 0 (counterAddr B) (State.addr D) := by
    refine ⟨?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      workspace_part hw 1492 16 (by decide), Covers.right wd, ?_⟩
    · rw [h8]
    · rw [h0]; simp
    · rw [h8]; change B.toNat + 1492 + 16 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at fitB; omega_using [fitB]
    · rw [h0]; exact fitD
    · exact (sep.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
  refine WP.mono (copyBlock_wp cp) fun s' h => ?_
  exact ⟨fun r h0' h9 h10 => (h.regs r h9 h10).trans (by simp [a, State.setReg, h0']),
    h.rd, h.wr, h.sp, h.frame, h.block⟩

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa SerialCfb.group s (GroupPost s B D K n) := by
  obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := movImm_ok s .r11 1 (by decide)
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.of_runBlock ⟨s₁, CfbFill.pad_run s₁, ?_⟩⟩))
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide)).trans hB
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide)).trans hD
  have wd₁ : Covers [⟨State.addr D, 16⟩] s₁.wr := by
    rw [wr₁]
    exact (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by simp,
        by change 0 + 16 ≤ 16 * n; omega_using [hn]⟩).trans wd
  have sep₁ := sep.sub_left (Region.sub_prefix (show 16 ≤ 16 * n by omega_using [hn]))
  refine WP.seq (WP.mono (CfbGroup.batch_wp (g := 1) (by decide) (by decide) b₁ d₁ g₁ fitB
    (by omega_using [hn, fitD]) (by rw [wr₁]; exact hw) wd₁ sep₁ (by rw [m₁]; exact hH)) fun s₂ b => ?_)
  have b₂ : s₂.gpr sb = B := (b.regs _ (by simp [sb])).trans b₁
  refine WP.seq (WP.mono (save_wp b₂ b.data fitB (by omega_using [hn, fitD])
    (by rw [b.wr, wr₁]; exact hw) (by rw [b.wr]; exact wd₁) sep₁)
    fun s₃ ⟨o₃, rd₃, wr₃, sp₃, f₃, c₃⟩ => ?_)
  have n₃ : s₃.gpr .r7 = BitVec.ofNat 32 n :=
    (o₃ _ (by decide) (by decide) (by decide)).trans
      ((b.regs _ (by simp)).trans ((o₁ _ (by decide)).trans hN))
  have g₃ : s₃.gpr .r11 = 1 :=
    (o₃ _ (by decide) (by decide) (by decide)).trans ((b.regs _ (by simp)).trans g₁)
  have out₂ : bytesAt s₂.mem (State.addr D) 16 =
      Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (Spec.Sm4.cipher K (bytesAt s.mem (counterAddr B) 16)) := by
    simpa [dataAddr, CfbGroup.inputBlock, m₁] using b.blocks 0 (by decide)
  have data₃ : bytesAt s₃.mem (State.addr D) 16 = bytesAt s₂.mem (State.addr D) 16 := by
    apply bytes_frame f₃
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.sub_right (Offset.sub_base _ (by decide))
  have frame₃ : Frame (batchRegions B D 1) s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
  have table₃ := table_frame b.table f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  obtain ⟨s₄, e₄, r₄, z₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := subsR_ok s₃ .r7 .r7 .r11
  refine WP.of_runBlock ⟨s₄, e₄, fun r hr => ?_, ?_, ?_, ?_,
    rd₄.trans (rd₃.trans (b.rd.trans rd₁)), wr₄.trans (wr₃.trans (b.wr.trans wr₁)),
    sp₄.trans (sp₃.trans (b.sp.trans sp₁)), ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [o₄ _ (by decide), o₃ _ (by decide) (by decide) (by decide), b.regs _ (by simp), o₁ _ (by decide)]
  · rw [o₄ _ (by decide), o₃ _ (by decide) (by decide) (by decide)]; exact b.data
  · rw [r₄, n₃, g₃]; exact Offset.ofNat_sub_ofNat hn
  · rw [z₄, n₃, g₃]; exact difference_zero hn32 hn
  · rw [m₄, ← m₁]; exact b.frame.trans frame₃
  · rw [m₄]; exact table₃
  · rw [m₄, c₃, out₂]
  · rw [m₄, data₃, c₃]

end VG.Proof.Sm4.Arm.SerialCfbGroup

end

end

/-! # The arbitrary-length prepared-key SM4-CFB encryption loop on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.SerialCfbLoop

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.SerialCfbGroup
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- Blocks at and after `i` are outside a frame writing only earlier data
blocks and the separate working space. -/
theorem future_data {m m' : Mem} {B D : BitVec 32} {n i j : Nat}
    (hn : n < 2 ^ 32) (hi : i ≤ j) (hj : j < n)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hf : Frame (batchRegions B D i) m m') : bytesAt m' (dataAddr D j) 16 = bytesAt m (dataAddr D j) 16 := by
  apply bytes_frame hf
  intro r hr
  simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_arith))
  · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

def chain (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (i : Nat) : List Byte :=
  Proof.Modes.fbIn .cfbEnc 16 (Spec.Sm4.cipher K) m (State.addr D) t i

def outBlock (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (j : Nat) : List Byte :=
  Proof.Modes.fbOut .cfbEnc 16 (Spec.Sm4.cipher K) m (State.addr D) t j

structure LoopInv (s₀ : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte)
    (n i : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s.gpr r = s₀.gpr r
  data : s.gpr .r6 = D + BitVec.ofNat 32 (16 * i)
  left : s.gpr .r7 = BitVec.ofNat 32 (n - i)
  bound : i ≤ n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (batchRegions B D i) s₀.mem s.mem
  table : Holds layout s.mem (State.addr B) K .encrypt
  counter : bytesAt s.mem (counterAddr B) 16 = chain s₀.mem D K t i
  blocks : ∀ j < i, bytesAt s.mem (dataAddr D j) 16 = outBlock s₀.mem D K t j

theorem loopInv_step {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : LoopInv s₀ B D K t n i s) :
    WP isa SerialCfb.group s fun s' =>
      LoopInv s₀ B D K t n (i + 1) s' ∧ s'.z = decide (i + 1 = n) := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  let g : Nat := 1
  have hg : 1 ≤ g := by dsimp only [g]; omega_arith
  have hgn : g ≤ n - i := by dsimp only [g]; omega_arith
  have hgi : i + g ≤ n := by omega_arith
  have diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega_arith)
  have diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega_arith)
  have subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega_arith)
  have wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr,
      by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_arith⟩
  have sb' : s.gpr sb = B := (h.regs _ (by simp [sb])).trans hB
  refine WP.mono (group_wp (by omega_arith) (by omega_arith) sb' h.data h.left fitB
    (by rw [diNat]; omega_arith) (by rw [h.wr]; exact hw) wdi (sep.sub_left subD) h.table)
    fun s' hs => ?_
  have fNew : Frame (batchRegions B D (i + g)) s.mem s'.mem := hs.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · refine ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], ?_⟩
      rw [diAddr]; exact Offset.sub_base _ (by omega_arith)
  have fOld : Frame (batchRegions B D (i + g)) s₀.mem s.mem := h.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · exact ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], Region.sub_prefix (by omega_arith)⟩
  refine ⟨⟨fun r hr => (hs.regs r hr).trans (h.regs r hr), ?_, ?_, hgi,
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, fOld.trans fNew, hs.table, ?_, ?_⟩, ?_⟩
  · rw [hs.data]
    change D + BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 (16 * g) = _
    rw [Offset.add_add]; congr 2
  · rw [hs.left, show n - i - 1 = n - (i + 1) by omega_arith]
  · rw [hs.counter]
    have ha : State.addr Di = dataAddr D i := diAddr
    rw [ha, future_data hn32 (by omega_arith) (by omega_arith) sep h.frame, h.counter]
    rfl
  · intro j hj
    by_cases hjOld : j < i
    · rw [bytes_frame (P := dataAddr D j) hs.frame (fun r hr => ?_), h.blocks j hjOld]
      simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
          (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_arith))
      · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
          (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
      · rw [diAddr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · have he : j = i := by dsimp only [g] at *; omega_arith
      subst j
      have ha : State.addr Di = dataAddr D i := diAddr
      rw [← ha, hs.block, hs.counter, ha,
        future_data hn32 (by omega_arith) (by omega_arith) sep h.frame, h.counter]
      rfl
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega_arith

theorem loop_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.loop SerialCfb.group .ne) s₀ (LoopInv s₀ B D K t n n) := by
  have hi : LoopInv s₀ B D K t n 0 s₀ :=
    ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
      by simpa only [Nat.sub_zero] using hN, by omega_arith, rfl, rfl, rfl, Frame.refl _ _, hH,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega_arith⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B D K t n i s)
    (fun m s hs => ?_) n s₀ ⟨0, by omega_arith, by omega_arith, hi⟩
  obtain ⟨i, rfl, hi, hs⟩ := hs
  refine WP.mono (loopInv_step hn32 hi hB fitB fitD hw wd sep hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : i + 1 = n
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      n - (i + 1), by omega_arith,
      i + 1, rfl, by have := h'.bound; omega_arith, h'⟩

theorem loopOrEmpty_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n) (hZ : s₀.z = decide (n = 0))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.ite .eq (.block []) (.loop SerialCfb.group .ne)) s₀ (LoopInv s₀ B D K t n n) := by
  refine WP.ite (decide (n = 0)) (by change some s₀.z = some (decide (n = 0)); rw [hZ]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = 0 := of_decide_eq_true hz
    subst hn
    exact WP.block_nil
      ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
        by simpa only [Nat.sub_zero] using hN, by omega_arith, rfl, rfl, rfl, Frame.refl _ _, hH,
        by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega_arith⟩
  · have hn : 1 ≤ n := by simp at hz; omega_arith
    exact loop_wp hn hn32 hB hD hN fitB fitD hw wd sep hH hC

theorem loop_output {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (h : LoopInv s₀ B D K t n n s) :
    Spec.Cbc.blocksAt s.mem (State.addr D) n =
      Spec.Cfb.encrypt (Spec.Sm4.cipher K) t (Spec.Cbc.blocksAt s₀.mem (State.addr D) n) := by
  rw [← Proof.Modes.blocksOf_16, ← (Proof.Modes.cfbEnc_of 16 (Spec.Sm4.cipher K) s₀.mem (State.addr D) t n).1]
  unfold Proof.Modes.blocksOf
  apply List.map_congr_left
  intro j hj
  exact h.blocks j (List.mem_range.mp hj)

theorem chain_next (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (n : Nat) :
    chain m D K t n = Spec.Cbc.next t
      (Spec.Cfb.encrypt (Spec.Sm4.cipher K) t (Spec.Cbc.blocksAt m (State.addr D) n)) :=
  (Proof.Modes.cfbEnc_of 16 (Spec.Sm4.cipher K) m (State.addr D) t n).2

end VG.Proof.Sm4.Arm.SerialCfbLoop

end

end

/-! # Public registers across SM4-CFB encryption's helper calls -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCfbHead

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchGroup
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchEntry
open VG.Proof.Sm4.Prepared (Holds)

def groupHead : Prog isa := .seq SerialCfb.count (.seq BatchCfb.fill BatchCtr.crypt)
def groupTail : Prog isa := .seq BatchCtr.xorGroup
  (.seq (.block SerialCfb.saveCipher) (.block [.subs .r7 .r7 (.reg .r11)]))
structure HeadPre (B D : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  left : s.gpr .r7 = BitVec.ofNat 32 n
  fit : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  writable : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  table : ∃ K, Holds layout s.mem (State.addr B) K .encrypt
  data : s.gpr .r6 = D
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  wdata : Covers [⟨State.addr D, 16 * n⟩] s.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

structure HeadPost (s : State) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r6, .r7, .r8], s'.gpr r = s.gpr r
  group : s'.gpr .r11 = BitVec.ofNat 32 (1)

theorem count_wp (s : State) : WP isa SerialCfb.count s fun s' =>
    s'.gpr .r11 = (1 : BitVec 32) ∧
      (∀ r, r ≠ .r11 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s', e, g, o, m, rd, wr, sp⟩ := movImm_ok s .r11 1 (by decide)
  exact WP.seq (WP.of_runBlock ⟨s', e, WP.of_runBlock
    ⟨s', CfbFill.pad_run s', g, fun r hr _ => o r hr, m, rd, wr, sp⟩⟩)

theorem head_wp {s : State} {B D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (_hn32 : n < 2 ^ 32)
    (h : HeadPre B D n s) : WP isa groupHead s (HeadPost s n) := by
  have hg : 1 ≤ 1 := by omega_using []
  have hg8 : 1 ≤ 8 := by decide
  obtain ⟨K, hH⟩ := h.table
  refine WP.seq (WP.mono (count_wp s) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans h.base
  have table₁ : Holds layout s₁.mem (State.addr B) K .encrypt := by
    rw [m₁]; exact hH
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans h.data
  have wd₁ : Covers [⟨State.addr D, 16 * 1⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wdata
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero],
      by change 0 + 16 * 1 ≤ 16 * n; omega_using [hn]⟩
  have fp : CfbFill.Pre B D (1) s₁ := ⟨b₁, d₁, g₁, h.fit, by have := h.fitD; omega_using [hn, this],
    by rw [wr₁]; exact h.writable, wd₁, h.sep.sub_left (Region.sub_prefix (by omega_using [hn]))⟩
  refine WP.seq (WP.mono (CfbFill.fill_wp fp hg hg8) fun s₂ f => ?_)
  have b₂ : s₂.gpr sb = B := (f.regs _ (by decide) (by decide)).trans b₁
  have table₂ : Holds layout s₂.mem (State.addr B) K .encrypt := table_frame table₁ f.frame fun r hr => by
    simp only [CfbFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 128 ≤ 384; decide
      · decide
      · change 4 * tailSlot + 16 * 0 + 128 ≤ 2 ^ 64; rw [tailSlot]; omega_using []
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₂.wr := by
    rw [f.wr, wr₁]
    simpa only [BitVec.add_zero] using workspace_part h.writable 0 (4 * slots)
      (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; decide)
  refine WP.mono (BatchCalls.crypt_wp b₂ (by have := h.fit; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this]) wc table₂)
    fun s₃ ⟨c, _, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide), g₁]; rfl


theorem loop_pre {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (_hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : SerialCfbLoop.LoopInv s₀ B D K t n i s) : HeadPre B (D + BitVec.ofNat 32 (16 * i)) (n - i) s := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  have diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega_using [hi, fitD])
  have diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega_using [hi, fitD])
  have subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega_using [hi])
  have wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr, by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_using [hi]⟩
  exact ⟨(h.regs _ (by simp [sb])).trans hB, h.left, fitB, by rw [h.wr]; exact hw,
    ⟨K, h.table⟩, h.data, by change Di.toNat + 16 * (n - i) ≤ 2 ^ 32; rw [diNat]; omega_using [hi, fitD], wdi, sep.sub_left subD⟩

end VG.Proof.Sm4.Arm.SerialCfbHead
