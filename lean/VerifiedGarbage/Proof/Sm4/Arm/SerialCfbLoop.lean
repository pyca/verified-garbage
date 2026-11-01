module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCfb
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbGroup
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Spec.Sm4.Cfb
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Proof.Modes.Fb
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared

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
