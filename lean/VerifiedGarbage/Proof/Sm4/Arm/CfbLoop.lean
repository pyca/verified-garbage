module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Proof.Sm4.Arm.CfbGroup
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # The arbitrary-length batched SM4-CFB decryption loop on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.CfbLoop

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.CfbGroup
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
  · exact (sep.sub_left (Offset.sub_base _ (by omega))).sub_right
      (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega))
  · exact (sep.sub_left (Offset.sub_base _ (by omega))).sub_right
      (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
  · exact Offset.disjoint_base _ (by omega) (by omega)

def chain (m : Mem) (D : BitVec 32) (t : List Byte) (i : Nat) : List Byte :=
  if i = 0 then t else bytesAt m (dataAddr D (i - 1)) 16

/-- CFB decryption's block at index `j`, from the original ciphertext. -/
def outBlock (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (j : Nat) : List Byte :=
  Spec.Cbc.xor (bytesAt m (dataAddr D j) 16) (Spec.Sm4.cipher K (chain m D t j))

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
  counter : bytesAt s.mem (counterAddr B) 16 = chain s₀.mem D t i
  blocks : ∀ j < i, bytesAt s.mem (dataAddr D j) 16 = outBlock s₀.mem D K t j

theorem loopInv_step {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : LoopInv s₀ B D K t n i s) :
    WP isa BatchCfb.group s fun s' =>
      LoopInv s₀ B D K t n (i + min (n - i) 8) s' ∧ s'.z = decide (i + min (n - i) 8 = n) := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  let g := min (n - i) 8
  have hg : 1 ≤ g := by dsimp only [g]; omega_arith
  have hgn : g ≤ n - i := Nat.min_le_left _ _
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
    rw [Offset.add_add]; congr 2; omega_arith
  · rw [hs.left, show n - i - min (n - i) 8 = n - (i + min (n - i) 8) by omega_arith]
  · rw [hs.counter]
    have ha : dataAddr Di (g - 1) = dataAddr D (i + g - 1) := by
      change State.addr Di + BitVec.ofNat 64 (16 * (g - 1)) = _
      rw [diAddr, Offset.add_add]
      congr 2; omega_arith
    rw [ha, future_data hn32 (by omega_arith) (by omega_arith) sep h.frame]
    simp only [chain, show i + min (n - i) 8 ≠ 0 by omega_arith, ↓reduceIte]
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
    · have hjG : j - i < g := by omega_arith
      have ha : dataAddr Di (j - i) = dataAddr D j := by
        change State.addr Di + BitVec.ofNat 64 (16 * (j - i)) = _
        rw [diAddr, Offset.add_add]
        congr 2; omega_arith
      have hb := hs.blocks (j - i) hjG
      rw [ha, future_data hn32 (by omega_arith) (by omega_arith) sep h.frame] at hb
      have inp : inputBlock s.mem B Di (j - i) = chain s₀.mem D t j := by
        by_cases he : j = i
        · subst j
          simpa only [inputBlock, Nat.sub_self, ↓reduceIte] using h.counter
        · have ne : j - i ≠ 0 := by omega_arith
          have az : dataAddr Di (j - i - 1) = dataAddr D (j - 1) := by
            change State.addr Di + BitVec.ofNat 64 (16 * (j - i - 1)) = _
            rw [diAddr, Offset.add_add]
            congr 2; omega_arith
          simp only [inputBlock, ne, ↓reduceIte, chain, show j ≠ 0 by omega_arith]
          rw [az, future_data hn32 (by omega_arith) (by omega_arith) sep h.frame]
      rw [inp] at hb
      exact hb
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
    WP isa (.loop BatchCfb.group .ne) s₀ (LoopInv s₀ B D K t n n) := by
  have hi : LoopInv s₀ B D K t n 0 s₀ :=
    ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
      by simpa only [Nat.sub_zero] using hN, by omega, rfl, rfl, rfl, Frame.refl _ _, hH,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B D K t n i s)
    (fun m s hs => ?_) n s₀ ⟨0, by omega, by omega, hi⟩
  obtain ⟨i, rfl, hi, hs⟩ := hs
  refine WP.mono (loopInv_step hn32 hi hB fitB fitD hw wd sep hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : i + min (n - i) 8 = n
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      n - (i + min (n - i) 8), by omega,
      i + min (n - i) 8, rfl, by have := h'.bound; omega, h'⟩

theorem loopOrEmpty_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n) (hZ : s₀.z = decide (n = 0))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.ite .eq (.block []) (.loop BatchCfb.group .ne)) s₀ (LoopInv s₀ B D K t n n) := by
  refine WP.ite (decide (n = 0)) (by change some s₀.z = some (decide (n = 0)); rw [hZ]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = 0 := of_decide_eq_true hz
    subst hn
    exact WP.block_nil
      ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
        by simpa only [Nat.sub_zero] using hN, by omega, rfl, rfl, rfl, Frame.refl _ _, hH,
        by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  · have hn : 1 ≤ n := by simp at hz; omega
    exact loop_wp hn hn32 hB hD hN fitB fitD hw wd sep hH hC

/-- The shared recursive CFB decryption specification, by block index. -/
theorem decrypt_eq (ciph : Spec.Cbc.Cipher) :
    ∀ (cs : List (List Byte)) (iv : List Byte), Spec.Cfb.decrypt ciph iv cs =
      (List.range cs.length).map fun j => Spec.Cbc.xor (cs.getD j [])
        (ciph (if j = 0 then iv else cs.getD (j - 1) []))
  | [], _ => rfl
  | c :: cs, iv => by
    rw [Spec.Cfb.decrypt, decrypt_eq ciph cs c, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congrArg _ (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply, List.getD_cons_succ, Nat.succ_ne_zero, ite_false]
    cases j <;> simp

theorem blocks_getD {m : Mem} {D : BitVec 32} {n k : Nat} (hk : k < n) :
    (Spec.Cbc.blocksAt m (State.addr D) n).getD k [] = bytesAt m (dataAddr D k) 16 := by
  rw [← List.getElem_eq_getD (h := by simp only [Spec.Cbc.blocksAt, List.length_map, List.length_range]; exact hk) []]
  simp only [Spec.Cbc.blocksAt, List.getElem_map, List.getElem_range]

theorem loop_output {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (h : LoopInv s₀ B D K t n n s) :
    Spec.Cbc.blocksAt s.mem (State.addr D) n =
      Spec.Cfb.decrypt (Spec.Sm4.cipher K) t (Spec.Cbc.blocksAt s₀.mem (State.addr D) n) := by
  rw [decrypt_eq, show (Spec.Cbc.blocksAt s₀.mem (State.addr D) n).length = n by simp [Spec.Cbc.blocksAt]]
  conv => lhs; unfold Spec.Cbc.blocksAt
  apply List.map_congr_left
  intro j hj
  have hjn := List.mem_range.mp hj
  rw [blocks_getD hjn, h.blocks j hjn]
  unfold outBlock chain
  by_cases he : j = 0
  · simp only [he, ↓reduceIte]
  · simp only [he, ↓reduceIte]
    rw [blocks_getD (by omega)]

theorem chain_next (m : Mem) (D : BitVec 32) (t : List Byte) (n : Nat) :
    chain m D t n = Spec.Cbc.next t (Spec.Cbc.blocksAt m (State.addr D) n) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [Spec.Cbc.blocksAt, Spec.Cbc.next, Proof.Modes.getLastD_map_range]
    simp only [chain, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]

end VG.Proof.Sm4.Arm.CfbLoop
