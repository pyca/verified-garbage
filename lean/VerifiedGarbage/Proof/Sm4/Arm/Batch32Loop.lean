module

import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Fill
public import VerifiedGarbage.Proof.Sm4.Arm.BatchXor
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Proof.Sm4.Arm.Group
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Sm4
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.BatchLoop
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Sm4.Arm.Batch32Group`, which only this module used -/

section

/-! # One complete batch of SM4's counter mode with `inc₃₂` on ARMv7

As `BatchGroup`, with the lanes filled by `Batch32Fill`. -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Group

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR lsrOp)
open VG.Proof.Sm4.Arm.BatchFill (counterAddr bufferAddr total_eq counter_eq workspace_part bytes_frame)
open VG.Proof.Sm4.Arm.BatchXor (dataAddr xor_wp)
open VG.Proof.Sm4.Arm.BatchGroup (table_frame count_wp encrypted_lane batchRegions difference_zero)
open VG.Proof.Sm4.Arm.Batch32Fill (next32 fill_wp)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

structure BatchPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (g : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r7, .r8, .r11], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * g)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D g) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = next32 (bytesAt s.mem (counterAddr B) 16) g
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (next32 (bytesAt s.mem (counterAddr B) 16) k))

theorem batch_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {g : Nat}
    (hg : 1 ≤ g) (hg8 : g ≤ 8) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hG : s.gpr .r11 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr32.batch s (BatchPost s B D K g) := by
  refine WP.seq (WP.mono (fill_wp hg hg8 hB hG fitB hw) fun s₁ f₁ => ?_)
  obtain sb₁ : s₁.gpr sb = B := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hB
  obtain r6₁ : s₁.gpr .r6 = D := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hD
  obtain r11₁ : s₁.gpr .r11 = BitVec.ofNat 32 g :=
    (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hG
  obtain hH₁ : Holds layout s₁.mem (State.addr B) K .encrypt := table_frame hH f₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 16 * g ≤ 384; rw [tailSlot]; omega_using [hg8]
      · decide
      · change 4 * tailSlot + 16 * 0 + 16 * g ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg8]
    · apply Offset.disjoint (State.addr B)
      · left; change 384 + 1024 ≤ 4 * BatchCtr.counterSlot; decide
      · decide
      · decide
  obtain f₁wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.mem s₁.mem :=
    f₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg8])⟩
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by decide)⟩
  obtain f₁batch : Frame (batchRegions B D g) s.mem s₁.mem := f₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr B, 4 * slots⟩, List.mem_cons_self,
        Offset.sub_base _ (by rw [tailSlot, slots_eq]; omega_using [hg8])⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
  obtain wc₁ : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f₁.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots) (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using [])
  refine WP.seq (WP.mono (BatchCalls.crypt_wp sb₁ (by rw [total_eq] at fitB; rw [slots_eq]; omega_using [fitB]) wc₁ hH₁)
    fun s₂ ⟨c₂, table₂, ecb₂⟩ => ?_)
  obtain sb₂ : s₂.gpr sb = B := (c₂.regs _ (by decide) (by decide)).trans sb₁
  obtain r6₂ : s₂.gpr .r6 = D := (c₂.regs _ (by decide) (by decide)).trans r6₁
  obtain r11₂ : s₂.gpr .r11 = BitVec.ofNat 32 g := (c₂.regs _ (by decide) (by decide)).trans r11₁
  obtain c₂wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₁.mem s₂.mem :=
    c₂.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
        Region.sub_prefix (by rw [slots_eq, total_eq]; omega_using [])⟩
  obtain c₂batch : Frame (batchRegions B D g) s₁.mem s₂.mem :=
    c₂.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  obtain phaseFrame := f₁wide.trans c₂wide
  obtain counter₂ : bytesAt s₂.mem (counterAddr B) 16 = next32 (bytesAt s.mem (counterAddr B) 16) g := by
    rw [bytes_frame c₂.frame (fun r hr => ?_), f₁.counter]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by rw [slots_eq, counter_eq]; omega_using []) (by decide)
  obtain cipher₂ : ∀ k < g, bytesAt s₂.mem (bufferAddr B k) 16 =
      Spec.Sm4.cipher K (next32 (bytesAt s.mem (counterAddr B) 16) k) := by
    intro k hk
    rw [encrypted_lane ecb₂ (by omega_using [hg8, hk]), f₁.lanes k hk]
  obtain plain₂ : ∀ k < g, bytesAt s₂.mem (dataAddr D k) 16 = bytesAt s.mem (dataAddr D k) 16 := by
    intro k hk
    apply bytes_frame phaseFrame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.sub_left (Offset.sub_base _ (by omega_using [hk]))
  refine WP.mono (xor_wp hg hg8 sb₂ r6₂ r11₂ fitB fitD
    (by rw [c₂.wr, f₁.wr]; exact hw) (by rw [c₂.wr, f₁.wr]; exact wd) sep) fun s₃ x₃ => ?_
  obtain table₃ : Holds layout s₃.mem (State.addr B) K .encrypt := table_frame table₂ x₃.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.symm.sub_left (Offset.sub_base _ (by change 384 + 1024 ≤ 4 * BatchCtr.totalSlots; rw [total_eq]; omega_using []))
  obtain counter₃ : bytesAt s₃.mem (counterAddr B) 16 = bytesAt s₂.mem (counterAddr B) 16 := by
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
  counter : bytesAt s'.mem (counterAddr B) 16 = next32 (bytesAt s.mem (counterAddr B) 16) (min n 8)
  blocks : ∀ k < min n 8, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (next32 (bytesAt s.mem (counterAddr B) 16) k))

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr32.group s (GroupPost s B D K n) := by
  obtain hgN : min n 8 ≤ n := Nat.min_le_left _ _
  obtain hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  obtain hg : 1 ≤ min n 8 := by omega_using [hn]
  refine WP.seq (WP.mono (count_wp hN hn32) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  obtain b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans hB
  obtain d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans hD
  obtain n₁ : s₁.gpr .r7 = BitVec.ofNat 32 n := (o₁ _ (by decide) (by decide)).trans hN
  obtain wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero],
      by change 0 + 16 * min n 8 ≤ 16 * n; omega_using []⟩
  refine WP.seq (WP.mono (batch_wp hg hg8 b₁ d₁ g₁ fitB (by omega_using [fitD])
    (by rw [wr₁]; exact hw) wd₁ (sep.sub_left (Region.sub_prefix (by omega_using [])))
    (by rw [m₁]; exact hH)) fun s₂ b₂ => ?_)
  obtain n₂ : s₂.gpr .r7 = BitVec.ofNat 32 n := (b₂.regs _ (by simp)).trans n₁
  obtain g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (min n 8) := (b₂.regs _ (by simp)).trans g₁
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

end VG.Proof.Sm4.Arm.Batch32Group

end

end


/-! # The arbitrary-length batched loop of SM4's counter mode with `inc₃₂` on ARMv7

As `BatchLoop`, with the batches of `Batch32Group`. -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Loop

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill (counterAddr total_eq offset_nat bytes_frame fill_eval_ne)
open VG.Proof.Sm4.Arm.BatchXor (dataAddr)
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions)
open VG.Proof.Sm4.Arm.BatchLoop (future_data)
open VG.Proof.Sm4.Arm.Batch32Fill (next32 next32_add)
open VG.Proof.Sm4.Arm.Batch32Group
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- The intended block at index `j`, from the original data and counter. -/
def outBlock (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (j : Nat) : List Byte :=
  Spec.Cbc.xor (bytesAt m (dataAddr D j) 16) (Spec.Sm4.cipher K (next32 t j))

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
  counter : bytesAt s.mem (counterAddr B) 16 = next32 t i
  blocks : ∀ j < i, bytesAt s.mem (dataAddr D j) 16 = outBlock s₀.mem D K t j

theorem loopInv_step {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : LoopInv s₀ B D K t n i s) :
    WP isa BatchCtr32.group s fun s' =>
      LoopInv s₀ B D K t n (i + min (n - i) 8) s' ∧ s'.z = decide (i + min (n - i) 8 = n) := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  let g := min (n - i) 8
  obtain hg : 1 ≤ g := by dsimp only [g]; omega_using [hi]
  obtain hgn : g ≤ n - i := Nat.min_le_left _ _
  obtain hgi : i + g ≤ n := by omega_using [hi]
  obtain diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega_using [hi, fitD])
  obtain diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega_using [hi, fitD])
  obtain subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega_using [hi])
  obtain wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr,
      by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_using [hi]⟩
  obtain sb' : s.gpr sb = B := (h.regs _ (by simp [sb])).trans hB
  refine WP.mono (group_wp (by omega_using [hi]) (by omega_using [hn32]) sb' h.data h.left fitB
    (by rw [diNat]; omega_using [hi, fitD]) (by rw [h.wr]; exact hw) wdi (sep.sub_left subD) h.table)
    fun s' hs => ?_
  obtain fNew : Frame (batchRegions B D (i + g)) s.mem s'.mem := hs.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · refine ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], ?_⟩
      rw [diAddr]; exact Offset.sub_base _ (by omega_using [])
  obtain fOld : Frame (batchRegions B D (i + g)) s₀.mem s.mem := h.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · exact ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], Region.sub_prefix (by omega_using [])⟩
  refine ⟨⟨fun r hr => (hs.regs r hr).trans (h.regs r hr), ?_, ?_, hgi,
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, fOld.trans fNew, hs.table, ?_, ?_⟩, ?_⟩
  · rw [hs.data]
    change D + BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 (16 * g) = _
    rw [Offset.add_add]; congr 2; omega_using []
  · rw [hs.left, show n - i - min (n - i) 8 = n - (i + min (n - i) 8) by omega_using []]
  · rw [hs.counter, h.counter, ← next32_add]
  · intro j hj
    by_cases hjOld : j < i
    · rw [bytes_frame (P := dataAddr D j) hs.frame (fun r hr => ?_), h.blocks j hjOld]
      simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Offset.sub_base _ (by omega_using [hi, hj]))).sub_right
          (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using []))
      · exact (sep.sub_left (Offset.sub_base _ (by omega_using [hi, hj]))).sub_right
          (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
      · rw [diAddr]
        exact Offset.disjoint _ (.inl (by omega_using [hjOld])) (by omega_using [hn32, hi, hj]) (by omega_using [hn32, hi])
    · have hjG : j - i < g := by omega_using [hi, hj]
      obtain ha : dataAddr Di (j - i) = dataAddr D j := by
        change State.addr Di + BitVec.ofNat 64 (16 * (j - i)) = _
        rw [diAddr, Offset.add_add]
        congr 2; omega_using [hjOld]
      obtain hb := hs.blocks (j - i) hjG
      rw [ha, future_data hn32 (by omega_using [hjOld]) (by omega_using [hi, hj]) sep h.frame, h.counter, ← next32_add,
        show i + (j - i) = j by omega_using [hjOld]] at hb
      exact hb
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega_using [hi]

theorem loop_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.loop BatchCtr32.group .ne) s₀ (LoopInv s₀ B D K t n n) := by
  obtain hi : LoopInv s₀ B D K t n 0 s₀ :=
    ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
      by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _, hH,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B D K t n i s)
    (fun m s hs => ?_) n s₀ ⟨0, by omega_using [], by omega_using [hn], hi⟩
  obtain ⟨i, rfl, hi, hs⟩ := hs
  refine WP.mono (loopInv_step hn32 hi hB fitB fitD hw wd sep hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : i + min (n - i) 8 = n
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      n - (i + min (n - i) 8), by omega_using [hi],
      i + min (n - i) 8, rfl, by have := h'.bound; omega_using [hi, he], h'⟩

theorem loopOrEmpty_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n) (hZ : s₀.z = decide (n = 0))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.ite .eq (.block []) (.loop BatchCtr32.group .ne)) s₀ (LoopInv s₀ B D K t n n) := by
  refine WP.ite (decide (n = 0)) (by change some s₀.z = some (decide (n = 0)); rw [hZ]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = 0 := of_decide_eq_true hz
    subst hn
    exact WP.block_nil
      ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
        by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _, hH,
        by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  · have hn : 1 ≤ n := by simp at hz; omega_using [hz]
    exact loop_wp hn hn32 hB hD hN fitB fitD hw wd sep hH hC

end VG.Proof.Sm4.Arm.Batch32Loop
