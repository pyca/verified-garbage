module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.Prologue
import VerifiedGarbage.Proof.Modes.CbcNext
public import VerifiedGarbage.Proof.Modes.CbcEnc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbHead
import VerifiedGarbage.Proof.Sm4.Arm.SerialOfbGroup
import VerifiedGarbage.Proof.Sm4.Arm.Group
public import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Modes.Arm.Cbc

/-! ### `Sm4.Arm.SerialCbcGroup`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.SerialCbcCore`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.SerialCbcFill`, which this module and modules that import it used -/

section

/-! # CBC encryption's input and output copies -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcFill

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

theorem count_wp (s : State) : WP isa SerialCbc.count s fun s' =>
    s'.gpr .r11 = (1 : BitVec 32) ∧
      (∀ r, r ≠ .r11 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine WP.seq (WP.mono (SerialCfbHead.count_wp s) fun s' h => ?_)
  exact WP.of_runBlock ⟨s', CfbFill.pad_run s', h⟩

structure Post (s : State) (B D : BitVec 32) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B 0, 16⟩] s.mem s'.mem
  block : bytesAt s'.mem (bufferAddr B 0) 16 =
    Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (bytesAt s.mem (counterAddr B) 16)

theorem fill_wp {s : State} {B D : BitVec 32} (h : CfbFill.Pre B D 1 s) :
    WP isa SerialCbc.fill s (Post s B D) := by
  refine WP.seq (WP.mono (CfbFill.first_wp h) fun s₁ f => ?_)
  have hb : s₁.gpr sb = B := (f.regs _ (by decide) (by decide)).trans h.base
  have hd : s₁.gpr .r6 = D := (f.regs _ (by decide) (by decide)).trans h.data
  have xp : NPre 4 s₁ sb .r6 (4 * tailSlot) 0 (bufferAddr B 0) (State.addr D) := by
    refine ⟨by rw [hb]; rfl, by rw [hd]; simp, ?_, ?_, by decide, by decide,
      by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
    · rw [hb]; have := h.fitB; change B.toNat + 256 + 16 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this]
    · rw [hd]; simpa using h.fitD
    · rw [f.wr]; exact workspace_part h.hw 256 16 (by decide)
    · rw [f.rd, f.wr]; exact Covers.right h.wd
    · exact h.sep.symm.sub_left (Offset.sub_base _ (by decide))
  refine WP.mono (xorN_wp xp) fun s₂ x => ?_
  have fx : Frame [⟨bufferAddr B 0, 16⟩] s₁.mem s₂.mem := by
    rw [x.mem]; exact Proof.Modes.over_frame _ _ _ _
  refine ⟨fun r h9 h10 => (x.regs r h9 h10).trans (f.regs r h9 h10),
    x.rd.trans f.rd, x.wr.trans f.wr, x.sp.trans f.sp, f.frame.trans fx, ?_⟩
  rw [x.mem, bytesAt_over_self _ _ _ (by decide), xor_bytes, f.block]
  have d : bytesAt s₁.mem (State.addr D) 16 = bytesAt s.mem (State.addr D) 16 := by
    apply bytes_frame f.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact h.sep.sub_right (Offset.sub_base _ (by decide))
  rw [d, xor_comm]

theorem copy_wp {s : State} {B D : BitVec 32} (h : CfbFill.Pre B D 1 s) :
    WP isa (.block SerialCbc.copyOutput) s (CopyPost s (State.addr D) (bufferAddr B 0)) := by
  apply copyBlock_wp
  refine ⟨by rw [h.data]; simp, by rw [h.base]; rfl, ?_, ?_, by decide, by decide,
    by decide, by decide, by decide, by decide, h.wd,
    Covers.right (workspace_part h.hw 256 16 (by decide)), ?_⟩
  · rw [h.data]; simpa using h.fitD
  · rw [h.base]; have := h.fitB; change B.toNat + 256 + 16 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this]
  · exact h.sep.sub_right (Offset.sub_base _ (by decide))

end VG.Proof.Sm4.Arm.SerialCbcFill

end

end

/-! # Encrypting the CBC input under the prepared round keys -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcCore

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchGroup
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

structure Post (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r6, .r7, .r8, .r11], s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨State.addr B, 4 * slots⟩] s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  block : bytesAt s'.mem (bufferAddr B 0) 16 =
    Spec.Sm4.cipher K (Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (bytesAt s.mem (counterAddr B) 16))

theorem core_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule}
    (h : CfbFill.Pre B D 1 s) (ht : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa SerialCbc.core s (Post s B D K) := by
  refine WP.seq (WP.mono (SerialCbcFill.fill_wp h) fun s₁ f => ?_)
  have hb : s₁.gpr sb = B := (f.regs _ (by decide) (by decide)).trans h.base
  have ht₁ := table_frame ht f.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
  have hw₁ : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f.wr]
    simpa only [BitVec.add_zero] using workspace_part h.hw 0 (4 * slots) (by decide)
  refine WP.mono (BatchCalls.crypt_wp hb (by
    have := h.fitB; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this])
    hw₁ ht₁) fun s₂ ⟨c, ht₂, ecb⟩ => ?_
  have ff : Frame [⟨State.addr B, 4 * slots⟩] s.mem s₁.mem := f.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  refine ⟨fun r hr => ?_, c.rd.trans f.rd, c.wr.trans f.wr, c.sp.trans f.sp,
    ff.trans c.frame, ht₂, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide)]
  · rw [encrypted_lane ecb (by decide), f.block]

end VG.Proof.Sm4.Arm.SerialCbcCore

end

end

/-! # One prepared-key CBC encryption block -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCbcGroup

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions table_frame difference_zero)
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
    Spec.Sm4.cipher K (Spec.Cbc.xor (bytesAt s.mem (State.addr D) 16) (bytesAt s.mem (counterAddr B) 16))
  block : bytesAt s'.mem (State.addr D) 16 = bytesAt s'.mem (counterAddr B) 16

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (ht : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa SerialCbc.group s (GroupPost s B D K n) := by
  refine WP.seq (WP.mono (SerialCbcFill.count_wp s) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans hB
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans hD
  have wd₁ : Covers [⟨State.addr D, 16⟩] s₁.wr := by
    rw [wr₁]
    exact (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by simp,
        by change 0 + 16 ≤ 16 * n; omega_using [hn]⟩).trans wd
  have sep₁ := sep.sub_left (Region.sub_prefix (show 16 ≤ 16 * n by omega_using [hn]))
  have p₁ : CfbFill.Pre B D 1 s₁ := ⟨b₁, d₁, g₁, fitB, by omega_using [hn, fitD],
    by rw [wr₁]; exact hw, wd₁, sep₁⟩
  refine WP.seq (WP.mono (SerialCbcCore.core_wp p₁ (by rw [m₁]; exact ht)) fun s₂ c => ?_)
  have p₂ : CfbFill.Pre B D 1 s₂ := ⟨(c.regs _ (by simp [sb])).trans b₁,
    (c.regs _ (by simp)).trans d₁, (c.regs _ (by simp)).trans g₁, fitB, by omega_using [hn, fitD],
    by rw [c.wr, wr₁]; exact hw, by rw [c.wr]; exact wd₁, sep₁⟩
  refine WP.seq (WP.mono (SerialCbcFill.copy_wp p₂) fun s₃ cp => ?_)
  have b₃ : s₃.gpr sb = B := (cp.regs _ (by decide) (by decide)).trans p₂.base
  refine WP.seq (WP.mono (SerialOfbGroup.save_wp b₃ fitB (by rw [cp.wr, c.wr, wr₁]; exact hw))
    fun s₄ sv => ?_)
  have buf₃ : bytesAt s₃.mem (bufferAddr B 0) 16 = bytesAt s₂.mem (bufferAddr B 0) 16 := by
    apply bytes_frame cp.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.symm.sub_left (Offset.sub_base _ (by decide))
  have data₄ : bytesAt s₄.mem (State.addr D) 16 = bytesAt s₃.mem (State.addr D) 16 := by
    apply bytes_frame sv.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.sub_right (Offset.sub_base _ (by decide))
  have f₂ : Frame (batchRegions B D 1) s₁.mem s₂.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]
  have f₃ : Frame (batchRegions B D 1) s₂.mem s₃.mem := cp.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]
  have f₄ : Frame (batchRegions B D 1) s₃.mem s₄.mem := sv.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]
  have table₃ := table_frame c.table cp.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sep₁.symm.sub_left (Offset.sub_base _ (by decide)))
  have table₄ := table_frame table₃ sv.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  have n₄ : s₄.gpr .r7 = BitVec.ofNat 32 n := by
    rw [sv.regs _ (by decide) (by decide), cp.regs _ (by decide) (by decide),
      c.regs _ (by simp), o₁ _ (by decide) (by decide), hN]
  have g₄ : s₄.gpr .r11 = 1 := by
    rw [sv.regs _ (by decide) (by decide), cp.regs _ (by decide) (by decide), c.regs _ (by simp), g₁]
  have d₄ : s₄.gpr .r6 = D := by
    rw [sv.regs _ (by decide) (by decide), cp.regs _ (by decide) (by decide)]; exact p₂.data
  obtain ⟨s₅, e₅, d₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := addImm_ok s₄ .r6 .r6 16 (by decide)
  apply (WP.block_append_iff (M := isa) (l₁ := [.dp .add .r6 .r6 (.imm 16)])
    (l₂ := [.subs .r7 .r7 (.reg .r11)])).mpr
  refine WP.of_runBlock ⟨s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, n₆, z₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := subsR_ok s₅ .r7 .r7 .r11
  refine WP.of_runBlock ⟨s₆, e₆, fun r hr => ?_, ?_, ?_, ?_,
    rd₆.trans (rd₅.trans (sv.rd.trans (cp.rd.trans (c.rd.trans rd₁)))),
    wr₆.trans (wr₅.trans (sv.wr.trans (cp.wr.trans (c.wr.trans wr₁)))),
    sp₆.trans (sp₅.trans (sv.sp.trans (cp.sp.trans (c.sp.trans sp₁)))), ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [o₆ _ (by decide), o₅ _ (by decide), sv.regs _ (by decide) (by decide),
        cp.regs _ (by decide) (by decide), c.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [o₆ _ (by decide), d₅, d₄]
  · rw [n₆, o₅ _ (by decide), o₅ _ (by decide), n₄, g₄]; exact Offset.ofNat_sub_ofNat hn
  · rw [z₆, o₅ _ (by decide), o₅ _ (by decide), n₄, g₄]; exact difference_zero hn32 hn
  · rw [m₆, m₅, ← m₁]; exact (f₂.trans f₃).trans f₄
  · rw [m₆, m₅]; exact table₄
  · rw [m₆, m₅, sv.block, buf₃, c.block, m₁]
  · rw [m₆, m₅, data₄, cp.block, sv.block, buf₃]

end VG.Proof.Sm4.Arm.SerialCbcGroup

end

end

/-! # The arbitrary-length prepared-key SM4-CBC encryption loop on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.SerialCbcLoop

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.SerialCbcGroup
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
  · exact (sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right
      (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using []))
  · exact (sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right
      (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
  · exact Offset.disjoint_base _ (by omega_using [hi]) (by omega_using [hn, hj])

def chain (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (i : Nat) : List Byte :=
  Proof.Modes.cbcEncPrev 16 (Spec.Sm4.cipher K) m (State.addr D) t i

def outBlock (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (j : Nat) : List Byte :=
  Proof.Modes.cbcEncC 16 (Spec.Sm4.cipher K) m (State.addr D) t j

theorem chain_succ (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (i : Nat) :
    chain m D K t (i + 1) = outBlock m D K t i := by
  simp only [chain, Proof.Modes.cbcEncPrev, show i + 1 ≠ 0 by omega_using [], ↓reduceIte, Nat.add_sub_cancel]
  rfl

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
    WP isa SerialCbc.group s fun s' =>
      LoopInv s₀ B D K t n (i + 1) s' ∧ s'.z = decide (i + 1 = n) := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  let g : Nat := 1
  have hg : 1 ≤ g := by dsimp only [g]; omega_using []
  have hgn : g ≤ n - i := by dsimp only [g]; omega_using [hi]
  have hgi : i + g ≤ n := by omega_using [hi]
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
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr,
      by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_using [hi]⟩
  have sb' : s.gpr sb = B := (h.regs _ (by simp [sb])).trans hB
  refine WP.mono (group_wp (by omega_using [hi]) (by omega_using [hn32]) sb' h.data h.left fitB
    (by rw [diNat]; omega_using [hi, fitD]) (by rw [h.wr]; exact hw) wdi (sep.sub_left subD) h.table)
    fun s' hs => ?_
  have fNew : Frame (batchRegions B D (i + g)) s.mem s'.mem := hs.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · refine ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], ?_⟩
      rw [diAddr]; exact Offset.sub_base _ (by omega_using [])
  have fOld : Frame (batchRegions B D (i + g)) s₀.mem s.mem := h.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · exact ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], Region.sub_prefix (by omega_using [])⟩
  refine ⟨⟨fun r hr => (hs.regs r hr).trans (h.regs r hr), ?_, ?_, hgi,
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, fOld.trans fNew, hs.table, ?_, ?_⟩, ?_⟩
  · rw [hs.data]
    change D + BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 (16 * g) = _
    rw [Offset.add_add]; congr 2
  · rw [hs.left, show n - i - 1 = n - (i + 1) by omega_using []]
  · rw [hs.counter]
    have ha : State.addr Di = dataAddr D i := diAddr
    rw [ha, future_data hn32 (by omega_using []) (by omega_using [hi]) sep h.frame, h.counter, chain_succ]
    exact (Proof.Modes.cbcEncC_eq 16 (Spec.Sm4.cipher K) s₀.mem (State.addr D) t i).symm
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
        exact Offset.disjoint _ (.inl (by omega_using [hjOld])) (by omega_using [diNat, hj]) (by omega_using [diNat])
    · have he : j = i := by dsimp only [g] at *; omega_using [hj, hjOld]
      subst j
      have ha : State.addr Di = dataAddr D i := diAddr
      rw [← ha, hs.block, hs.counter, ha,
        future_data hn32 (by omega_using []) (by omega_using [hi]) sep h.frame, h.counter]
      exact (Proof.Modes.cbcEncC_eq 16 (Spec.Sm4.cipher K) s₀.mem (State.addr D) t i).symm
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega_using []

theorem loop_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.loop SerialCbc.group .ne) s₀ (LoopInv s₀ B D K t n n) := by
  have hi : LoopInv s₀ B D K t n 0 s₀ :=
    ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
      by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _, hH,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B D K t n i s)
    (fun m s hs => ?_) n s₀ ⟨0, by omega_using [], by omega_using [hn], hi⟩
  obtain ⟨i, rfl, hi, hs⟩ := hs
  refine WP.mono (loopInv_step hn32 hi hB fitB fitD hw wd sep hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : i + 1 = n
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      n - (i + 1), by omega_using [hi],
      i + 1, rfl, by have := h'.bound; omega_using [hi, he], h'⟩

theorem loopOrEmpty_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n) (hZ : s₀.z = decide (n = 0))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.ite .eq (.block []) (.loop SerialCbc.group .ne)) s₀ (LoopInv s₀ B D K t n n) := by
  refine WP.ite (decide (n = 0)) (by change some s₀.z = some (decide (n = 0)); rw [hZ]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = 0 := of_decide_eq_true hz
    subst hn
    exact WP.block_nil
      ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
        by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _, hH,
        by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  · have hn : 1 ≤ n := by simp at hz; omega_using [hz]
    exact loop_wp hn hn32 hB hD hN fitB fitD hw wd sep hH hC

theorem loop_output {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (h : LoopInv s₀ B D K t n n s) :
    Spec.Cbc.blocksAt s.mem (State.addr D) n =
      Spec.Cbc.encrypt (Spec.Sm4.cipher K) t (Spec.Cbc.blocksAt s₀.mem (State.addr D) n) := by
  rw [← Proof.Modes.blocksOf_16, Proof.Modes.encrypt_eq]
  unfold Proof.Modes.blocksOf
  apply List.map_congr_left
  intro j hj
  exact h.blocks j (List.mem_range.mp hj)

theorem chain_next (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (n : Nat) :
    chain m D K t n = Spec.Cbc.next t
      (Spec.Cbc.encrypt (Spec.Sm4.cipher K) t (Spec.Cbc.blocksAt m (State.addr D) n)) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [chain_succ, Spec.Cbc.next, ← Proof.Modes.blocksOf_16, Proof.Modes.encrypt_eq,
      Proof.Modes.getLastD_map_range]
    rfl

end VG.Proof.Sm4.Arm.SerialCbcLoop
