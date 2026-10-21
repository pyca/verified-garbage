module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Impl.Modes.Arm.Seq
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.Ctr
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Modes.Arm.Counter
import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! # Filling SM4's counter batches on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchFill

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Impl.Modes.Arm (copyWord incAt)
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

abbrev counterAddr (B : BitVec 32) : Addr := State.addr B + BitVec.ofNat 64 (4 * BatchCtr.counterSlot)
abbrev bufferAddr (B : BitVec 32) (j : Nat) : Addr := State.addr B + BitVec.ofNat 64 (4 * tailSlot + 16 * j)

theorem total_eq : BatchCtr.totalSlots = 378 := rfl
theorem counter_eq : BatchCtr.counterSlot = 373 := rfl

theorem offset_nat (B : BitVec 32) (o : Nat) (h : B.toNat + o < 2 ^ 32) :
    (B + BitVec.ofNat 32 o).toNat = B.toNat + o := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

theorem workspace_part {rs : List Region} {B : BitVec 32}
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] rs) (o n : Nat)
    (h : o + n ≤ 4 * BatchCtr.totalSlots) : Covers [⟨State.addr B + BitVec.ofNat 64 o, n⟩] rs :=
  (Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _, o, rfl, h⟩).trans hw

/-- Copy the running counter into lane `j`, then increment it. -/
def copyIncCode : List Instr :=
  (List.range 4).flatMap (copyWord .r0 sb 0 (4 * BatchCtr.counterSlot)) ++ incAt sb (4 * BatchCtr.counterSlot)

structure CopyIncPost (s : State) (B : BitVec 32) (j : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B j, 16⟩, ⟨counterAddr B, 16⟩] s.mem s'.mem
  lane : bytesAt s'.mem (bufferAddr B j) 16 = bytesAt s.mem (counterAddr B) 16
  counter : bytesAt s'.mem (counterAddr B) 16 = Spec.Ctr.inc (bytesAt s.mem (counterAddr B) 16)

theorem copyInc_wp {s : State} {B : BitVec 32} {j : Nat} (hj : j < 8)
    (hB : s.gpr sb = B) (hp : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr) :
    WP isa (.block copyIncCode) s (CopyIncPost s B j) := by
  have htail : 4 * tailSlot + 16 * j + 16 ≤ 4 * BatchCtr.totalSlots := by
    rw [tailSlot, total_eq]; omega
  have hctr : 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots := by decide
  have wt := workspace_part hw (4 * tailSlot + 16 * j) 16 htail
  have wc := workspace_part hw (4 * BatchCtr.counterSlot) 16 hctr
  have sep : Region.Disjoint ⟨bufferAddr B j, 16⟩ ⟨counterAddr B, 16⟩ := by
    apply Offset.disjoint (State.addr B)
    · left
      change 4 * tailSlot + 16 * j + 16 ≤ 4 * BatchCtr.counterSlot
      rw [tailSlot, counter_eq]; omega
    · change 4 * tailSlot + 16 * j + 16 ≤ 2 ^ 64
      rw [tailSlot]; omega
    · decide
  have np : NPre 4 s .r0 sb 0 (4 * BatchCtr.counterSlot) (bufferAddr B j) (counterAddr B) :=
    ⟨by rw [BitVec.add_zero, hp, addr_add (by omega)], by rw [hB],
      by rw [hp, offset_nat B _ (by omega)]; omega,
      by rw [hB]; omega, by decide, by decide, by decide, by decide, by decide, by decide,
      wt, Covers.right wc, sep⟩
  obtain ⟨t₁, s₁, he₁, h₁⟩ := copyN_wp np
  have b₁ : s₁.gpr sb = B := (h₁.regs _ (by decide) (by decide)).trans hB
  obtain ⟨s₂, e₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := Counter.incr_ok s₁ (base := sb) (off := 4 * BatchCtr.counterSlot)
    (by decide) (by decide) (by decide)
    (fun d hd => by
      rw [b₁, addr_add (by omega), Offset.add_add])
    (fun d n hn => by
      rw [h₁.rd, h₁.wr]
      exact Covers.right wc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun d n hn => by
      rw [h₁.wr]
      exact wc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
  have fc : Frame [⟨bufferAddr B j, 16⟩] s.mem s₁.mem := by
    rw [h₁.mem]; exact Proof.Modes.over_frame _ _ _ _
  have fi : Frame [⟨counterAddr B, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Counter.incMem_frame _ _
  have sameCounter : bytesAt s₁.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    rw [h₁.mem]
    exact bytesAt_over_other _ _ sep (by decide)
  have sameLane : bytesAt s₂.mem (bufferAddr B j) 16 = bytesAt s₁.mem (bufferAddr B j) 16 := by
    apply List.map_congr_left
    intro i hi
    exact fi.bytes (R := ⟨bufferAddr B j, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sep) (by change 16 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have copied : bytesAt s₁.mem (bufferAddr B j) 16 = bytesAt s.mem (counterAddr B) 16 := by
    rw [h₁.mem, bytesAt_over_self _ _ _ (by decide)]
    rfl
  refine WP.block_append_iff.mpr ⟨t₁, s₁, he₁, WP.of_runBlock ⟨s₂, e₂, ?_⟩⟩
  refine ⟨fun r h9 h10 => (g₂ r h9 h10).trans (h₁.regs r h9 h10), rd₂.trans h₁.rd,
    wr₂.trans h₁.wr, sp₂.trans h₁.sp,
    (fc.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans (fi.mono fun r hr => List.mem_cons_of_mem _ hr),
    sameLane.trans copied, ?_⟩
  rw [m₂, Counter.incMem_bytes, sameCounter]

structure FillStepPost (s : State) (B : BitVec 32) (j n : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r
  ptr : s'.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * (j + 1))
  left : s'.gpr .r1 = BitVec.ofNat 32 (n - 1)
  z : s'.z = decide (n = 1)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B j, 16⟩, ⟨counterAddr B, 16⟩] s.mem s'.mem
  lane : bytesAt s'.mem (bufferAddr B j) 16 = bytesAt s.mem (counterAddr B) 16
  counter : bytesAt s'.mem (counterAddr B) 16 = Spec.Ctr.inc (bytesAt s.mem (counterAddr B) 16)

theorem fillBody_eq : BatchCtr.fillBody = copyIncCode ++
    ([.dp .add .r0 .r0 (.imm 16), .subs .r1 .r1 (.imm 1)] : List Instr) := by
  simp only [BatchCtr.fillBody, copyIncCode, List.append_assoc]

theorem fillStep_wp {s : State} {B : BitVec 32} {j n : Nat} (hj : j < 8) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hB : s.gpr sb = B) (hp : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j))
    (hN : s.gpr .r1 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr) :
    WP isa (.block BatchCtr.fillBody) s (FillStepPost s B j n) := by
  rw [fillBody_eq]
  apply WP.block_append_iff.mpr
  refine WP.mono (copyInc_wp hj hB hp fitB hw) fun s₁ h₁ => ?_
  refine Proof.MdStream.Arm.wp_add (Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ => ?_
  refine Proof.MdStream.Arm.wp_subs (Proof.MdStream.Arm.op2_imm (by decide)) fun s₃ u₃ hz => ?_
  refine WP.block_nil ⟨fun r h9 h10 h0 h1 => by
      rw [u₃.other r h1, u₂.other r h0, h₁.regs r h9 h10], ?_, ?_, ?_,
    by rw [u₃.rd, u₂.rd, h₁.rd], by rw [u₃.wr, u₂.wr, h₁.wr], by rw [u₃.sp, u₂.sp, h₁.sp],
    by rw [u₃.mem, u₂.mem]; exact h₁.frame,
    by rw [u₃.mem, u₂.mem]; exact h₁.lane,
    by rw [u₃.mem, u₂.mem]; exact h₁.counter⟩
  · rw [u₃.other _ (by decide), u₂.gpr, h₁.regs _ (by decide) (by decide), hp,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_add]
    congr 2
  · rw [u₃.gpr, u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), hN]
    exact Offset.ofNat_sub_ofNat hn
  · rw [hz, u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), hN,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat hn]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have hnat := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
      have : (0 : BitVec 32).toNat = 0 := rfl
      rw [this] at hnat
      omega
    · intro h; subst h; rfl

/-- Reading a block outside a frame preserves all of its bytes. -/
theorem bytes_frame {m m' : Mem} {rs : List Region} {P : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P, 16⟩ r) : bytesAt m' P 16 = bytesAt m P 16 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes hd (by change 16 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem buffer_counter_sep (B : BitVec 32) {j : Nat} (hj : j < 8) :
    Region.Disjoint ⟨bufferAddr B j, 16⟩ ⟨counterAddr B, 16⟩ := by
  apply Offset.disjoint (State.addr B)
  · left; change 4 * tailSlot + 16 * j + 16 ≤ 4 * BatchCtr.counterSlot
    rw [tailSlot, counter_eq]; omega
  · change 4 * tailSlot + 16 * j + 16 ≤ 2 ^ 64
    rw [tailSlot]; omega
  · decide

theorem buffer_sub (B : BitVec 32) {j n : Nat} (hj : j < n) (_hn : n ≤ 8) :
    Region.Sub ⟨bufferAddr B j, 16⟩ ⟨bufferAddr B 0, 16 * n⟩ := by
  have he : bufferAddr B j = bufferAddr B 0 + BitVec.ofNat 64 (16 * j) := by
    simp only [bufferAddr, Nat.mul_zero, Nat.add_zero, Offset.add_add]
  rw [he]
  exact Offset.sub_base _ (by omega)

structure FillInv (s₀ : State) (B : BitVec 32) (g : Nat) (t : List Byte) (j : Nat) (s : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → s.gpr r = s₀.gpr r
  ptr : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j)
  left : s.gpr .r1 = BitVec.ofNat 32 (g - j)
  bound : j ≤ g
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨bufferAddr B 0, 16 * j⟩, ⟨counterAddr B, 16⟩] s₀.mem s.mem
  counter : bytesAt s.mem (counterAddr B) 16 = Spec.Ctr.next t j
  lanes : ∀ k < j, bytesAt s.mem (bufferAddr B k) 16 = Spec.Ctr.next t k

theorem fillInv_step {s₀ s : State} {B : BitVec 32} {g j : Nat} {t : List Byte}
    (hg : g ≤ 8) (hj : j < g) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (h : FillInv s₀ B g t j s) :
    WP isa (.block BatchCtr.fillBody) s fun s' => FillInv s₀ B g t (j + 1) s' ∧ s'.z = decide (j + 1 = g) := by
  have base : s.gpr sb = B := (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans hB
  refine WP.mono (fillStep_wp (by omega) (by omega) (by omega) base h.ptr h.left fitB
    (by rw [h.wr]; exact hw)) fun s' hs => ?_
  refine ⟨⟨fun r h9 h10 h0 h1 => (hs.regs r h9 h10 h0 h1).trans (h.regs r h9 h10 h0 h1), hs.ptr,
    by rw [hs.left, show g - j - 1 = g - (j + 1) by omega], by omega,
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, ?_, ?_, ?_⟩, ?_⟩
  · have old : Frame [⟨bufferAddr B 0, 16 * (j + 1)⟩, ⟨counterAddr B, 16⟩] s₀.mem s.mem :=
      h.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
        · exact ⟨_, by simp, fun _ hi => hi⟩
    exact old.trans (hs.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, buffer_sub B (by omega) (by omega)⟩
      · exact ⟨_, by simp, fun _ hi => hi⟩)
  · rw [hs.counter, h.counter, Proof.AesCtr.next_succ]
  · intro k hk
    by_cases he : k = j
    · subst he; exact hs.lane.trans h.counter
    · have hk' : k < j := by omega
      rw [bytes_frame hs.frame (fun r hr => ?_), h.lanes k hk']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · apply Offset.disjoint (State.addr B)
        · left; change 4 * tailSlot + 16 * k + 16 ≤ 4 * tailSlot + 16 * j; omega
        · change 4 * tailSlot + 16 * k + 16 ≤ 2 ^ 64; rw [tailSlot]; omega
        · change 4 * tailSlot + 16 * j + 16 ≤ 2 ^ 64; rw [tailSlot]; omega
      · exact buffer_counter_sep B (by omega)
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega

theorem fill_eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl

theorem fillLoop_wp {s₀ : State} {B : BitVec 32} {g : Nat} {t : List Byte}
    (hg : 1 ≤ g) (hg8 : g ≤ 8) (hB : s₀.gpr sb = B)
    (hp : s₀.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot))
    (hN : s₀.gpr .r1 = BitVec.ofNat 32 g) (hC : bytesAt s₀.mem (counterAddr B) 16 = t)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr) :
    WP isa (.loop (.block BatchCtr.fillBody) .ne) s₀ (FillInv s₀ B g t g) := by
  have hi : FillInv s₀ B g t 0 s₀ :=
    ⟨fun _ _ _ _ _ => rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using hp,
      by simpa only [Nat.sub_zero] using hN, by omega, rfl, rfl, rfl, Frame.refl _ _,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC,
      fun _ h => by omega⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ j, m = g - j ∧ j < g ∧ FillInv s₀ B g t j s)
    (fun m s hs => ?_) g s₀ ⟨0, by omega, by omega, hi⟩
  obtain ⟨j, rfl, hj, hs⟩ := hs
  refine WP.mono (fillInv_step hg8 hj hB fitB hw hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : j + 1 = g
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      g - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

def fillArgs (s : State) : State :=
  (s.setReg .r0 (s.gpr sb + BitVec.ofNat 32 (4 * tailSlot))).setReg .r1 (s.gpr .r11)

theorem fillArgs_run (s : State) :
    runBlock isa [tailAddr .r0, VG.Impl.Aes.Arm.movR .r1 .r11] s = some (fillArgs s) := by rfl

structure FillPost (s : State) (B : BitVec 32) (g : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B 0, 16 * g⟩, ⟨counterAddr B, 16⟩] s.mem s'.mem
  counter : bytesAt s'.mem (counterAddr B) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) g
  lanes : ∀ k < g, bytesAt s'.mem (bufferAddr B k) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) k

theorem fill_wp {s : State} {B : BitVec 32} {g : Nat} (hg : 1 ≤ g) (hg8 : g ≤ 8)
    (hB : s.gpr sb = B) (hN : s.gpr .r11 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr) :
    WP isa BatchCtr.fill s (FillPost s B g) := by
  have hb : (fillArgs s).gpr sb = B := by simpa [fillArgs, State.setReg, sb] using hB
  have hp : (fillArgs s).gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot) := by
    simp only [fillArgs, RegUpd.gpr_setReg]; simp only [reduceCtorEq, ↓reduceIte]; rw [hB]
  have hn : (fillArgs s).gpr .r1 = BitVec.ofNat 32 g := by rw [fillArgs, RegUpd.gpr_setReg_self, hN]
  refine WP.seq (WP.of_runBlock ⟨fillArgs s, fillArgs_run s, ?_⟩)
  refine WP.mono (fillLoop_wp hg hg8 hb hp hn rfl fitB hw) fun s' h => ?_
  refine ⟨fun r h9 h10 h0 h1 => ?_, h.rd, h.wr, h.sp, h.frame, h.counter, h.lanes⟩
  rw [h.regs r h9 h10 h0 h1]
  simp only [fillArgs, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h0]

end VG.Proof.Sm4.Arm.BatchFill
