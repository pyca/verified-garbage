module

public import VerifiedGarbage.Proof.Modes.Arm.Words
public import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # Moving the running counter into and out of SM4-CTR's working space -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchChain

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Impl.Modes.Arm (copyWord)
open VG.Proof.Modes.Arm VG.Proof.Sm4.Arm.BatchFill
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)
open VG.Proof.Sm4.Arm.BatchGroup

structure CopyPost (s : State) (P Q : Addr) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨P, 16⟩] s.mem s'.mem
  block : bytesAt s'.mem P 16 = bytesAt s.mem Q 16

theorem copyBlock_wp {s : State} {rd rs : Reg} {od os : Nat} {P Q : Addr}
    (h : NPre 4 s rd rs od os P Q) :
    WP isa (.block ((List.range 4).flatMap (copyWord rd rs od os))) s (CopyPost s P Q) := by
  refine WP.mono (copyN_wp h) fun s' hc => ⟨hc.regs, hc.rd, hc.wr, hc.sp, ?_, ?_⟩
  · rw [hc.mem]; exact Proof.Modes.over_frame _ _ _ _
  · rw [hc.mem, bytesAt_over_self _ _ _ (by decide)]; rfl

structure ChainPre (s : State) (B I : BitVec 32) : Prop where
  base : s.gpr sb = B
  iv : s.gpr .r5 = I
  fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  fitI : I.toNat + 16 ≤ 2 ^ 32
  hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  hi : Covers [⟨State.addr I, 16⟩] s.wr
  sep : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

theorem ChainPre.counterSub {s : State} {B I : BitVec 32} (_h : ChainPre s B I) :
    Region.Sub ⟨counterAddr B, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩ := Offset.sub_base _ (by decide)

theorem counterIn_wp {s : State} {B I : BitVec 32} (h : ChainPre s B I) :
    WP isa (.block BatchCtr.copyCounterIn) s (CopyPost s (counterAddr B) (State.addr I)) := by
  have wc := workspace_part h.hw (4 * BatchCtr.counterSlot) 16 (by decide)
  apply copyBlock_wp
  exact ⟨by rw [h.base], by rw [h.iv, BitVec.add_zero],
    by rw [h.base]; have := h.fitB; rw [total_eq, counter_eq] at *; omega,
    by rw [h.iv]; have := h.fitI; omega,
    by decide, by decide, by decide, by decide, by decide, by decide,
    wc, Covers.right h.hi, h.sep.symm.sub_left h.counterSub⟩

theorem counterOut_wp {s : State} {B I : BitVec 32} (h : ChainPre s B I) :
    WP isa (.block BatchCtr.copyCounterOut) s (CopyPost s (State.addr I) (counterAddr B)) := by
  have wc := workspace_part h.hw (4 * BatchCtr.counterSlot) 16 (by decide)
  apply copyBlock_wp
  exact ⟨by rw [h.iv, BitVec.add_zero], by rw [h.base],
    by rw [h.iv]; have := h.fitI; omega,
    by rw [h.base]; have := h.fitB; rw [total_eq, counter_eq] at *; omega,
    by decide, by decide, by decide, by decide, by decide, by decide,
    h.hi, Covers.right wc, h.sep.sub_right h.counterSub⟩

structure SetupPost (s : State) (B I : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨counterAddr B, 16⟩] s.mem s'.mem
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (State.addr I) 16
  table : Holds layout s'.mem (State.addr B) K .encrypt
  z : s'.z = decide (n = 0)

theorem setup_wp {s : State} {B I : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (h : ChainPre s B I) (hn : n < 2 ^ 32) (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa (.block (BatchCtr.copyCounterIn ++ ([.cmp .r7 (.imm 0)] : List Instr))) s (SetupPost s B I K n) := by
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterIn) (l₂ := [.cmp .r7 (.imm 0)])).mpr
  refine WP.mono (counterIn_wp h) fun s₁ c₁ => ?_
  have table₁ : Holds layout s₁.mem (State.addr B) K .encrypt := table_frame hH c₁.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine Proof.MdStream.Arm.wp_cmp (Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ hz => ?_
  refine WP.block_nil ⟨fun r h9 h10 => by rw [u₂.gpr, c₁.regs r h9 h10], u₂.rd.trans c₁.rd,
    u₂.wr.trans c₁.wr, u₂.sp.trans c₁.sp,
    by rw [u₂.mem]; exact c₁.frame, by rw [u₂.mem]; exact c₁.block,
    by rw [u₂.mem]; exact table₁, ?_⟩
  rw [hz, c₁.regs _ (by decide) (by decide), hN]
  exact difference_zero hn (Nat.zero_le n)

end VG.Proof.Sm4.Arm.BatchChain
