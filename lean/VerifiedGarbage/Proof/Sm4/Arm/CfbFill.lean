module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb
public import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
public import VerifiedGarbage.Proof.Sm4.Arm.BatchXor
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! # Filling the independent input lanes of CFB decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CfbFill

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Impl.Modes.Arm (copyWord)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

structure Pre (B D : BitVec 32) (g : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  data : s.gpr .r6 = D
  group : s.gpr .r11 = BitVec.ofNat 32 g
  fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  fitD : D.toNat + 16 * g ≤ 2 ^ 32
  hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  wd : Covers [⟨State.addr D, 16 * g⟩] s.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

theorem data_copy_wp {s : State} {B D : BitVec 32} {g j o : Nat} (h : Pre B D g s)
    (hg : g ≤ 8) (hj : j < g) (ho : o + 16 ≤ 4 * BatchCtr.totalSlots) :
    WP isa (.block ((List.range 4).flatMap (copyWord sb .r6 o (16 * j)))) s
      (CopyPost s (State.addr B + BitVec.ofNat 64 o) (dataAddr D j)) := by
  have wd : Covers [⟨dataAddr D j, 16⟩] s.wr :=
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * g⟩, List.mem_singleton_self _, 16 * j, rfl, by change 16 * j + 16 ≤ 16 * g; omega⟩).trans h.wd
  apply copyBlock_wp
  exact ⟨by rw [h.base], by rw [h.data], by rw [h.base]; have := h.fitB; omega,
    by rw [h.data]; have := h.fitD; omega,
    by change o + 16 ≤ 4096; rw [total_eq] at ho; omega, by change 16 * j + 16 ≤ 4096; omega,
    by decide, by decide, by decide, by decide,
    workspace_part h.hw o 16 ho, Covers.right wd,
    (h.sep.symm.sub_left (Offset.sub_base _ ho)).sub_right (Offset.sub_base _ (by omega))⟩

theorem first_wp {s : State} {B D : BitVec 32} {g : Nat} (h : Pre B D g s) :
    WP isa (.block BatchCfb.first) s (CopyPost s (bufferAddr B 0) (counterAddr B)) := by
  apply copyBlock_wp
  exact ⟨by rw [h.base]; simp only [bufferAddr, Nat.mul_zero, Nat.add_zero], by rw [h.base],
    by rw [h.base]; have := h.fitB; change B.toNat + 1512 ≤ 2 ^ 32 at this; change B.toNat + 256 + 16 ≤ 2 ^ 32; omega,
    by rw [h.base]; have := h.fitB; change B.toNat + 1512 ≤ 2 ^ 32 at this; change B.toNat + 1492 + 16 ≤ 2 ^ 32; omega,
    by decide, by decide, by decide, by decide, by decide, by decide,
    workspace_part h.hw 256 16 (by decide), Covers.right (workspace_part h.hw 1492 16 (by decide)),
    buffer_counter_sep B (by decide)⟩

theorem compare_run (s : State) (j : Nat) (hj : j < 8) :
    runBlock isa [.cmp .r11 (.imm (BitVec.ofNat 32 (j + 1)))] s =
      some (subFlags s (s.gpr .r11) (BitVec.ofNat 32 (j + 1))) := by
  have enc : encodable (BitVec.ofNat 32 (j + 1)) = true := by
    have all : ∀ j < 8, encodable (BitVec.ofNat 32 (j + 1)) = true := by decide
    exact all j hj
  simp only [runBlock_cons, exec, Op2.eval, enc, ite_true, Option.map_some, runStep_some, runBlock_nil]

theorem compare_eq {s : State} {g j : Nat} (hg : g ≤ 8) (hj : j < 8)
    (hn : s.gpr .r11 = BitVec.ofNat 32 g) :
    isa.eval .eq (subFlags s (s.gpr .r11) (BitVec.ofNat 32 (j + 1))) = some (decide (j + 1 = g)) := by
  change some ((s.gpr .r11 - BitVec.ofNat 32 (j + 1)) == 0) = _
  apply congrArg some
  rw [hn]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_iff]
  have gn : (BitVec.ofNat 32 g).toNat = g := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have jn : (BitVec.ofNat 32 (j + 1)).toNat = j + 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro he
    have eq : BitVec.ofNat 32 g = BitVec.ofNat 32 (j + 1) := by bv_omega
    have e := congrArg BitVec.toNat eq
    rw [gn, jn] at e
    omega
  · intro he
    rw [he, BitVec.sub_self]
    rfl

def regions (B : BitVec 32) : List Region := [⟨bufferAddr B 0, 128⟩, ⟨counterAddr B, 16⟩]

structure Inv (s₀ : State) (B D : BitVec 32) (j : Nat) (s : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (regions B) s₀.mem s.mem
  first : bytesAt s.mem (bufferAddr B 0) 16 = bytesAt s₀.mem (counterAddr B) 16
  lanes : ∀ k < j, bytesAt s.mem (bufferAddr B (k + 1)) 16 = bytesAt s₀.mem (dataAddr D k) 16

structure Post (s₀ : State) (B D : BitVec 32) (g : Nat) (s : State) : Prop extends Inv s₀ B D (g - 1) s where
  counter : bytesAt s.mem (counterAddr B) 16 = bytesAt s₀.mem (dataAddr D (g - 1)) 16

theorem Inv.pre {s₀ s : State} {B D : BitVec 32} {g j : Nat} (h : Pre B D g s₀) (i : Inv s₀ B D j s) : Pre B D g s :=
  ⟨(i.regs _ (by decide) (by decide)).trans h.base, (i.regs _ (by decide) (by decide)).trans h.data,
    (i.regs _ (by decide) (by decide)).trans h.group, h.fitB, h.fitD,
    by rw [i.wr]; exact h.hw, by rw [i.wr]; exact h.wd, h.sep⟩

theorem lane_frame {B : BitVec 32} {k : Nat} (hk : k < 8) :
    Region.Sub ⟨bufferAddr B k, 16⟩ ⟨bufferAddr B 0, 128⟩ := buffer_sub B (n := 8) hk (by decide)

theorem counter_frame {B : BitVec 32} :
    Region.Sub ⟨counterAddr B, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩ := Offset.sub_base _ (by decide)

theorem Inv.data_kept {s₀ s : State} {B D : BitVec 32} {g j k : Nat}
    (h : Pre B D g s₀) (i : Inv s₀ B D j s) (hk : k < g) :
    bytesAt s.mem (dataAddr D k) 16 = bytesAt s₀.mem (dataAddr D k) 16 := by
  apply bytes_frame i.frame
  intro r hr
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
  · exact (h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right counter_frame

theorem Inv.cmp {s₀ s : State} {B D : BitVec 32} {j : Nat} (h : Inv s₀ B D j s) (a b : BitVec 32) :
    Inv s₀ B D j (subFlags s a b) := ⟨h.regs, h.rd, h.wr, h.sp, h.frame, h.first, h.lanes⟩

theorem Inv.next {s₀ s s' : State} {B D : BitVec 32} {g j : Nat}
    (h : Pre B D g s₀) (hg : g ≤ 8) (hj : j + 1 < g) (i : Inv s₀ B D j s)
    (c : CopyPost s (bufferAddr B (j + 1)) (dataAddr D j) s') : Inv s₀ B D (j + 1) s' := by
  have cf : Frame (regions B) s.mem s'.mem := c.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨bufferAddr B 0, 128⟩, List.mem_cons_self, lane_frame (by omega)⟩
  refine ⟨fun r h9 h10 => (c.regs r h9 h10).trans (i.regs r h9 h10), c.rd.trans i.rd,
    c.wr.trans i.wr, c.sp.trans i.sp, i.frame.trans cf, ?_, ?_⟩
  · rw [bytes_frame (P := bufferAddr B 0) c.frame (fun r hr => ?_)]
    exact i.first
    simp only [List.mem_singleton] at hr; subst hr
    apply Offset.disjoint (State.addr B)
    · left; change 4 * tailSlot + 16 * 0 + 16 ≤ 4 * tailSlot + 16 * (j + 1); omega
    · change 4 * tailSlot + 16 * 0 + 16 ≤ 2 ^ 64; rw [tailSlot]; omega
    · change 4 * tailSlot + 16 * (j + 1) + 16 ≤ 2 ^ 64; rw [tailSlot]; omega
  · intro k hk
    by_cases he : k = j
    · subst k
      rw [c.block, i.data_kept h (by omega)]
    · rw [bytes_frame (P := bufferAddr B (k + 1)) c.frame (fun r hr => ?_)]
      exact i.lanes k (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      apply Offset.disjoint (State.addr B)
      · left; change 4 * tailSlot + 16 * (k + 1) + 16 ≤ 4 * tailSlot + 16 * (j + 1); omega
      · change 4 * tailSlot + 16 * (k + 1) + 16 ≤ 2 ^ 64; rw [tailSlot]; omega
      · change 4 * tailSlot + 16 * (j + 1) + 16 ≤ 2 ^ 64; rw [tailSlot]; omega

theorem Inv.last {s₀ s s' : State} {B D : BitVec 32} {g j : Nat}
    (h : Pre B D g s₀) (hg : g ≤ 8) (hj : j + 1 = g) (i : Inv s₀ B D j s)
    (c : CopyPost s (counterAddr B) (dataAddr D j) s') : Post s₀ B D g s' := by
  have cf : Frame (regions B) s.mem s'.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  have je : j = g - 1 := by omega
  refine ⟨⟨fun r h9 h10 => (c.regs r h9 h10).trans (i.regs r h9 h10), c.rd.trans i.rd,
    c.wr.trans i.wr, c.sp.trans i.sp, i.frame.trans cf, ?_, ?_⟩, ?_⟩
  · rw [bytes_frame (P := bufferAddr B 0) c.frame (fun r hr => ?_)]
    exact i.first
    simp only [List.mem_singleton] at hr; subst hr
    exact buffer_counter_sep B (by decide)
  · intro k hk
    rw [bytes_frame (P := bufferAddr B (k + 1)) c.frame (fun r hr => ?_)]
    exact i.lanes k (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact buffer_counter_sep B (by omega)
  · rw [c.block, i.data_kept h (by omega), je]

theorem steps_wp {s₀ s : State} {B D : BitVec 32} {g j m : Nat}
    (h : Pre B D g s₀) (hg : g ≤ 8) (hj : j < g) (hm : g ≤ j + m) (i : Inv s₀ B D j s) :
    WP isa (BatchCfb.steps j m) s (Post s₀ B D g) := by
  induction m generalizing j s with
  | zero => omega
  | succ m ih =>
    have jj : j < 8 := by omega
    let sc := subFlags s (s.gpr .r11) (BitVec.ofNat 32 (j + 1))
    have ic : Inv s₀ B D j sc := i.cmp _ _
    have pc := ic.pre h
    refine WP.seq (WP.of_runBlock ⟨sc, compare_run s j jj, ?_⟩)
    refine WP.ite (decide (j + 1 = g)) (compare_eq hg jj (i.pre h).group) (fun he => ?_) (fun he => ?_)
    · have eq : j + 1 = g := of_decide_eq_true he
      exact WP.mono (data_copy_wp pc hg hj (by decide)) fun s' c => ic.last h hg eq c
    · have ne : j + 1 ≠ g := by simpa using he
      have jg : j + 1 < g := by omega
      refine WP.seq (WP.mono (data_copy_wp (o := 4 * tailSlot + 16 * (j + 1)) pc hg hj
        (by rw [tailSlot, total_eq]; omega)) fun s' c => ?_)
      exact ih jg (by omega) (ic.next h hg jg c)

theorem fill_wp {s : State} {B D : BitVec 32} {g : Nat} (h : Pre B D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8) :
    WP isa BatchCfb.fill s (Post s B D g) := by
  refine WP.seq (WP.mono (first_wp h) fun s' c => ?_)
  have cf : Frame (regions B) s.mem s'.mem := c.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨bufferAddr B 0, 128⟩, List.mem_cons_self, lane_frame (by decide)⟩
  exact steps_wp h hg8 (by omega) hg8
    ⟨c.regs, c.rd, c.wr, c.sp, cf, c.block, fun _ hk => by omega⟩

end VG.Proof.Sm4.Arm.CfbFill
