module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! ### `Sm4.Arm.CbcFill`, which only this module used -/

section

/-! ### `Sm4.Arm.CbcReverse`, which only this module used -/

section

/-! # Combining CBC's decrypted blocks in reverse order -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcReverse
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Impl.Modes.Arm (copyWord xorWord)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

/-- Keep the source's observable fields separate, so flag-only changes are
irrelevant to this effect. -/
structure Effect (g₀ : Reg → BitVec 32) (m₀ : Mem) (rd₀ wr₀ : List Region) (sp₀ : BitVec 32)
    (rs : List Region) (s : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s.gpr r = g₀ r
  rd : s.rd = rd₀
  wr : s.wr = wr₀
  sp : s.sp = sp₀
  frame : Frame rs m₀ s.mem

abbrev effect (s₀ : State) (rs : List Region) (s : State) : Prop :=
  Effect s₀.gpr s₀.mem s₀.rd s₀.wr s₀.sp rs s

def blockPost (s₀ : State) (P : Addr) (out : List Byte) (s : State) : Prop :=
  effect s₀ [⟨P, 16⟩] s ∧ bytesAt s.mem P 16 = out

def prevAddr (B D : BitVec 32) (j : Nat) : Addr :=
  if j = 0 then counterAddr B else dataAddr D (j - 1)

def outBlock (m : Mem) (B D : BitVec 32) (j : Nat) : List Byte :=
  Spec.Cbc.xor (bytesAt m (bufferAddr B j) 16) (bytesAt m (prevAddr B D j) 16)

def prefixPost (s₀ : State) (B D : BitVec 32) (n : Nat) (s : State) : Prop :=
  effect s₀ [⟨State.addr D, 16 * n⟩] s ∧
    ∀ k < n, bytesAt s.mem (dataAddr D k) 16 = outBlock s₀.mem B D k

theorem xorN_block {s : State} {rd rs : Reg} {od os : Nat} {P Q : Addr} (h : NPre 4 s rd rs od os P Q) :
    WP isa (.block ((List.range 4).flatMap (xorWord rd rs od os))) s
      (blockPost s P (Spec.Cbc.xor (bytesAt s.mem P 16) (bytesAt s.mem Q 16))) := by
  refine WP.mono (xorN_wp h) fun s' c => ⟨⟨c.regs, c.rd, c.wr, c.sp, ?_⟩, ?_⟩
  · rw [c.mem]; exact Proof.Modes.over_frame _ _ _ _
  · rw [c.mem, bytesAt_over_self _ _ _ (by decide), xor_bytes]

theorem data_part {s : State} {B D : BitVec 32} {g j : Nat} (h : CfbFill.Pre B D g s) (hj : j < g) :
    Covers [⟨dataAddr D j, 16⟩] s.wr :=
  (Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * g⟩, List.mem_singleton_self _, 16 * j, rfl, by change 16 * j + 16 ≤ 16 * g; omega_using [hj]⟩).trans h.wd

theorem copy_plain_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block ((List.range 4).flatMap (copyWord .r6 sb (16 * j) (4 * tailSlot + 16 * j)))) s
      (CopyPost s (dataAddr D j) (bufferAddr B j)) := by
  apply copyBlock_wp
  exact ⟨by rw [h.data], by rw [h.base], by rw [h.data]; have := h.fitD; omega_using [hj, this],
    by rw [h.base]; have := h.fitB; rw [total_eq, tailSlot] at *; omega_using [hg, hj, this],
    by change 16 * j + 16 ≤ 4096; omega_using [hg, hj], by change 4 * tailSlot + 16 * j + 16 ≤ 4096; rw [tailSlot]; omega_using [hg, hj],
    by decide, by decide, by decide, by decide, data_part h hj,
    Covers.right (workspace_part h.hw (4 * tailSlot + 16 * j) 16 (by rw [tailSlot, total_eq]; omega_using [hg, hj])),
    (h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg, hj]))⟩

theorem xor_prev_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block ((List.range 4).flatMap (if j = 0 then xorWord .r6 sb 0 (4 * BatchCtr.counterSlot)
      else xorWord .r6 .r6 (16 * j) (16 * (j - 1))))) s
      (blockPost s (dataAddr D j) (Spec.Cbc.xor (bytesAt s.mem (dataAddr D j) 16)
        (bytesAt s.mem (prevAddr B D j) 16))) := by
  by_cases he : j = 0
  · subst j
    simp only [↓reduceIte, prevAddr]
    apply xorN_block
    exact ⟨by rw [h.data, BitVec.add_zero]; simp only [dataAddr, Nat.mul_zero, BitVec.add_zero], by rw [h.base],
      by rw [h.data]; have := h.fitD; omega_using [hj, this],
      by rw [h.base]; have := h.fitB; change B.toNat + 1512 ≤ 2 ^ 32 at this; change B.toNat + 1492 + 16 ≤ 2 ^ 32; omega_using [this],
      by decide, by decide, by decide, by decide, by decide, by decide, data_part h hj,
      Covers.right (workspace_part h.hw 1492 16 (by decide)),
      (h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right CfbFill.counter_frame⟩
  · simp only [he, ↓reduceIte, prevAddr]
    apply xorN_block
    exact ⟨by rw [h.data], by rw [h.data], by rw [h.data]; have := h.fitD; omega_using [hj, this],
      by rw [h.data]; have := h.fitD; omega_using [hj, this],
      by change 16 * j + 16 ≤ 4096; omega_using [hg, hj], by change 16 * (j - 1) + 16 ≤ 4096; omega_using [hg, hj],
      by decide, by decide, by decide, by decide, data_part h hj, Covers.right (data_part h (j := j - 1) (by omega_using [hj])),
      Offset.disjoint _ (.inr (by omega_using [he])) (by omega_using [hg, hj]) (by omega_using [hg, hj])⟩

theorem step_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block (BatchCbc.xorBlock j)) s (blockPost s (dataAddr D j) (outBlock s.mem B D j)) := by
  apply (WP.block_append_iff (M := isa)
    (l₁ := (List.range 4).flatMap (copyWord .r6 sb (16 * j) (4 * tailSlot + 16 * j)))
    (l₂ := (List.range 4).flatMap (if j = 0 then xorWord .r6 sb 0 (4 * BatchCtr.counterSlot)
      else xorWord .r6 .r6 (16 * j) (16 * (j - 1))))).mpr
  refine WP.mono (copy_plain_wp h hg hj) fun s₁ c => ?_
  have p : CfbFill.Pre B D g s₁ := ⟨(c.regs _ (by decide) (by decide)).trans h.base,
    (c.regs _ (by decide) (by decide)).trans h.data, (c.regs _ (by decide) (by decide)).trans h.group,
    h.fitB, h.fitD, by rw [c.wr]; exact h.hw, by rw [c.wr]; exact h.wd, h.sep⟩
  have prev : bytesAt s₁.mem (prevAddr B D j) 16 = bytesAt s.mem (prevAddr B D j) 16 := by
    apply bytes_frame c.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    by_cases he : j = 0
    · simp only [prevAddr, he, ↓reduceIte]
      exact ((h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right CfbFill.counter_frame).symm
    · simp only [prevAddr, he, ↓reduceIte]
      exact Offset.disjoint _ (.inl (by omega_using [he])) (by omega_using [hg, hj]) (by omega_using [hg, hj])
  refine WP.mono (xor_prev_wp p hg hj) fun s₂ ⟨x, out⟩ => ?_
  refine ⟨⟨fun r h9 h10 => (x.regs r h9 h10).trans (c.regs r h9 h10), x.rd.trans c.rd,
    x.wr.trans c.wr, x.sp.trans c.sp, c.frame.trans x.frame⟩, ?_⟩
  rw [out, c.block, prev]
  rfl

theorem Effect.pre {s₀ s : State} {B D : BitVec 32} {g : Nat} {rs : List Region}
    (h : CfbFill.Pre B D g s₀) (e : effect s₀ rs s) : CfbFill.Pre B D g s :=
  ⟨(e.regs _ (by decide) (by decide)).trans h.base, (e.regs _ (by decide) (by decide)).trans h.data,
    (e.regs _ (by decide) (by decide)).trans h.group, h.fitB, h.fitD,
    by rw [e.wr]; exact h.hw, by rw [e.wr]; exact h.wd, h.sep⟩

theorem out_kept {s : State} {m' : Mem} {B D : BitVec 32} {g j k : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) (hk : k < j)
    (hf : Frame [⟨dataAddr D j, 16⟩] s.mem m') : outBlock m' B D k = outBlock s.mem B D k := by
  unfold outBlock
  have buf : bytesAt m' (bufferAddr B k) 16 = bytesAt s.mem (bufferAddr B k) 16 := by
    apply bytes_frame hf
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right
      (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg, hj, hk]))).symm
  have prv : bytesAt m' (prevAddr B D k) 16 = bytesAt s.mem (prevAddr B D k) 16 := by
    apply bytes_frame hf
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    by_cases he : k = 0
    · simp only [prevAddr, he, ↓reduceIte]
      exact ((h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right CfbFill.counter_frame).symm
    · simp only [prevAddr, he, ↓reduceIte]
      exact Offset.disjoint _ (.inl (by omega_using [hk])) (by omega_using [hg, hj, hk]) (by omega_using [hg, hj])
  rw [buf, prv]

theorem prefix_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (BatchCbc.xorPrefix j) s (prefixPost s B D (j + 1)) := by
  induction j generalizing s with
  | zero =>
    refine WP.mono (step_wp h hg hj) fun s' ⟨e, out⟩ => ⟨⟨e.regs, e.rd, e.wr, e.sp, ?_⟩, ?_⟩
    · simpa only [dataAddr, Nat.mul_zero, BitVec.add_zero] using e.frame
    · intro k hk
      have he : k = 0 := by omega_using [hk]
      subst k
      exact out
  | succ j ih =>
    refine WP.seq (WP.mono (step_wp h hg hj) fun s₁ ⟨e, out⟩ => ?_)
    refine WP.mono (ih (e.pre h) (by omega_using [hj])) fun s₂ ⟨e', blocks⟩ => ?_
    have f₁ : Frame [⟨State.addr D, 16 * (j + 1 + 1)⟩] s.mem s₁.mem := e.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * (j + 1 + 1)⟩, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [])⟩
    have f₂ : Frame [⟨State.addr D, 16 * (j + 1 + 1)⟩] s₁.mem s₂.mem := e'.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * (j + 1 + 1)⟩, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
    refine ⟨⟨fun r h9 h10 => (e'.regs r h9 h10).trans (e.regs r h9 h10), e'.rd.trans e.rd,
      e'.wr.trans e.wr, e'.sp.trans e.sp, f₁.trans f₂⟩, ?_⟩
    intro k hk
    by_cases he : k = j + 1
    · subst k
      rw [bytes_frame (P := dataAddr D (j + 1)) e'.frame (fun r hr => ?_), out]
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_using []) (by omega_using [hg, hj])
    · rw [blocks k (by omega_using [hk, he])]
      exact out_kept h hg hj (by omega_using [hk, he]) e.frame

theorem choose_wp {s : State} {B D : BitVec 32} {g j m : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) (hm : g ≤ j + m) :
    WP isa (BatchCbc.chooseXor j m) s (prefixPost s B D g) := by
  induction m generalizing j s with
  | zero => omega
  | succ m ih =>
    have jj : j < 8 := by omega_using [hg, hj]
    let sc := subFlags s (s.gpr .r11) (BitVec.ofNat 32 (j + 1))
    have pc : CfbFill.Pre B D g sc := ⟨h.base, h.data, h.group, h.fitB, h.fitD, h.hw, h.wd, h.sep⟩
    refine WP.seq (WP.of_runBlock ⟨sc, CfbFill.compare_run s j jj, ?_⟩)
    refine WP.ite (decide (j + 1 = g)) (CfbFill.compare_eq hg jj h.group) (fun he => ?_) (fun he => ?_)
    · have eq : j + 1 = g := of_decide_eq_true he
      have p := prefix_wp pc hg hj
      rw [eq] at p
      exact p
    · have ne : j + 1 ≠ g := by simpa using he
      exact ih pc (by omega_using [hj, ne]) (by omega_using [hm])

theorem xor_wp {s : State} {B D : BitVec 32} {g : Nat}
    (h : CfbFill.Pre B D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8) :
    WP isa (BatchCbc.chooseXor 0 8) s (prefixPost s B D g) := choose_wp h hg8 (by omega_using [hg]) hg8

end VG.Proof.Sm4.Arm.CbcReverse

end

end


/-! # CBC decryption inputs and the ciphertext saved for continuation -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcFill
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.CbcReverse (effect Effect data_part)
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

structure Pre (B I D : BitVec 32) (g : Nat) (s : State) : Prop where
  core : CfbFill.Pre B D g s
  iv : s.gpr .r5 = I
  fitI : I.toNat + 16 ≤ 2 ^ 32
  hi : Covers [⟨State.addr I, 16⟩] s.wr
  id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * g⟩
  ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

def regions (B I : BitVec 32) : List Region := [⟨bufferAddr B 0, 128⟩, ⟨State.addr I, 16⟩]

structure Inv (s₀ : State) (B I D : BitVec 32) (j : Nat) (s : State) : Prop where
  kept : effect s₀ (regions B I) s
  lanes : ∀ k < j, bytesAt s.mem (bufferAddr B k) 16 = bytesAt s₀.mem (dataAddr D k) 16

structure Post (s₀ : State) (B I D : BitVec 32) (g : Nat) (s : State) : Prop extends Inv s₀ B I D g s where
  iv : bytesAt s.mem (State.addr I) 16 = bytesAt s₀.mem (dataAddr D (g - 1)) 16

theorem Inv.pre {s₀ s : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s₀) (i : Inv s₀ B I D j s) : Pre B I D g s :=
  ⟨i.kept.pre h.core, (i.kept.regs _ (by decide) (by decide)).trans h.iv, h.fitI,
    by rw [i.kept.wr]; exact h.hi, h.id, h.ib⟩

theorem Inv.cmp {s₀ s : State} {B I D : BitVec 32} {j : Nat} (h : Inv s₀ B I D j s) (a b : BitVec 32) :
    Inv s₀ B I D j (subFlags s a b) :=
  ⟨⟨h.kept.regs, h.kept.rd, h.kept.wr, h.kept.sp, h.kept.frame⟩, h.lanes⟩

theorem Inv.data_kept {s₀ s : State} {B I D : BitVec 32} {g j k : Nat}
    (h : Pre B I D g s₀) (i : Inv s₀ B I D j s) (hk : k < g) :
    bytesAt s.mem (dataAddr D k) 16 = bytesAt s₀.mem (dataAddr D k) 16 := by
  apply bytes_frame i.kept.frame
  intro r hr
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.core.sep.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right (Offset.sub_base _ (by decide))
  · exact h.id.symm.sub_left (Offset.sub_base _ (by omega_using [hk]))

theorem save_wp {s : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block (BatchCbc.saveLast j)) s (CopyPost s (State.addr I) (dataAddr D j)) := by
  apply copyBlock_wp
  exact ⟨by rw [h.iv, BitVec.add_zero], by rw [h.core.data],
    by rw [h.iv]; have := h.fitI; omega_using [this],
    by rw [h.core.data]; have := h.core.fitD; omega_using [hj, this],
    by decide, by change 16 * j + 16 ≤ 4096; omega_using [hg, hj],
    by decide, by decide, by decide, by decide, h.hi, Covers.right (data_part h.core hj),
    h.id.sub_right (Offset.sub_base _ (by omega_using [hj]))⟩

theorem Inv.copy {s₀ s s' : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j < g) (i : Inv s₀ B I D j s)
    (c : CopyPost s (bufferAddr B j) (dataAddr D j) s') : Inv s₀ B I D (j + 1) s' := by
  have cf : Frame (regions B I) s.mem s'.mem := c.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨bufferAddr B 0, 128⟩, List.mem_cons_self, CfbFill.lane_frame (by omega_using [hg, hj])⟩
  refine ⟨⟨fun r h9 h10 => (c.regs r h9 h10).trans (i.kept.regs r h9 h10), c.rd.trans i.kept.rd,
    c.wr.trans i.kept.wr, c.sp.trans i.kept.sp, i.kept.frame.trans cf⟩, ?_⟩
  intro k hk
  by_cases he : k = j
  · subst k
    rw [c.block, i.data_kept h hj]
  · rw [bytes_frame (P := bufferAddr B k) c.frame (fun r hr => ?_)]
    exact i.lanes k (by omega_using [hk, he])
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by change 4 * tailSlot + 16 * k + 16 ≤ 4 * tailSlot + 16 * j; omega_using [hk, he]))
      (by change 4 * tailSlot + 16 * k + 16 ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg, hj, hk])
      (by change 4 * tailSlot + 16 * j + 16 ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg, hj])

theorem Inv.last {s₀ s s' : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j + 1 = g) (i : Inv s₀ B I D g s)
    (c : CopyPost s (State.addr I) (dataAddr D j) s') : Post s₀ B I D g s' := by
  have cf : Frame (regions B I) s.mem s'.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  refine ⟨⟨⟨fun r h9 h10 => (c.regs r h9 h10).trans (i.kept.regs r h9 h10), c.rd.trans i.kept.rd,
    c.wr.trans i.kept.wr, c.sp.trans i.kept.sp, i.kept.frame.trans cf⟩, ?_⟩, ?_⟩
  · intro k hk
    rw [bytes_frame (P := bufferAddr B k) c.frame (fun r hr => ?_)]
    exact i.lanes k hk
    simp only [List.mem_singleton] at hr; subst hr
    exact h.ib.symm.sub_left (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg, hk]))
  · rw [c.block, i.data_kept h (by omega_using [hj]), show j = g - 1 by omega_using [hj]]

theorem steps_wp {s₀ s : State} {B I D : BitVec 32} {g j m : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j < g) (hm : g ≤ j + m) (i : Inv s₀ B I D j s) :
    WP isa (BatchCbc.fillSteps j m) s (Post s₀ B I D g) := by
  induction m generalizing j s with
  | zero => omega
  | succ m ih =>
    have jj : j < 8 := by omega_using [hg, hj]
    have p := i.pre h
    refine WP.seq ?_
    apply (WP.block_append_iff (M := isa) (l₁ := BatchCbc.copyLane j)
      (l₂ := [.cmp .r11 (.imm (BitVec.ofNat 32 (j + 1)))])).mpr
    refine WP.mono (CfbFill.data_copy_wp (o := 4 * tailSlot + 16 * j) p.core hg hj
      (by rw [tailSlot, total_eq]; omega_using [jj])) fun s₁ c => ?_
    have i₁ := i.copy h hg hj c
    let sc := subFlags s₁ (s₁.gpr .r11) (BitVec.ofNat 32 (j + 1))
    have ic : Inv s₀ B I D (j + 1) sc := i₁.cmp _ _
    refine WP.of_runBlock ⟨sc, CfbFill.compare_run s₁ j jj, ?_⟩
    refine WP.ite (decide (j + 1 = g)) (CfbFill.compare_eq hg jj (i₁.pre h).core.group) (fun he => ?_) (fun he => ?_)
    · have eq : j + 1 = g := of_decide_eq_true he
      have icg : Inv s₀ B I D g sc := eq ▸ ic
      exact WP.mono (save_wp (ic.pre h) hg hj) fun s' cp => icg.last h hg eq cp
    · have ne : j + 1 ≠ g := by simpa using he
      exact ih (by omega_using [hj, ne]) (by omega_using [hm]) ic

theorem fill_wp {s : State} {B I D : BitVec 32} {g : Nat}
    (h : Pre B I D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8) : WP isa BatchCbc.fill s (Post s B I D g) := by
  refine WP.seq (WP.of_runBlock ⟨s, CfbFill.pad_run s, ?_⟩)
  exact steps_wp h hg8 (by omega_using [hg]) hg8
    ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩, fun _ hk => by omega⟩

end VG.Proof.Sm4.Arm.CbcFill

end

end


/-! # One batch of CBC decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcGroup
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchGroup (blockAt_of_ecb table_frame count_wp difference_zero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

def regions (B I D : BitVec 32) (g : Nat) : List Region :=
  [⟨State.addr B, 4 * slots⟩, ⟨counterAddr B, 16⟩, ⟨State.addr I, 16⟩, ⟨State.addr D, 16 * g⟩]

def prevBlock (m : Mem) (B D : BitVec 32) (k : Nat) : List Byte :=
  if k = 0 then bytesAt m (counterAddr B) 16 else bytesAt m (dataAddr D (k - 1)) 16

theorem decrypted_lane {K : Spec.Sm4.Schedule} {m m' : Mem} {B : BitVec 32}
    (h : Spec.Sm4.blocksAt m' (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb K .decrypt (Spec.Sm4.blocksAt m (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks))
    {j : Nat} (hj : j < 8) :
    bytesAt m' (bufferAddr B j) 16 = Spec.Sm4.invCipher K (bytesAt m (bufferAddr B j) 16) := by
  have hb := blockAt_of_ecb h hj
  have ha : State.addr B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) = bufferAddr B j := by
    rw [Offset.add_add]; rfl
  rw [ha] at hb
  rw [Proof.Sm4.bytesAt_eq_blockAt, hb]
  rw [Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]
  rfl

structure BatchPost (s : State) (B I D : BitVec 32) (K : Spec.Sm4.Schedule) (g : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r6, .r7, .r8, .r11], s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (regions B I D g) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .decrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16)) (prevBlock s.mem B D k)

def batch : Prog isa := .seq BatchCbc.fill
  (.seq BatchCtr.crypt (.seq (BatchCbc.chooseXor 0 8) (.block BatchCtr.copyCounterIn)))

theorem batch_wp {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {g : Nat}
    (h : CbcFill.Pre B I D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8)
    (hH : Holds layout s.mem (State.addr B) K .decrypt) : WP isa batch s (BatchPost s B I D K g) := by
  refine WP.seq (WP.mono (CbcFill.fill_wp h hg hg8) fun s₁ f => ?_)
  have p₁ := f.toInv.pre h
  have hH₁ : Holds layout s₁.mem (State.addr B) K .decrypt := table_frame hH f.kept.frame fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left (Offset.sub_base _ (by decide))
  have counter₁ : bytesAt s₁.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    apply bytes_frame f.kept.frame
    intro r hr
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left CfbFill.counter_frame
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f.kept.wr]
    simpa only [BitVec.add_zero] using workspace_part h.core.hw 0 (4 * slots) (by decide)
  refine WP.seq (WP.mono (BatchCalls.crypt_wp p₁.core.base
    (by have := h.core.fitB; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this])
    wc hH₁) fun s₂ ⟨c, table₂, ecb₂⟩ => ?_)
  have p₂ : CbcFill.Pre B I D g s₂ := ⟨⟨(c.regs _ (by decide) (by decide)).trans p₁.core.base,
    (c.regs _ (by decide) (by decide)).trans p₁.core.data, (c.regs _ (by decide) (by decide)).trans p₁.core.group,
    h.core.fitB, h.core.fitD, by rw [c.wr]; exact p₁.core.hw, by rw [c.wr]; exact p₁.core.wd, h.core.sep⟩,
    (c.regs _ (by decide) (by decide)).trans p₁.iv, h.fitI, by rw [c.wr]; exact p₁.hi, h.id, h.ib⟩
  have iv₂ : bytesAt s₂.mem (State.addr I) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16 := by
    rw [bytes_frame (P := State.addr I) c.frame (fun r hr => ?_), f.iv]
    simp only [List.mem_singleton] at hr; subst hr
    exact h.ib.sub_right (Region.sub_prefix (by decide))
  have data₂ : ∀ k < g, bytesAt s₂.mem (dataAddr D k) 16 = bytesAt s.mem (dataAddr D k) 16 := by
    intro k hk
    rw [bytes_frame (P := dataAddr D k) c.frame (fun r hr => ?_), f.toInv.data_kept h hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.core.sep.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right (Region.sub_prefix (by decide))
  have counter₂ : bytesAt s₂.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    rw [bytes_frame (P := counterAddr B) c.frame (fun r hr => ?_), counter₁]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  have plain₂ : ∀ k < g, bytesAt s₂.mem (bufferAddr B k) 16 = Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16) := by
    intro k hk
    rw [decrypted_lane ecb₂ (by omega_using [hg8, hk]), f.lanes k hk]
  refine WP.seq (WP.mono (CbcReverse.xor_wp p₂.core hg hg8) fun s₃ ⟨x, blocks⟩ => ?_)
  have p₃ : ChainPre s₃ B I := ⟨(x.regs _ (by decide) (by decide)).trans p₂.core.base,
    (x.regs _ (by decide) (by decide)).trans p₂.iv, h.core.fitB, h.fitI,
    by rw [x.wr]; exact p₂.core.hw, by rw [x.wr]; exact p₂.hi, h.ib⟩
  have iv₃ : bytesAt s₃.mem (State.addr I) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16 := by
    rw [bytes_frame (P := State.addr I) x.frame (fun r hr => ?_), iv₂]
    simp only [List.mem_singleton] at hr; subst hr
    exact h.id
  have table₃ := table_frame table₂ x.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.core.sep.symm.sub_left (Offset.sub_base _ (by decide)))
  refine WP.mono (counterIn_wp p₃) fun s₄ v => ?_
  have ff : Frame (regions B I D g) s.mem s₁.mem := f.kept.frame.sub fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr B, 4 * slots⟩, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr I, 16⟩, by simp [regions], fun _ h => h⟩
  have fc : Frame (regions B I D g) s₁.mem s₂.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  have fx : Frame (regions B I D g) s₂.mem s₃.mem := x.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  have fv : Frame (regions B I D g) s₃.mem s₄.mem := v.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  refine ⟨?_, v.rd.trans (x.rd.trans (c.rd.trans f.kept.rd)), v.wr.trans (x.wr.trans (c.wr.trans f.kept.wr)),
    v.sp.trans (x.sp.trans (c.sp.trans f.kept.sp)), ((ff.trans fc).trans fx).trans fv, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [v.regs _ (by decide) (by decide), x.regs _ (by decide) (by decide), c.regs _ (by decide) (by decide), f.kept.regs _ (by decide) (by decide)]
  · exact table_frame table₃ v.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  · rw [v.block, iv₃]
  · intro k hk
    rw [bytes_frame (P := dataAddr D k) v.frame (fun r hr => ?_), blocks k hk]
    unfold CbcReverse.outBlock
    rw [plain₂ k hk]
    by_cases he : k = 0
    · simp only [CbcReverse.prevAddr, prevBlock, he, ↓reduceIte]
      rw [counter₂]
    · simp only [CbcReverse.prevAddr, prevBlock, he, ↓reduceIte]
      rw [data₂ (k - 1) (by omega_using [hk])]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.core.sep.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right CfbFill.counter_frame

structure Pre (B I D : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  iv : s.gpr .r5 = I
  data : s.gpr .r6 = D
  left : s.gpr .r7 = BitVec.ofNat 32 n
  fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  fitI : I.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  hi : Covers [⟨State.addr I, 16⟩] s.wr
  wd : Covers [⟨State.addr D, 16 * n⟩] s.wr
  id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩
  ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩
  db : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

structure GroupPost (s : State) (B I D : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * min n 8)
  left : s'.gpr .r7 = BitVec.ofNat 32 (n - min n 8)
  z : s'.z = decide (n = min n 8)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (regions B I D (min n 8)) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .decrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (dataAddr D (min n 8 - 1)) 16
  blocks : ∀ k < min n 8, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16)) (prevBlock s.mem B D k)

theorem shift_group (g : Nat) : (BitVec.ofNat 32 g <<< 4) = BitVec.ofNat 32 (16 * g) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 g * BitVec.ofNat 32 16 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

theorem group_wp {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (h : Pre B I D n s) (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (hH : Holds layout s.mem (State.addr B) K .decrypt) : WP isa BatchCbc.group s (GroupPost s B I D K n) := by
  have hgN : min n 8 ≤ n := Nat.min_le_left _ _
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  have hg : 1 ≤ min n 8 := by omega_using [hn]
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  have wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero], by change 0 + 16 * min n 8 ≤ 16 * n; omega_using []⟩
  have fp : CbcFill.Pre B I D (min n 8) s₁ := ⟨⟨(o₁ _ (by decide) (by decide)).trans h.base,
    (o₁ _ (by decide) (by decide)).trans h.data, g₁, h.fitB, by have := h.fitD; omega_using [this],
    by rw [wr₁]; exact h.hw, wd₁, h.db.sub_left (Region.sub_prefix (by omega_using []))⟩,
    (o₁ _ (by decide) (by decide)).trans h.iv, h.fitI, by rw [wr₁]; exact h.hi,
    h.id.sub_right (Region.sub_prefix (by omega_using [])), h.ib⟩
  refine WP.seq (WP.mono (batch_wp fp hg hg8 (by rw [m₁]; exact hH)) fun s₂ b => ?_)
  have d₂ : s₂.gpr .r6 = D := (b.regs _ (by simp)).trans fp.core.data
  have n₂ : s₂.gpr .r7 = BitVec.ofNat 32 n := (b.regs _ (by simp)).trans ((o₁ _ (by decide) (by decide)).trans h.left)
  have g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (min n 8) := (b.regs _ (by simp)).trans g₁
  refine Proof.MdStream.Arm.wp_mov (show Op2.eval s₂ (.shifted .r11 .lsl 4) = some (s₂.gpr .r11 <<< 4) from rfl) fun s₃ u₃ => ?_
  refine Proof.MdStream.Arm.wp_add (Proof.MdStream.Arm.op2_reg s₃ .r0) fun s₄ u₄ => ?_
  refine Proof.MdStream.Arm.wp_subs (Proof.MdStream.Arm.op2_reg s₄ .r11) fun s₅ u₅ hz => ?_
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (b.rd.trans rd₁))),
    u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (b.wr.trans wr₁))), u₅.sp.trans (u₄.sp.trans (u₃.sp.trans (b.sp.trans sp₁))), ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), b.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), d₂, u₃.gpr, g₂, shift_group]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), n₂,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    exact Offset.ofNat_sub_ofNat hgN
  · rw [hz, u₄.other _ (by decide), u₃.other _ (by decide), n₂,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    exact difference_zero hn32 hgN
  · rw [u₅.mem, u₄.mem, u₃.mem, ← m₁]; exact b.frame
  · rw [u₅.mem, u₄.mem, u₃.mem]; exact b.table
  · rw [u₅.mem, u₄.mem, u₃.mem, b.counter, m₁]
  · intro k hk
    rw [u₅.mem, u₄.mem, u₃.mem, b.blocks k hk, m₁]

end VG.Proof.Sm4.Arm.CbcGroup
