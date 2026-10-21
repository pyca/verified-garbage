module

public import VerifiedGarbage.Proof.Sm4.Arm.CbcReverse
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

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
  · exact (h.core.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
  · exact h.id.symm.sub_left (Offset.sub_base _ (by omega))

theorem save_wp {s : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block (BatchCbc.saveLast j)) s (CopyPost s (State.addr I) (dataAddr D j)) := by
  apply copyBlock_wp
  exact ⟨by rw [h.iv, BitVec.add_zero], by rw [h.core.data],
    by rw [h.iv]; have := h.fitI; omega,
    by rw [h.core.data]; have := h.core.fitD; omega,
    by decide, by change 16 * j + 16 ≤ 4096; omega,
    by decide, by decide, by decide, by decide, h.hi, Covers.right (data_part h.core hj),
    h.id.sub_right (Offset.sub_base _ (by omega))⟩

theorem Inv.copy {s₀ s s' : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j < g) (i : Inv s₀ B I D j s)
    (c : CopyPost s (bufferAddr B j) (dataAddr D j) s') : Inv s₀ B I D (j + 1) s' := by
  have cf : Frame (regions B I) s.mem s'.mem := c.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨bufferAddr B 0, 128⟩, List.mem_cons_self, CfbFill.lane_frame (by omega)⟩
  refine ⟨⟨fun r h9 h10 => (c.regs r h9 h10).trans (i.kept.regs r h9 h10), c.rd.trans i.kept.rd,
    c.wr.trans i.kept.wr, c.sp.trans i.kept.sp, i.kept.frame.trans cf⟩, ?_⟩
  intro k hk
  by_cases he : k = j
  · subst k
    rw [c.block, i.data_kept h hj]
  · rw [bytes_frame (P := bufferAddr B k) c.frame (fun r hr => ?_)]
    exact i.lanes k (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by change 4 * tailSlot + 16 * k + 16 ≤ 4 * tailSlot + 16 * j; omega))
      (by change 4 * tailSlot + 16 * k + 16 ≤ 2 ^ 64; rw [tailSlot]; omega)
      (by change 4 * tailSlot + 16 * j + 16 ≤ 2 ^ 64; rw [tailSlot]; omega)

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
    exact h.ib.symm.sub_left (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega))
  · rw [c.block, i.data_kept h (by omega), show j = g - 1 by omega]

theorem steps_wp {s₀ s : State} {B I D : BitVec 32} {g j m : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j < g) (hm : g ≤ j + m) (i : Inv s₀ B I D j s) :
    WP isa (BatchCbc.fillSteps j m) s (Post s₀ B I D g) := by
  induction m generalizing j s with
  | zero => omega
  | succ m ih =>
    have jj : j < 8 := by omega
    have p := i.pre h
    refine WP.seq ?_
    apply (WP.block_append_iff (M := isa) (l₁ := BatchCbc.copyLane j)
      (l₂ := [.cmp .r11 (.imm (BitVec.ofNat 32 (j + 1)))])).mpr
    refine WP.mono (CfbFill.data_copy_wp (o := 4 * tailSlot + 16 * j) p.core hg hj
      (by rw [tailSlot, total_eq]; omega)) fun s₁ c => ?_
    have i₁ := i.copy h hg hj c
    let sc := subFlags s₁ (s₁.gpr .r11) (BitVec.ofNat 32 (j + 1))
    have ic : Inv s₀ B I D (j + 1) sc := i₁.cmp _ _
    refine WP.of_runBlock ⟨sc, CfbFill.compare_run s₁ j jj, ?_⟩
    refine WP.ite (decide (j + 1 = g)) (CfbFill.compare_eq hg jj (i₁.pre h).core.group) (fun he => ?_) (fun he => ?_)
    · have eq : j + 1 = g := of_decide_eq_true he
      have icg : Inv s₀ B I D g sc := eq ▸ ic
      exact WP.mono (save_wp (ic.pre h) hg hj) fun s' cp => icg.last h hg eq cp
    · have ne : j + 1 ≠ g := by simpa using he
      exact ih (by omega) (by omega) ic

theorem fill_wp {s : State} {B I D : BitVec 32} {g : Nat}
    (h : Pre B I D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8) : WP isa BatchCbc.fill s (Post s B I D g) := by
  refine WP.seq (WP.of_runBlock ⟨s, CfbFill.pad_run s, ?_⟩)
  exact steps_wp h hg8 (by omega) hg8
    ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩, fun _ hk => by omega⟩

end VG.Proof.Sm4.Arm.CbcFill
