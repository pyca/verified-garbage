module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

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
    exact ⟨⟨State.addr D, 16 * g⟩, List.mem_singleton_self _, 16 * j, rfl, by change 16 * j + 16 ≤ 16 * g; omega⟩).trans h.wd

theorem copy_plain_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block ((List.range 4).flatMap (copyWord .r6 sb (16 * j) (4 * tailSlot + 16 * j)))) s
      (CopyPost s (dataAddr D j) (bufferAddr B j)) := by
  apply copyBlock_wp
  exact ⟨by rw [h.data], by rw [h.base], by rw [h.data]; have := h.fitD; omega,
    by rw [h.base]; have := h.fitB; rw [total_eq, tailSlot] at *; omega,
    by change 16 * j + 16 ≤ 4096; omega, by change 4 * tailSlot + 16 * j + 16 ≤ 4096; rw [tailSlot]; omega,
    by decide, by decide, by decide, by decide, data_part h hj,
    Covers.right (workspace_part h.hw (4 * tailSlot + 16 * j) 16 (by rw [tailSlot, total_eq]; omega)),
    (h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega))⟩

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
      by rw [h.data]; have := h.fitD; omega,
      by rw [h.base]; have := h.fitB; change B.toNat + 1512 ≤ 2 ^ 32 at this; change B.toNat + 1492 + 16 ≤ 2 ^ 32; omega,
      by decide, by decide, by decide, by decide, by decide, by decide, data_part h hj,
      Covers.right (workspace_part h.hw 1492 16 (by decide)),
      (h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right CfbFill.counter_frame⟩
  · simp only [he, ↓reduceIte, prevAddr]
    apply xorN_block
    exact ⟨by rw [h.data], by rw [h.data], by rw [h.data]; have := h.fitD; omega,
      by rw [h.data]; have := h.fitD; omega,
      by change 16 * j + 16 ≤ 4096; omega, by change 16 * (j - 1) + 16 ≤ 4096; omega,
      by decide, by decide, by decide, by decide, data_part h hj, Covers.right (data_part h (j := j - 1) (by omega)),
      Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)⟩

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
      exact ((h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right CfbFill.counter_frame).symm
    · simp only [prevAddr, he, ↓reduceIte]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
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
    exact ((h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right
      (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega))).symm
  have prv : bytesAt m' (prevAddr B D k) 16 = bytesAt s.mem (prevAddr B D k) 16 := by
    apply bytes_frame hf
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    by_cases he : k = 0
    · simp only [prevAddr, he, ↓reduceIte]
      exact ((h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right CfbFill.counter_frame).symm
    · simp only [prevAddr, he, ↓reduceIte]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [buf, prv]

theorem prefix_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (BatchCbc.xorPrefix j) s (prefixPost s B D (j + 1)) := by
  induction j generalizing s with
  | zero =>
    refine WP.mono (step_wp h hg hj) fun s' ⟨e, out⟩ => ⟨⟨e.regs, e.rd, e.wr, e.sp, ?_⟩, ?_⟩
    · simpa only [dataAddr, Nat.mul_zero, BitVec.add_zero] using e.frame
    · intro k hk
      have he : k = 0 := by omega
      subst k
      exact out
  | succ j ih =>
    refine WP.seq (WP.mono (step_wp h hg hj) fun s₁ ⟨e, out⟩ => ?_)
    refine WP.mono (ih (e.pre h) (by omega)) fun s₂ ⟨e', blocks⟩ => ?_
    have f₁ : Frame [⟨State.addr D, 16 * (j + 1 + 1)⟩] s.mem s₁.mem := e.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * (j + 1 + 1)⟩, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
    have f₂ : Frame [⟨State.addr D, 16 * (j + 1 + 1)⟩] s₁.mem s₂.mem := e'.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * (j + 1 + 1)⟩, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    refine ⟨⟨fun r h9 h10 => (e'.regs r h9 h10).trans (e.regs r h9 h10), e'.rd.trans e.rd,
      e'.wr.trans e.wr, e'.sp.trans e.sp, f₁.trans f₂⟩, ?_⟩
    intro k hk
    by_cases he : k = j + 1
    · subst k
      rw [bytes_frame (P := dataAddr D (j + 1)) e'.frame (fun r hr => ?_), out]
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
    · rw [blocks k (by omega)]
      exact out_kept h hg hj (by omega) e.frame

theorem choose_wp {s : State} {B D : BitVec 32} {g j m : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) (hm : g ≤ j + m) :
    WP isa (BatchCbc.chooseXor j m) s (prefixPost s B D g) := by
  induction m generalizing j s with
  | zero => omega
  | succ m ih =>
    have jj : j < 8 := by omega
    let sc := subFlags s (s.gpr .r11) (BitVec.ofNat 32 (j + 1))
    have pc : CfbFill.Pre B D g sc := ⟨h.base, h.data, h.group, h.fitB, h.fitD, h.hw, h.wd, h.sep⟩
    refine WP.seq (WP.of_runBlock ⟨sc, CfbFill.compare_run s j jj, ?_⟩)
    refine WP.ite (decide (j + 1 = g)) (CfbFill.compare_eq hg jj h.group) (fun he => ?_) (fun he => ?_)
    · have eq : j + 1 = g := of_decide_eq_true he
      have p := prefix_wp pc hg hj
      rw [eq] at p
      exact p
    · have ne : j + 1 ≠ g := by simpa using he
      exact ih pc (by omega) (by omega)

theorem xor_wp {s : State} {B D : BitVec 32} {g : Nat}
    (h : CfbFill.Pre B D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8) :
    WP isa (BatchCbc.chooseXor 0 8) s (prefixPost s B D g) := choose_wp h hg8 (by omega) hg8

end VG.Proof.Sm4.Arm.CbcReverse
