module

public import VerifiedGarbage.Proof.Modes.Arm.Ops
public import VerifiedGarbage.Impl.Modes.Arm.Wide
import VerifiedGarbage.Proof.Modes.Arm.Counter
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# A group's block operations on ARMv7, and what they compute

A group of a wide mode (`Impl.Modes.Arm.WMode`) works on its `G` data blocks
(at `r6`), the `G` blocks of the buffer on the stack (at `r12`), and the
chaining and spare blocks of the scratch buffer (at `r8`): `WBlks` holds
their contents, `wrunOp` is what an operation does to them, and
`wopsCode_wp` says that the code of a list of operations
(`Core.wopsCode`) leaves them as `wrunOps` says, changing only them and
`r9`, `r10` (`WBlkMem`, with the blocks where `WLay` puts them), as
`opsCode_wp` does for the three blocks of a mode one block at a time.
-/

-- separate module: the operations' proofs cost more than their imports, so a change to the groups' proof (`Wide.lean`) does not check them again.

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (over)

/-- The contents of a group's blocks. -/
abbrev WBlks := WBlk → List Byte

/-- The blocks, with `v` as block `x`. -/
def wset (b : WBlks) (x : WBlk) (v : List Byte) : WBlks := fun y => if y = x then v else b y

theorem wset_self (b : WBlks) (x : WBlk) (v : List Byte) : wset b x v x = v := by
  simp only [wset, ↓reduceIte]

theorem wset_of_ne (b : WBlks) {x y : WBlk} (v : List Byte) (h : y ≠ x) : wset b x v y = b y := by
  simp only [wset, h, ↓reduceIte]

/-- What an operation does to the blocks. -/
def wrunOp : WOp → WBlks → WBlks
  | .inc, b => wset b .o (Spec.Ctr.inc (b .o))
  | .copy x y, b => wset b x (b y)
  | .xor x y, b => wset b x (Spec.Cbc.xor (b x) (b y))

/-- The operations, in order. -/
def wrunOps (ops : List WOp) (b : WBlks) : WBlks := ops.foldl (fun b op => wrunOp op b) b

/-- A block of a group of `G`. -/
def _root_.VG.Impl.Modes.Arm.WBlk.ok (G : Nat) : WBlk → Bool
  | .d j => decide (j < G)
  | .w j => decide (j < G)
  | _ => true

/-- An operation on two different blocks of a group of `G`. -/
def wopOk (bs G : Nat) : WOp → Bool
  | .inc => bs == 16
  | .copy x y => x != y && x.ok G && y.ok G
  | .xor x y => x != y && x.ok G && y.ok G

/-! ## Where the blocks are -/

/-- The arrays the blocks are in: the data, the scratch buffer and the
buffer on the stack. -/
inductive WArr | data | scr | buf
  deriving DecidableEq

/-- The array of a block. -/
def warr : WBlk → WArr
  | .d _ => .data
  | .w _ => .buf
  | .o => .scr
  | .t => .scr

/-- The address of each array, with the group's data at `D`, the scratch
buffer at `S` and the buffer on the stack at `W`. -/
def WArr.ptr (D S W : BitVec 32) : WArr → BitVec 32
  | .data => D
  | .scr => S
  | .buf => W

/-- The size of each array: `G` blocks, and the scratch buffer as far as
the end of the spare block. -/
def WArr.len (c : Core) (G : Nat) : WArr → Nat
  | .data => c.bs * G
  | .scr => oOff + 2 * c.bs
  | .buf => c.bs * G

/-- The address of each block. -/
def waddr (c : Core) (D S W : BitVec 32) (x : WBlk) : Addr :=
  State.addr ((warr x).ptr D S W) + BitVec.ofNat 64 (c.wbase x).2

/-- The blocks' layout: the arrays within the address space, their blocks'
offsets in reach, the group's data, the chaining and spare blocks and the
buffer writable (in `wr`), and the arrays apart. -/
structure WLay (c : Core) (G : Nat) (D S W : BitVec 32) (wr : List Region) : Prop where
  bw : 0 < c.bw
  off : ∀ a : WArr, a.len c G ≤ 4096
  fit : ∀ a : WArr, (a.ptr D S W).toNat + a.len c G ≤ 2 ^ 32
  wD : Covers [⟨State.addr D, c.bs * G⟩] wr
  wS : Covers [⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩] wr
  wW : Covers [⟨State.addr W, c.bs * G⟩] wr
  sep : ∀ a a' : WArr, a ≠ a' →
    Region.Disjoint ⟨State.addr (a.ptr D S W), a.len c G⟩ ⟨State.addr (a'.ptr D S W), a'.len c G⟩

/-- The blocks' contents in memory. -/
def WBlkMem (c : Core) (G : Nat) (D S W : BitVec 32) (m : Mem) (b : WBlks) : Prop :=
  ∀ x, x.ok G = true → bytesAt m (waddr c D S W x) c.bs = b x

/-- The regions of the blocks. -/
abbrev wblkRegions (c : Core) (G : Nat) (D S W : BitVec 32) : List Region :=
  [⟨State.addr D, c.bs * G⟩, ⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩, ⟨State.addr W, c.bs * G⟩]

/-- A block of the group lies within its array. -/
theorem wfit {c : Core} {G : Nat} {x : WBlk} (hx : x.ok G = true) : (c.wbase x).2 + c.bs ≤ (warr x).len c G := by
  cases x with
  | d j => exact VG.Proof.Modes.idx_lt (by simpa [WBlk.ok] using hx)
  | w j => exact VG.Proof.Modes.idx_lt (by simpa [WBlk.ok] using hx)
  | o => show oOff + c.bs ≤ oOff + 2 * c.bs; omega_arith
  | t => show oOff + c.bs + c.bs ≤ oOff + 2 * c.bs; omega_arith

/-- Two different blocks are in different arrays, or apart in the same. -/
theorem wapart {c : Core} {x y : WBlk} (hxy : x ≠ y) :
    warr x ≠ warr y ∨ (c.wbase x).2 + c.bs ≤ (c.wbase y).2 ∨ (c.wbase y).2 + c.bs ≤ (c.wbase x).2 := by
  cases x <;> cases y <;>
    first
    | (left; simp [warr]; done)
    | exact absurd rfl hxy
    | exact .inr (.inl (Nat.le_refl _))
    | exact .inr (.inr (Nat.le_refl _))
    | skip
  all_goals
    rename_i j k
    rcases Nat.lt_or_gt_of_ne (fun e : j = k => hxy (by rw [e])) with h | h
    · exact .inr (.inl (VG.Proof.Modes.idx_lt h))
    · exact .inr (.inr (VG.Proof.Modes.idx_lt h))

theorem wbase_ne9 (c : Core) (x : WBlk) : (c.wbase x).1 ≠ .r9 := by cases x <;> simp [Core.wbase]
theorem wbase_ne10 (c : Core) (x : WBlk) : (c.wbase x).1 ≠ .r10 := by cases x <;> simp [Core.wbase]

namespace WLay

variable {c : Core} {G : Nat} {D S W : BitVec 32} {wr : List Region} (h : WLay c G D S W wr)
include h

omit h in
/-- A block, within its array. -/
theorem sub_arr {x : WBlk} (hx : x.ok G = true) :
    Region.Sub ⟨waddr c D S W x, c.bs⟩ ⟨State.addr ((warr x).ptr D S W), (warr x).len c G⟩ :=
  VG.Offset.sub_base _ (wfit hx)

omit h in
/-- A block, within the regions of the blocks. -/
theorem sub {x : WBlk} (hx : x.ok G = true) :
    ∃ r ∈ wblkRegions c G D S W, Region.Sub ⟨waddr c D S W x, c.bs⟩ r := by
  have fx := wfit (c := c) hx
  cases x with
  | d j => exact ⟨_, List.mem_cons_self, VG.Offset.sub_base _ fx⟩
  | w j => exact ⟨⟨State.addr W, c.bs * G⟩, by simp, VG.Offset.sub_base _ fx⟩
  | o => exact ⟨⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩, by simp, Region.sub_prefix (by omega_arith)⟩
  | t =>
    refine ⟨⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩, by simp, ?_⟩
    show Region.Sub ⟨State.addr S + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ _
    rw [← VG.Offset.add_add]; exact VG.Offset.sub_base _ (by omega_arith)

theorem writable {x : WBlk} (hx : x.ok G = true) : Covers [⟨waddr c D S W x, c.bs⟩] wr := by
  have fx := wfit (c := c) hx
  cases x with
  | d j =>
    exact Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, c.bs * j, rfl, fx⟩) h.wD
  | w j =>
    exact Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, c.bs * j, rfl, fx⟩) h.wW
  | o =>
    exact Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, 0, (add0 _).symm, by show 0 + c.bs ≤ 2 * c.bs; omega_arith⟩) h.wS
  | t =>
    exact Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, c.bs, (VG.Offset.add_add _ _ _).symm,
        by show c.bs + c.bs ≤ 2 * c.bs; omega_arith⟩) h.wS

theorem disjoint {x y : WBlk} (hx : x.ok G = true) (hy : y.ok G = true) (hxy : x ≠ y) :
    Region.Disjoint ⟨waddr c D S W x, c.bs⟩ ⟨waddr c D S W y, c.bs⟩ := by
  have fx := wfit (c := c) hx
  have fy := wfit (c := c) hy
  by_cases he : warr x = warr y
  · rcases wapart (c := c) hxy with ha | ha
    · exact absurd he ha
    · have := h.fit (warr y)
      unfold waddr
      rw [he] at fx ⊢
      exact VG.Offset.disjoint _ ha (by omega_using [fx, this]) (by omega_using [fy, this])
  · exact ((h.sep _ _ he).sub_left (sub_arr hx)).sub_right (sub_arr hy)

omit h in
/-- The base register and offset of a block give its address. -/
theorem base_addr {s : State} (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = S) (h12 : s.gpr .r12 = W) (x : WBlk) :
    State.addr (s.gpr (c.wbase x).1) + BitVec.ofNat 64 (c.wbase x).2 = waddr c D S W x := by
  cases x
  · simp [Core.wbase, waddr, warr, WArr.ptr, h6]
  · simp [Core.wbase, waddr, warr, WArr.ptr, h12]
  · simp [Core.wbase, waddr, warr, WArr.ptr, h8]
  · simp [Core.wbase, waddr, warr, WArr.ptr, h8]

omit h in
theorem base_gpr {s : State} (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = S) (h12 : s.gpr .r12 = W) (x : WBlk) :
    s.gpr (c.wbase x).1 = (warr x).ptr D S W := by
  cases x
  · simp [Core.wbase, warr, WArr.ptr, h6]
  · simp [Core.wbase, warr, WArr.ptr, h12]
  · simp [Core.wbase, warr, WArr.ptr, h8]
  · simp [Core.wbase, warr, WArr.ptr, h8]

theorem base_fit {s : State} (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = S) (h12 : s.gpr .r12 = W) {x : WBlk}
    (hx : x.ok G = true) : (s.gpr (c.wbase x).1).toNat + (c.wbase x).2 + c.bs ≤ 2 ^ 32 := by
  have fx := wfit (c := c) hx
  have := h.fit (warr x)
  rw [base_gpr h6 h8 h12]; omega_using [fx, this]

theorem base_off {x : WBlk} (hx : x.ok G = true) : (c.wbase x).2 + c.bs ≤ 4096 := by
  have fx := wfit (c := c) hx
  have := h.off (warr x)
  omega_using [fx, this]

/-- Byte `k` of block `x`, through its base register. -/
theorem byte_addr {s : State} (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = S) (h12 : s.gpr .r12 = W) {x : WBlk}
    (hx : x.ok G = true) {k : Nat} (hk : k < c.bs) :
    State.addr (s.gpr (c.wbase x).1 + BitVec.ofNat 32 ((c.wbase x).2 + k)) =
      waddr c D S W x + BitVec.ofNat 64 k := by
  have := h.base_fit h6 h8 h12 hx
  rw [addr_add (by omega_using [this, hk]), ← VG.Offset.add_add, base_addr h6 h8 h12]

/-- The `NPre` of an operation on the blocks `x ← y`. -/
theorem npre {s : State} (hwr : s.wr = wr) (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = S) (h12 : s.gpr .r12 = W)
    {x y : WBlk} (hx : x.ok G = true) (hy : y.ok G = true) (hxy : x ≠ y) :
    NPre c.bw s (c.wbase x).1 (c.wbase y).1 (c.wbase x).2 (c.wbase y).2 (waddr c D S W x) (waddr c D S W y) :=
  { hP := base_addr h6 h8 h12 x
    hQ := base_addr h6 h8 h12 y
    fP := h.base_fit h6 h8 h12 hx
    fQ := h.base_fit h6 h8 h12 hy
    oP := h.base_off hx
    oQ := h.base_off hy
    d9 := wbase_ne9 c x
    d10 := wbase_ne10 c x
    s9 := wbase_ne9 c y
    s10 := wbase_ne10 c y
    wP := by rw [hwr]; exact h.writable hx
    rQ := by rw [hwr]; exact Covers.right (h.writable hy)
    sep := h.disjoint hx hy hxy }

end WLay

/-! ## One operation, and a list of them -/

/-- What the code of operations from `s` keeps. -/
structure WOpsInv (c : Core) (G : Nat) (D S W : BitVec 32) (s : State) (b : WBlks) (s' : State) : Prop where
  regs : ∀ x, x ≠ .r9 → x ≠ .r10 → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (wblkRegions c G D S W) s.mem s'.mem
  blks : WBlkMem c G D S W s'.mem b

theorem WOpsInv.refl {c : Core} {G : Nat} {D S W : BitVec 32} {s : State} {b : WBlks}
    (hb : WBlkMem c G D S W s.mem b) : WOpsInv c G D S W s b s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, hb⟩

theorem WOpsInv.trans {c : Core} {G : Nat} {D S W : BitVec 32} {s s₁ s₂ : State} {b b' : WBlks}
    (h₁ : WOpsInv c G D S W s b s₁) (h₂ : WOpsInv c G D S W s₁ b' s₂) : WOpsInv c G D S W s b' s₂ :=
  ⟨fun x h9 h10 => by rw [h₂.regs x h9 h10, h₁.regs x h9 h10], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr],
    by rw [h₂.sp, h₁.sp], h₁.frame.trans h₂.frame, h₂.blks⟩

/-- The memory after an operation's words, as blocks. -/
theorem wblkMem_over {c : Core} {G : Nat} {D S W : BitVec 32} {wr : List Region} {m : Mem} {b : WBlks}
    (h : WLay c G D S W wr) (hb : WBlkMem c G D S W m b) {x : WBlk} (hx : x.ok G = true) (v : List Byte)
    (f : Nat → Byte) (hv : (List.range c.bs).map f = v) :
    WBlkMem c G D S W (over m (waddr c D S W x) (4 * c.bw) f) (wset b x v) := by
  have hfit : c.bs ≤ 2 ^ 64 := by have := h.fit .scr; simp only [WArr.len] at this; omega_using [this]
  intro z hz
  by_cases e : z = x
  · subst e
    rw [wset_self, ← hv]
    exact bytesAt_over_self m _ f hfit
  · rw [wset_of_ne _ _ e, ← hb z hz]
    exact bytesAt_over_other m f (h.disjoint hx hz (Ne.symm e)) hfit

theorem wframe_over {c : Core} {G : Nat} {D S W : BitVec 32} (m : Mem) {x : WBlk} (hx : x.ok G = true)
    (f : Nat → Byte) : Frame (wblkRegions c G D S W) m (over m (waddr c D S W x) (4 * c.bw) f) := by
  obtain ⟨r, hr, hs⟩ := WLay.sub (c := c) (D := D) (S := S) (W := W) hx
  exact (VG.Proof.Modes.over_frame m _ _ f).sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact ⟨r, hr, hs⟩

theorem wbm_get {c : Core} {G : Nat} {D S W : BitVec 32} {m : Mem} {b : WBlks} (hb : WBlkMem c G D S W m b)
    {z : WBlk} (hz : z.ok G = true) {i : Nat} (hi : i < c.bs) :
    (b z).getD i 0 = m (waddr c D S W z + BitVec.ofNat 64 i) := by
  rw [← hb z hz, getD_bytesAt _ _ hi]

theorem wbm_len {c : Core} {G : Nat} {D S W : BitVec 32} {m : Mem} {b : WBlks} (hb : WBlkMem c G D S W m b)
    {x : WBlk} (hx : x.ok G = true) : (b x).length = c.bs := by
  rw [← hb x hx]; simp [bytesAt]

/-- The code of one operation. -/
theorem wopCode_wp {c : Core} {G : Nat} {D S W : BitVec 32} {s : State} (h : WLay c G D S W s.wr)
    (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = S) (h12 : s.gpr .r12 = W) {b : WBlks}
    (hb : WBlkMem c G D S W s.mem b) {op : WOp} (hok : wopOk c.bs G op = true) :
    WP isa (.block (c.wopCode op)) s (WOpsInv c G D S W s (wrunOp op b)) := by
  obtain hfit : c.bs ≤ 2 ^ 64 := by have := h.fit .scr; simp only [WArr.len] at this; omega_using [this]
  cases op with
  | inc =>
    obtain hbs : c.bs = 16 := by simpa [wopOk] using hok
    have ho : WBlk.ok G .o = true := rfl
    let P := waddr c D S W .o
    obtain w : Covers [⟨P, 16⟩] s.wr := by have := h.writable ho; rw [hbs] at this; exact this
    have inW (d n : Nat) (hd : d + n ≤ 16) : InRegions s.wr (P + BitVec.ofNat 64 d) n :=
      w _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P hd (by omega_using [hd])⟩
    obtain ⟨s', he, hg, hsp, hm, hrd, hwr⟩ := Counter.incr_ok s (base := .r8) (off := oOff)
      (by decide) (by decide) (by decide) (Q := P)
      (fun d hd => h.byte_addr h6 h8 h12 ho (by rw [hbs]; exact hd))
      (fun d n hd => by
        obtain ⟨r, hr, hc⟩ := inW d n hd
        exact ⟨r, List.mem_append_right _ hr, hc⟩) inW
    obtain hf := Counter.incMem_frame s.mem P
    refine WP.of_runBlock ⟨s', he, hg, hrd, hwr, hsp, ?_, ?_⟩
    · rw [hm]
      obtain ⟨r, hr, hs⟩ := WLay.sub (c := c) (D := D) (S := S) (W := W) ho
      exact hf.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨r, hr, by rw [hbs] at hs; exact hs⟩
    · intro x hx
      rw [hm]
      by_cases e : x = .o
      · subst e
        show bytesAt (Counter.incMem s.mem P) P c.bs = Spec.Ctr.inc (b .o)
        rw [hbs, Counter.incMem_bytes, ← hb .o ho, hbs]
      · show bytesAt (Counter.incMem s.mem P) (waddr c D S W x) c.bs = wset b .o _ x
        rw [wset_of_ne _ _ e, ← hb x hx]
        refine VG.Proof.Modes.bytesAt_frame hf (fun r hr => ?_) hfit
        simp only [List.mem_singleton] at hr; subst hr
        have := h.disjoint hx ho e
        rw [hbs] at this ⊢; exact this
  | copy x y =>
    obtain ⟨hxy, hx, hy⟩ : x ≠ y ∧ x.ok G = true ∧ y.ok G = true := by
      simpa [wopOk, and_assoc] using hok
    refine WP.mono (copyN_wp (h.npre rfl h6 h8 h12 hx hy hxy)) fun s' hi => ⟨hi.regs, hi.rd, hi.wr, hi.sp, ?_, ?_⟩
    · rw [hi.mem]; exact wframe_over _ hx _
    · rw [hi.mem]
      refine wblkMem_over h hb hx _ _ ?_
      rw [← hb y hy]; rfl
  | xor x y =>
    obtain ⟨hxy, hx, hy⟩ : x ≠ y ∧ x.ok G = true ∧ y.ok G = true := by
      simpa [wopOk, and_assoc] using hok
    refine WP.mono (xorN_wp (h.npre rfl h6 h8 h12 hx hy hxy)) fun s' hi => ⟨hi.regs, hi.rd, hi.wr, hi.sp, ?_, ?_⟩
    · rw [hi.mem]; exact wframe_over _ hx _
    · rw [hi.mem]
      refine wblkMem_over h hb hx _ _ ?_
      show _ = Spec.Cbc.xor (b x) (b y)
      have lx := wbm_len hb hx
      have ly := wbm_len hb hy
      apply List.ext_getElem
      · simp [Spec.Cbc.xor, lx, ly]
      · intro i h₁ h₂
        simp only [List.length_map, List.length_range] at h₁
        obtain ex : ∀ (z : WBlk) (_ : z.ok G = true) (hz : i < (b z).length),
            (b z)[i] = s.mem (waddr c D S W z + BitVec.ofNat 64 i) :=
          fun z hk hz => by rw [List.getElem_eq_getD 0, wbm_get hb hk h₁]
        simp only [List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
        rw [ex x hx, ex y hy]

/-- The code of a list of operations. -/
theorem wopsCode_wp {c : Core} {G : Nat} {D S W : BitVec 32} {s : State} (h : WLay c G D S W s.wr)
    (h6 : s.gpr .r6 = D) (h8 : s.gpr .r8 = S) (h12 : s.gpr .r12 = W) {b : WBlks}
    (hb : WBlkMem c G D S W s.mem b) {ops : List WOp} (hok : ops.all (wopOk c.bs G) = true) :
    WP isa (.block (c.wopsCode ops)) s (WOpsInv c G D S W s (wrunOps ops b)) := by
  induction ops generalizing s b with
  | nil => exact WP.block_nil (WOpsInv.refl hb)
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [Core.wopsCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (wopCode_wp h h6 h8 h12 hb hok.1) fun s₁ h₁ => ?_
    obtain h6' : s₁.gpr .r6 = D := by rw [h₁.regs _ (by decide) (by decide), h6]
    obtain h8' : s₁.gpr .r8 = S := by rw [h₁.regs _ (by decide) (by decide), h8]
    obtain h12' : s₁.gpr .r12 = W := by rw [h₁.regs _ (by decide) (by decide), h12]
    exact WP.mono (ih (h₁.wr ▸ h) h6' h8' h12' h₁.blks hok.2) fun s₂ h₂ => h₁.trans h₂

end VG.Proof.Modes.Arm
