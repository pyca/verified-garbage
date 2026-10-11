import VerifiedGarbage.Proof.Modes.Arm.Words
import VerifiedGarbage.Impl.Modes.Arm.Seq
import VerifiedGarbage.Spec.Cbc

/-!
# A mode's block operations on ARMv7, and what they compute

A mode (`Impl.Modes.Arm.Mode`) works on three blocks: the data block `D` (at
`r6`), the chaining block `O` and the spare block `T` (in the scratch buffer,
at `r8`). `Blks` holds their contents, `Op.run` is what an operation does to
them (a copy, or `Spec.Cbc.xor`), and `Mode.step` is a whole block's work:
the operations before the call, the cipher applied to the call's block, and
the operations after it.

`opsCode_wp`: the code of a list of operations (`Core.opsCode`) leaves the
three blocks as `runOps` says, changing only them and `r9`, `r10` (`BlkMem`,
with the blocks where `Lay` puts them).
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (over over_sep over_at)

/-- The contents of the data block, the chaining block and the spare block. -/
structure Blks where
  d : List Byte
  o : List Byte
  t : List Byte

def Blks.get (b : Blks) : Blk → List Byte
  | .d => b.d
  | .o => b.o
  | .t => b.t

def Blks.set (b : Blks) : Blk → List Byte → Blks
  | .d, v => { b with d := v }
  | .o, v => { b with o := v }
  | .t, v => { b with t := v }

@[simp] theorem Blks.get_set_self (b : Blks) (x : Blk) (v : List Byte) : (b.set x v).get x = v := by
  cases x <;> rfl

@[simp] theorem Blks.get_set_of_ne (b : Blks) {x y : Blk} (v : List Byte) (h : y ≠ x) :
    (b.set x v).get y = b.get y := by
  cases x <;> cases y <;> first | rfl | exact absurd rfl h

/-- What an operation does to the blocks. -/
def runOp : Op → Blks → Blks
  | .copy x y, b => b.set x (b.get y)
  | .xor x y, b => b.set x (Spec.Cbc.xor (b.get x) (b.get y))

/-- The operations, in order. -/
def runOps (ops : List Op) (b : Blks) : Blks := ops.foldl (fun b op => runOp op b) b

/-- One block's work: the operations before the call, the cipher on the
call's block, and the operations after it. -/
def stepOf (M : Mode) (ciph : Spec.Cbc.Cipher) (b : Blks) : Blks :=
  let b₁ := runOps M.pre b
  runOps M.post (b₁.set M.tgt (ciph (b₁.get M.tgt)))

/-- An operation on two different blocks. -/
def opOk : Op → Bool
  | .copy x y => x != y
  | .xor x y => x != y

/-! ## Where the blocks are -/

/-- The address of each block, with the data block at `Dp` and the scratch
buffer at `S`. -/
def addrOf (c : Core) (Dp S : BitVec 32) : Blk → Addr
  | .d => State.addr Dp
  | .o => State.addr S + BitVec.ofNat 64 oOff
  | .t => State.addr S + BitVec.ofNat 64 (oOff + c.bs)

/-- The blocks' layout: the data block at `Dp` and the chaining and spare
blocks of the scratch buffer at `S`, in reach, writable (in `wr`) and
apart. -/
structure Lay (c : Core) (Dp S : BitVec 32) (wr : List Region) : Prop where
  bw : 0 < c.bw
  off : oOff + 2 * c.bs ≤ 4096
  fD : Dp.toNat + c.bs ≤ 2 ^ 32
  fS : S.toNat + oOff + 2 * c.bs ≤ 2 ^ 32
  wD : Covers [⟨State.addr Dp, c.bs⟩] wr
  wS : Covers [⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩] wr
  sep : Region.Disjoint ⟨State.addr Dp, c.bs⟩ ⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩

/-- The three blocks' contents in memory. -/
def BlkMem (c : Core) (Dp S : BitVec 32) (m : Mem) (b : Blks) : Prop :=
  ∀ x, bytesAt m (addrOf c Dp S x) c.bs = b.get x

/-- The regions of the blocks. -/
abbrev blkRegions (c : Core) (Dp S : BitVec 32) : List Region :=
  [⟨State.addr Dp, c.bs⟩, ⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩]

namespace Lay

variable {c : Core} {Dp S : BitVec 32} {wr : List Region} (h : Lay c Dp S wr)
include h

omit h in
theorem bs_eq : c.bs = 4 * c.bw := rfl

omit h in
/-- The block of each `x`, within the regions of the blocks. -/
theorem sub (x : Blk) : ∃ r ∈ blkRegions c Dp S, Region.Sub ⟨addrOf c Dp S x, c.bs⟩ r := by
  cases x
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩, by simp, Region.sub_prefix (by omega)⟩
  · refine ⟨⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩, by simp, ?_⟩
    show Region.Sub ⟨State.addr S + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ _
    rw [← VG.Offset.add_add]; exact VG.Offset.sub_base _ (by omega)

theorem writable (x : Blk) : Covers [⟨addrOf c Dp S x, c.bs⟩] wr := by
  cases x
  · exact h.wD
  · refine Covers.trans (Covers.of_sub fun r hr => ?_) h.wS
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, 0, by simp [addrOf], by simp; omega⟩
  · refine Covers.trans (Covers.of_sub fun r hr => ?_) h.wS
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, c.bs, by simp [addrOf, VG.Offset.add_add], by simp; omega⟩

theorem disjoint {x y : Blk} (hxy : x ≠ y) :
    Region.Disjoint ⟨addrOf c Dp S x, c.bs⟩ ⟨addrOf c Dp S y, c.bs⟩ := by
  have hS : S.toNat + oOff + 2 * c.bs ≤ 2 ^ 32 := h.fS
  have ot : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 oOff, c.bs⟩
      ⟨State.addr S + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ :=
    VG.Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dO : Region.Disjoint ⟨State.addr Dp, c.bs⟩ ⟨State.addr S + BitVec.ofNat 64 oOff, c.bs⟩ :=
    h.sep.sub_right (Region.sub_prefix (by omega))
  have dT : Region.Disjoint ⟨State.addr Dp, c.bs⟩ ⟨State.addr S + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ :=
    h.sep.sub_right (by rw [← VG.Offset.add_add]; exact VG.Offset.sub_base _ (by omega))
  cases x <;> cases y <;> first | exact absurd rfl hxy | skip
  · exact dO
  · exact dT
  · exact dO.symm
  · exact ot
  · exact dT.symm
  · exact ot.symm

omit h in
/-- The base register and offset of block `x` give its address. -/
theorem base_addr {s : State} (h6 : s.gpr .r6 = Dp) (h8 : s.gpr .r8 = S) (x : Blk) :
    State.addr (s.gpr (c.base x).1) + BitVec.ofNat 64 (c.base x).2 = addrOf c Dp S x := by
  cases x
  · simp [Core.base, addrOf, h6]
  · simp [Core.base, addrOf, h8]
  · simp [Core.base, addrOf, h8]

theorem base_fit {s : State} (h6 : s.gpr .r6 = Dp) (h8 : s.gpr .r8 = S) (x : Blk) :
    (s.gpr (c.base x).1).toNat + (c.base x).2 + 4 * c.bw ≤ 2 ^ 32 := by
  have := h.fD; have := h.fS
  cases x <;> simp [Core.base, h6, h8, Core.bs] at * <;> omega

theorem base_off (x : Blk) : (c.base x).2 + 4 * c.bw ≤ 4096 := by
  have := h.off
  cases x <;> simp [Core.base, Core.bs] at * <;> omega

end Lay

theorem base_ne9 (c : Core) (x : Blk) : (c.base x).1 ≠ .r9 := by cases x <;> simp [Core.base]
theorem base_ne10 (c : Core) (x : Blk) : (c.base x).1 ≠ .r10 := by cases x <;> simp [Core.base]

/-! ## The bytes of `over` -/

theorem bytesAt_over_self (m : Mem) (P : Addr) {n : Nat} (f : Nat → Byte) (hn : n ≤ 2 ^ 64) :
    bytesAt (over m P n f) P n = (List.range n).map f := by
  apply List.map_congr_left
  intro i hi
  exact over_at (List.mem_range.mp hi) hn

theorem bytesAt_over_other (m : Mem) {P Q : Addr} {n k : Nat} (f : Nat → Byte) (hd : Region.Disjoint ⟨P, n⟩ ⟨Q, k⟩)
    (hk : k ≤ 2 ^ 64) : bytesAt (over m P n f) Q k = bytesAt m Q k := by
  apply List.map_congr_left
  intro i hi
  exact over_sep hd (List.mem_range.mp hi) hk

theorem getD_bytesAt (m : Mem) (Q : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m Q n).getD i 0 = m (Q + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-! ## One operation, and a list of them -/

/-- What the code of operations from `s` keeps. -/
structure OpsInv (c : Core) (Dp S : BitVec 32) (s : State) (b : Blks) (s' : State) : Prop where
  regs : ∀ x, x ≠ .r9 → x ≠ .r10 → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (blkRegions c Dp S) s.mem s'.mem
  blks : BlkMem c Dp S s'.mem b

theorem OpsInv.refl {c : Core} {Dp S : BitVec 32} {s : State} {b : Blks} (hb : BlkMem c Dp S s.mem b) :
    OpsInv c Dp S s b s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, hb⟩

theorem OpsInv.trans {c : Core} {Dp S : BitVec 32} {s s₁ s₂ : State} {b b' : Blks}
    (h₁ : OpsInv c Dp S s b s₁) (h₂ : OpsInv c Dp S s₁ b' s₂) : OpsInv c Dp S s b' s₂ :=
  ⟨fun x h9 h10 => by rw [h₂.regs x h9 h10, h₁.regs x h9 h10], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr],
    by rw [h₂.sp, h₁.sp], h₁.frame.trans h₂.frame, h₂.blks⟩

/-- The NPre of an operation on blocks `x ← y`. -/
theorem Lay.npre {c : Core} {Dp S : BitVec 32} {s : State} (h : Lay c Dp S s.wr) (h6 : s.gpr .r6 = Dp)
    (h8 : s.gpr .r8 = S) {x y : Blk} (hxy : x ≠ y) :
    NPre c.bw s (c.base x).1 (c.base y).1 (c.base x).2 (c.base y).2 (addrOf c Dp S x) (addrOf c Dp S y) :=
  { hP := Lay.base_addr h6 h8 x
    hQ := Lay.base_addr h6 h8 y
    fP := h.base_fit h6 h8 x
    fQ := h.base_fit h6 h8 y
    oP := h.base_off x
    oQ := h.base_off y
    d9 := base_ne9 c x
    d10 := base_ne10 c x
    s9 := base_ne9 c y
    s10 := base_ne10 c y
    wP := h.writable x
    rQ := Covers.right (h.writable y)
    sep := h.disjoint hxy }

/-- The memory after an operation's words, as blocks. -/
theorem blkMem_over {c : Core} {Dp S : BitVec 32} {wr : List Region} {m : Mem} {b : Blks} (h : Lay c Dp S wr)
    (hb : BlkMem c Dp S m b) (x : Blk) (v : List Byte) (f : Nat → Byte) (hv : (List.range c.bs).map f = v) :
    BlkMem c Dp S (over m (addrOf c Dp S x) (4 * c.bw) f) (b.set x v) := by
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Blks.get_set_self, ← hv, ← bytesAt_over_self m _ f (by have := h.fS; unfold Core.bs at *; omega)]
    rfl
  · rw [Blks.get_set_of_ne _ _ hz, ← hb z]
    exact bytesAt_over_other m f (h.disjoint (Ne.symm hz)) (by have := h.fS; unfold Core.bs at *; omega)

theorem frame_over {c : Core} {Dp S : BitVec 32} (m : Mem) (x : Blk) (f : Nat → Byte) :
    Frame (blkRegions c Dp S) m (over m (addrOf c Dp S x) (4 * c.bw) f) := by
  obtain ⟨r, hr, hs⟩ := Lay.sub (c := c) (Dp := Dp) (S := S) x
  exact (VG.Proof.Modes.over_frame m _ _ f).sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact ⟨r, hr, hs⟩

/-- The code of one operation. -/
theorem opCode_wp {c : Core} {Dp S : BitVec 32} {s : State} (h : Lay c Dp S s.wr) (h6 : s.gpr .r6 = Dp)
    (h8 : s.gpr .r8 = S) {b : Blks} (hb : BlkMem c Dp S s.mem b) {op : Op} (hok : opOk op = true)
    (hl : ∀ x, (b.get x).length = c.bs) :
    WP isa (.block (c.opCode op)) s (OpsInv c Dp S s (runOp op b)) := by
  have hfit : c.bs ≤ 2 ^ 64 := by have := h.fS; omega
  cases op with
  | copy x y =>
    have hxy : x ≠ y := by simpa [opOk] using hok
    refine WP.mono (copyN_wp (h.npre h6 h8 hxy)) fun s' hi => ⟨hi.regs, hi.rd, hi.wr, hi.sp, ?_, ?_⟩
    · rw [hi.mem]; exact frame_over _ x _
    · rw [hi.mem]
      refine blkMem_over h hb x _ _ ?_
      rw [← hb y]; rfl
  | xor x y =>
    have hxy : x ≠ y := by simpa [opOk] using hok
    refine WP.mono (xorN_wp (h.npre h6 h8 hxy)) fun s' hi => ⟨hi.regs, hi.rd, hi.wr, hi.sp, ?_, ?_⟩
    · rw [hi.mem]; exact frame_over _ x _
    · rw [hi.mem]
      refine blkMem_over h hb x _ _ ?_
      show _ = Spec.Cbc.xor (b.get x) (b.get y)
      apply List.ext_getElem
      · simp [Spec.Cbc.xor, hl]
      · intro i h₁ h₂
        simp only [List.length_map, List.length_range] at h₁
        have ex : ∀ z (hz : i < (b.get z).length), (b.get z)[i] = s.mem (addrOf c Dp S z + BitVec.ofNat 64 i) :=
          fun z hz => by rw [List.getElem_eq_getD 0, ← hb z, getD_bytesAt _ _ h₁]
        simp only [List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
        rw [ex x, ex y]

theorem runOp_length {op : Op} {b : Blks} {L : Nat} (hl : ∀ x, (b.get x).length = L) :
    ∀ x, ((runOp op b).get x).length = L := by
  intro z
  cases op with
  | copy x y =>
    by_cases hz : z = x
    · subst hz; simp [runOp, hl]
    · simp [runOp, Blks.get_set_of_ne _ _ hz, hl]
  | xor x y =>
    by_cases hz : z = x
    · subst hz; simp [runOp, Spec.Cbc.xor, hl]
    · simp [runOp, Blks.get_set_of_ne _ _ hz, hl]

theorem runOps_length {ops : List Op} {b : Blks} {L : Nat} (hl : ∀ x, (b.get x).length = L) :
    ∀ x, ((runOps ops b).get x).length = L := by
  induction ops generalizing b with
  | nil => exact hl
  | cons op ops ih => exact ih (runOp_length hl)

/-- The code of a list of operations. -/
theorem opsCode_wp {c : Core} {Dp S : BitVec 32} {s : State} (h : Lay c Dp S s.wr) (h6 : s.gpr .r6 = Dp)
    (h8 : s.gpr .r8 = S) {b : Blks} (hb : BlkMem c Dp S s.mem b) {ops : List Op}
    (hok : ops.all opOk = true) (hl : ∀ x, (b.get x).length = c.bs) :
    WP isa (.block (c.opsCode ops)) s (OpsInv c Dp S s (runOps ops b)) := by
  induction ops generalizing s b with
  | nil => exact WP.block_nil (OpsInv.refl hb)
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [Core.opsCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (opCode_wp h h6 h8 hb hok.1 hl) fun s₁ h₁ => ?_
    have h6' : s₁.gpr .r6 = Dp := by rw [h₁.regs _ (by decide) (by decide), h6]
    have h8' : s₁.gpr .r8 = S := by rw [h₁.regs _ (by decide) (by decide), h8]
    exact WP.mono (ih (h₁.wr ▸ h) h6' h8' h₁.blks hok.2 (runOp_length hl)) fun s₂ h₂ => h₁.trans h₂

end VG.Proof.Modes.Arm
