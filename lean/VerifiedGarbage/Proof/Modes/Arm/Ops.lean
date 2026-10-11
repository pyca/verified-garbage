import VerifiedGarbage.Proof.Modes.Arm.Words
import VerifiedGarbage.Impl.Modes.Arm.Seq
import VerifiedGarbage.Spec.Cbc

/-!
# A mode's block operations on ARMv7, and what they compute

A mode (`Impl.Modes.Arm.Mode`) works on three blocks: the data block `D` (at
`r6`), the chaining block `O` and the spare block `T` (in the scratch buffer,
at `r8`). `D` holds one of the data's elements, `ds` bytes: a block, or a
single byte (CFB8). `Blks` holds their contents, `runOp` is what an
operation does to them (a copy, `Spec.Cbc.xor`, the XOR of first bytes or a
shift by a byte), and `stepOf` is a whole element's work: the operations
before the call, the cipher applied to the call's block, and the operations
after it.

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

/-- The first byte of `y` XORed into the first byte of `l`. -/
def xorHead (l y : List Byte) : List Byte :=
  match l with
  | [] => []
  | a :: as => (a ^^^ y.headD 0) :: as

/-- What an operation does to the blocks. -/
def runOp : Op → Blks → Blks
  | .copy x y, b => b.set x (b.get y)
  | .xor x y, b => b.set x (Spec.Cbc.xor (b.get x) (b.get y))
  | .xorB x y, b => b.set x (xorHead (b.get x) (b.get y))
  | .shift x y, b => b.set x ((b.get x).tail ++ [(b.get y).headD 0])

/-- The operations, in order. -/
def runOps (ops : List Op) (b : Blks) : Blks := ops.foldl (fun b op => runOp op b) b

/-- One element's work: the operations before the call, the cipher on the
call's block, and the operations after it. -/
def stepOf (M : Mode) (ciph : Spec.Cbc.Cipher) (b : Blks) : Blks :=
  let b₁ := runOps M.pre b
  runOps M.post (b₁.set M.tgt (ciph (b₁.get M.tgt)))

/-- An operation on two different blocks, and, when the data comes a byte
at a time (`byte`), no whole-block operation on the data block, and no shift
of it. -/
def opOk (byte : Bool) : Op → Bool
  | .copy x y => x != y && (!byte || (x != .d && y != .d))
  | .xor x y => x != y && (!byte || (x != .d && y != .d))
  | .xorB x y => x != y
  | .shift x y => x != y && x != .d

/-! ## Where the blocks are -/

/-- The address of each block, with the data block at `Dp` and the scratch
buffer at `S`. -/
def addrOf (c : Core) (Dp S : BitVec 32) : Blk → Addr
  | .d => State.addr Dp
  | .o => State.addr S + BitVec.ofNat 64 oOff
  | .t => State.addr S + BitVec.ofNat 64 (oOff + c.bs)

/-- The size of each block: the data block holds `ds` bytes. -/
def sz (c : Core) (ds : Nat) : Blk → Nat
  | .d => ds
  | _ => c.bs

/-- The blocks' layout: the data block of `ds` bytes at `Dp` and the
chaining and spare blocks of the scratch buffer at `S`, in reach, writable
(in `wr`) and apart. -/
structure Lay (c : Core) (ds : Nat) (Dp S : BitVec 32) (wr : List Region) : Prop where
  bw : 0 < c.bw
  off : oOff + 2 * c.bs ≤ 4096
  ds_pos : 0 < ds
  ds_le : ds ≤ c.bs
  fD : Dp.toNat + ds ≤ 2 ^ 32
  fS : S.toNat + oOff + 2 * c.bs ≤ 2 ^ 32
  wD : Covers [⟨State.addr Dp, ds⟩] wr
  wS : Covers [⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩] wr
  sep : Region.Disjoint ⟨State.addr Dp, ds⟩ ⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩

/-- The three blocks' contents in memory. -/
def BlkMem (c : Core) (ds : Nat) (Dp S : BitVec 32) (m : Mem) (b : Blks) : Prop :=
  ∀ x, bytesAt m (addrOf c Dp S x) (sz c ds x) = b.get x

/-- The regions of the blocks. -/
abbrev blkRegions (c : Core) (ds : Nat) (Dp S : BitVec 32) : List Region :=
  [⟨State.addr Dp, ds⟩, ⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩]

namespace Lay

variable {c : Core} {ds : Nat} {Dp S : BitVec 32} {wr : List Region} (h : Lay c ds Dp S wr)
include h

omit h in
theorem bs_eq : c.bs = 4 * c.bw := rfl

omit h in
/-- The block of each `x`, within the regions of the blocks. -/
theorem sub (x : Blk) : ∃ r ∈ blkRegions c ds Dp S, Region.Sub ⟨addrOf c Dp S x, sz c ds x⟩ r := by
  cases x
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩, by simp, Region.sub_prefix (by simp [sz]; omega)⟩
  · refine ⟨⟨State.addr S + BitVec.ofNat 64 oOff, 2 * c.bs⟩, by simp, ?_⟩
    show Region.Sub ⟨State.addr S + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ _
    rw [← VG.Offset.add_add]; exact VG.Offset.sub_base _ (by omega)

theorem sz_pos (x : Blk) : 0 < sz c ds x := by
  have := h.ds_pos; have := h.bw; cases x <;> simp [sz, Core.bs] <;> omega

theorem sz_le (x : Blk) : sz c ds x ≤ c.bs := by
  have := h.ds_le; cases x <;> simp [sz]; omega

theorem writable (x : Blk) : Covers [⟨addrOf c Dp S x, sz c ds x⟩] wr := by
  cases x
  · exact h.wD
  · refine Covers.trans (Covers.of_sub fun r hr => ?_) h.wS
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, 0, by simp [addrOf], by simp [sz]; omega⟩
  · refine Covers.trans (Covers.of_sub fun r hr => ?_) h.wS
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, c.bs, by simp [addrOf, VG.Offset.add_add], by simp [sz]; omega⟩

theorem disjoint {x y : Blk} (hxy : x ≠ y) :
    Region.Disjoint ⟨addrOf c Dp S x, sz c ds x⟩ ⟨addrOf c Dp S y, sz c ds y⟩ := by
  have hS : S.toNat + oOff + 2 * c.bs ≤ 2 ^ 32 := h.fS
  have ot : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 oOff, c.bs⟩
      ⟨State.addr S + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ :=
    VG.Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dO : Region.Disjoint ⟨State.addr Dp, ds⟩ ⟨State.addr S + BitVec.ofNat 64 oOff, c.bs⟩ :=
    h.sep.sub_right (Region.sub_prefix (by omega))
  have dT : Region.Disjoint ⟨State.addr Dp, ds⟩ ⟨State.addr S + BitVec.ofNat 64 (oOff + c.bs), c.bs⟩ :=
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
    (s.gpr (c.base x).1).toNat + (c.base x).2 + sz c ds x ≤ 2 ^ 32 := by
  have := h.fD; have := h.fS
  cases x <;> simp [Core.base, h6, h8, sz] at * <;> omega

theorem base_off (x : Blk) : (c.base x).2 + c.bs ≤ 4096 := by
  have := h.off
  have := h.bw
  have : c.bs = 4 * c.bw := rfl
  cases x <;> simp [Core.base] at * <;> omega

/-- Byte `k` of block `x`, through its base register. -/
theorem byte_addr {s : State} (h6 : s.gpr .r6 = Dp) (h8 : s.gpr .r8 = S) (x : Blk) {k : Nat}
    (hk : k < sz c ds x) :
    State.addr (s.gpr (c.base x).1 + BitVec.ofNat 32 ((c.base x).2 + k)) = addrOf c Dp S x + BitVec.ofNat 64 k := by
  have := h.base_fit h6 h8 x
  rw [addr_add (by omega), ← VG.Offset.add_add, base_addr h6 h8]

theorem byte_in {rs : List Region} {x : Blk} (hc : Covers [⟨addrOf c Dp S x, sz c ds x⟩] rs) {k : Nat}
    (hk : k < sz c ds x) : InRegions rs (addrOf c Dp S x + BitVec.ofNat 64 k) 1 :=
  hc _ _ ⟨_, List.mem_singleton_self _, VG.Offset.contains_base _ (by omega)
    (by have := h.sz_le x; have := h.off; omega)⟩

end Lay

theorem base_ne9 (c : Core) (x : Blk) : (c.base x).1 ≠ .r9 := by cases x <;> simp [Core.base]
theorem base_ne10 (c : Core) (x : Blk) : (c.base x).1 ≠ .r10 := by cases x <;> simp [Core.base]

/-! ## The bytes of `over` -/

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

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

/-- A byte stored at `P + j` extends `over` of the `j` bytes before it. -/
theorem writeW_over_step {m : Mem} {P : Addr} {j : Nat} {f : Nat → Byte} (hj : j + 1 ≤ 2 ^ 64) :
    (over m P j f).writeW (P + BitVec.ofNat 64 j) (f j) = over m P (j + 1) f := by
  funext x
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  by_cases hx : (x - (P + BitVec.ofNat 64 j)).toNat < 8 / 8
  · rw [ite_eq_left (show (x - (P + BitVec.ofNat 64 j)).toNat < 8 / 8 from hx)]
    have e : (x - P).toNat = j := by bv_omega
    have z : (x - (P + BitVec.ofNat 64 j)).toNat = 0 := by omega
    simp only [over]; rw [ite_eq_left (show (x - P).toNat < j + 1 by omega), e, z]
    simp
  · rw [ite_eq_right (show ¬ (x - (P + BitVec.ofNat 64 j)).toNat < 8 / 8 from hx)]
    simp only [over]
    by_cases h1 : (x - P).toNat < j
    · rw [ite_eq_left h1, ite_eq_left (show (x - P).toNat < j + 1 by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (x - P).toNat < j + 1 by bv_omega)]

/-- The bytes of a block after `over` of its first `k` bytes. -/
theorem bytesAt_over_prefix (m : Mem) (P : Addr) {n k : Nat} (f : Nat → Byte) (hn : n ≤ 2 ^ 64) :
    bytesAt (over m P k f) P n = (List.range n).map fun i => if i < k then f i else m (P + BitVec.ofNat 64 i) := by
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  simp only [over]; rw [VG.Proof.Modes.off_self P (by omega)]

/-! ## One operation, and a list of them -/

/-- What the code of operations from `s` keeps. -/
structure OpsInv (c : Core) (ds : Nat) (Dp S : BitVec 32) (s : State) (b : Blks) (s' : State) : Prop where
  regs : ∀ x, x ≠ .r9 → x ≠ .r10 → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (blkRegions c ds Dp S) s.mem s'.mem
  blks : BlkMem c ds Dp S s'.mem b

theorem OpsInv.refl {c : Core} {ds : Nat} {Dp S : BitVec 32} {s : State} {b : Blks}
    (hb : BlkMem c ds Dp S s.mem b) : OpsInv c ds Dp S s b s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, hb⟩

theorem OpsInv.trans {c : Core} {ds : Nat} {Dp S : BitVec 32} {s s₁ s₂ : State} {b b' : Blks}
    (h₁ : OpsInv c ds Dp S s b s₁) (h₂ : OpsInv c ds Dp S s₁ b' s₂) : OpsInv c ds Dp S s b' s₂ :=
  ⟨fun x h9 h10 => by rw [h₂.regs x h9 h10, h₁.regs x h9 h10], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr],
    by rw [h₂.sp, h₁.sp], h₁.frame.trans h₂.frame, h₂.blks⟩

/-- The NPre of a whole-block operation on blocks `x ← y` of `c.bs` bytes. -/
theorem Lay.npre {c : Core} {ds : Nat} {Dp S : BitVec 32} {s : State} (h : Lay c ds Dp S s.wr)
    (h6 : s.gpr .r6 = Dp) (h8 : s.gpr .r8 = S) {x y : Blk} (hxy : x ≠ y) (hx : sz c ds x = c.bs)
    (hy : sz c ds y = c.bs) :
    NPre c.bw s (c.base x).1 (c.base y).1 (c.base x).2 (c.base y).2 (addrOf c Dp S x) (addrOf c Dp S y) :=
  { hP := Lay.base_addr h6 h8 x
    hQ := Lay.base_addr h6 h8 y
    fP := by have := h.base_fit h6 h8 x; rw [hx] at this; exact this
    fQ := by have := h.base_fit h6 h8 y; rw [hy] at this; exact this
    oP := h.base_off x
    oQ := h.base_off y
    d9 := base_ne9 c x
    d10 := base_ne10 c x
    s9 := base_ne9 c y
    s10 := base_ne10 c y
    wP := by have := h.writable x; rw [hx] at this; exact this
    rQ := by have := Covers.right (rd := s.rd) (h.writable y); rw [hy] at this; exact this
    sep := by have := h.disjoint hxy; rw [hx, hy] at this; exact this }

/-- The memory after an operation's words, as blocks. -/
theorem blkMem_over {c : Core} {ds : Nat} {Dp S : BitVec 32} {wr : List Region} {m : Mem} {b : Blks}
    (h : Lay c ds Dp S wr) (hb : BlkMem c ds Dp S m b) (x : Blk) (v : List Byte) (f : Nat → Byte)
    (hv : (List.range (sz c ds x)).map f = v) {k : Nat} (hk : k = sz c ds x) :
    BlkMem c ds Dp S (over m (addrOf c Dp S x) k f) (b.set x v) := by
  subst hk
  have hfit : ∀ y, sz c ds y ≤ 2 ^ 64 := fun y => by have := h.sz_le y; have := h.fS; omega
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Blks.get_set_self, ← hv, ← bytesAt_over_self m _ f (hfit _)]
  · rw [Blks.get_set_of_ne _ _ hz, ← hb z]
    exact bytesAt_over_other m f (h.disjoint (Ne.symm hz)) (hfit _)

theorem frame_over {c : Core} {ds : Nat} {Dp S : BitVec 32} (m : Mem) (x : Blk) (f : Nat → Byte) {k : Nat}
    (hk : k ≤ sz c ds x) : Frame (blkRegions c ds Dp S) m (over m (addrOf c Dp S x) k f) := by
  obtain ⟨r, hr, hs⟩ := Lay.sub (c := c) (ds := ds) (Dp := Dp) (S := S) x
  exact (VG.Proof.Modes.over_frame m _ _ f).sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact ⟨r, hr, fun a ha => hs a (Region.sub_prefix hk a ha)⟩

theorem bm_get {c : Core} {ds : Nat} {Dp S : BitVec 32} {m : Mem} {b : Blks} (hb : BlkMem c ds Dp S m b)
    (z : Blk) {i : Nat} (hi : i < sz c ds z) : (b.get z).getD i 0 = m (addrOf c Dp S z + BitVec.ofNat 64 i) := by
  rw [← hb z, getD_bytesAt _ _ hi]

theorem bm_len {c : Core} {ds : Nat} {Dp S : BitVec 32} {m : Mem} {b : Blks} (hb : BlkMem c ds Dp S m b) :
    ∀ x, (b.get x).length = sz c ds x := fun x => by rw [← hb x]; simp [bytesAt]

/-- The code of one operation. -/
theorem opCode_wp {c : Core} {ds : Nat} {byte : Bool} (hds : byte = false → ds = c.bs) {Dp S : BitVec 32}
    {s : State} (h : Lay c ds Dp S s.wr) (h6 : s.gpr .r6 = Dp) (h8 : s.gpr .r8 = S) {b : Blks}
    (hb : BlkMem c ds Dp S s.mem b) {op : Op} (hok : opOk byte op = true) :
    WP isa (.block (c.opCode op)) s (OpsInv c ds Dp S s (runOp op b)) := by
  have hfit : c.bs ≤ 2 ^ 64 := by have := h.fS; omega
  have hl := bm_len hb
  -- A whole-block operation is on blocks of `c.bs` bytes.
  have whole : ∀ {x y : Blk}, (x != y && (!byte || (x != .d && y != .d))) = true →
      x ≠ y ∧ sz c ds x = c.bs ∧ sz c ds y = c.bs := fun {x y} hxy => by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true'] at hxy
    refine ⟨hxy.1, ?_, ?_⟩ <;> rcases hxy.2 with hb' | hb'
    · cases x <;> simp [sz, hds hb']
    · cases x <;> simp_all [sz]
    · cases y <;> simp [sz, hds hb']
    · cases y <;> simp_all [sz]
  cases op with
  | copy x y =>
    obtain ⟨hxy, hx, hy⟩ := whole hok
    refine WP.mono (copyN_wp (h.npre h6 h8 hxy hx hy)) fun s' hi => ⟨hi.regs, hi.rd, hi.wr, hi.sp, ?_, ?_⟩
    · rw [hi.mem]; exact frame_over _ x _ (by rw [hx]; rfl)
    · rw [hi.mem]
      refine blkMem_over h hb x _ _ ?_ (by rw [hx]; rfl)
      rw [← hb y, hx, hy]; rfl
  | xor x y =>
    obtain ⟨hxy, hx, hy⟩ := whole hok
    refine WP.mono (xorN_wp (h.npre h6 h8 hxy hx hy)) fun s' hi => ⟨hi.regs, hi.rd, hi.wr, hi.sp, ?_, ?_⟩
    · rw [hi.mem]; exact frame_over _ x _ (by rw [hx]; rfl)
    · rw [hi.mem]
      refine blkMem_over h hb x _ _ ?_ (by rw [hx]; rfl)
      show _ = Spec.Cbc.xor (b.get x) (b.get y)
      apply List.ext_getElem
      · simp [Spec.Cbc.xor, hl, hx, hy]
      · intro i h₁ h₂
        simp only [List.length_map, List.length_range] at h₁
        have ex : ∀ z (hz : i < (b.get z).length), (b.get z)[i] = s.mem (addrOf c Dp S z + BitVec.ofNat 64 i) :=
          fun z hz => by rw [List.getElem_eq_getD 0, bm_get hb z (by rw [← hl z]; exact hz)]
        simp only [List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
        rw [ex x, ex y]
  | xorB x y =>
    have hxy : x ≠ y := by simpa [opOk] using hok
    have px := h.sz_pos x
    have py := h.sz_pos y
    have hA := h.byte_addr h6 h8 x px
    have hB := h.byte_addr h6 h8 y py
    simp only [Nat.add_zero, add0] at hA hB
    simp only [Core.opCode]
    refine MdStream.Arm.wp_ldrb (a := addrOf c Dp S x) (by have := h.base_off x; have := h.sz_le x; omega) hA
      (by have := h.byte_in (Covers.right (rd := s.rd) (h.writable x)) px; simpa [add0] using this)
      fun s₁ u₁ => ?_
    refine MdStream.Arm.wp_ldrb (a := addrOf c Dp S y) (by have := h.base_off y; have := h.sz_le y; omega)
      (by rw [u₁.other _ (base_ne9 c y)]; exact hB)
      (by rw [u₁.rd, u₁.wr]; have := h.byte_in (Covers.right (rd := s.rd) (h.writable y)) py; simpa [add0] using this)
      fun s₂ u₂ => ?_
    refine VG.Proof.CmacAes.Arm.wp_eor (MdStream.Arm.op2_reg _ _) fun s₃ u₃ => ?_
    refine MdStream.Arm.wp_strb (a := addrOf c Dp S x) (by have := h.base_off x; have := h.sz_le x; omega)
      (by rw [u₃.other _ (base_ne9 c x), u₂.other _ (base_ne10 c x), u₁.other _ (base_ne9 c x)]; exact hA)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; have := h.byte_in (h.writable x) px; simpa [add0] using this)
      fun s₄ u₄ => WP.block_nil ⟨fun r a b => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.gpr, u₃.other _ a, u₂.other _ b, u₁.other _ a]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]
    -- The memory: `over` of the first byte of `x`.
    all_goals
      have em : s₄.mem = over s.mem (addrOf c Dp S x) 1 fun _ =>
          s.mem (addrOf c Dp S x) ^^^ s.mem (addrOf c Dp S y) := by
        rw [u₄.mem, u₃.gpr, u₃.mem, u₂.other _ (by decide), u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]
        have e := writeW_over_step (m := s.mem) (P := addrOf c Dp S x) (j := 0)
          (f := fun _ => s.mem (addrOf c Dp S x) ^^^ s.mem (addrOf c Dp S y)) (by decide)
        rw [VG.Proof.Modes.over_zero, add0] at e
        rw [← e]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_xor]
    · rw [em]; exact frame_over _ x _ px
    · rw [em]
      have hfx : sz c ds x ≤ 2 ^ 64 := by have := h.sz_le x; have := h.fS; omega
      intro z
      by_cases hz : z = x
      · subst hz
        rw [bytesAt_over_prefix _ _ _ hfx]
        simp only [runOp, Blks.get_set_self]
        rw [← hb z, ← hb y]
        obtain ⟨n, hn⟩ : ∃ n, sz c ds z = n + 1 := ⟨sz c ds z - 1, by omega⟩
        rw [hn, List.range_succ_eq_map, List.map_cons, List.map_map]
        simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, xorHead, add0]
        refine List.cons_eq_cons.mpr ⟨?_, List.map_congr_left fun i _ => by simp⟩
        cases hy : sz c ds y with
        | zero => omega
        | succ k => simp [List.range_succ_eq_map]
      · rw [runOp, Blks.get_set_of_ne _ _ hz, ← hb z]
        exact bytesAt_over_other _ _ ((h.disjoint (Ne.symm hz)).sub_left (Region.sub_prefix px))
          (by have := h.sz_le z; have := h.fS; omega)
  | shift x y =>
    have hxy : x ≠ y := by simp [opOk] at hok; exact hok.1
    have hx : sz c ds x = c.bs := by simp [opOk] at hok; cases x <;> simp_all [sz]
    have px := h.sz_pos x
    have py := h.sz_pos y
    have hfit' : c.bs ≤ 2 ^ 64 := hfit
    have off := h.base_off x
    have offy := h.base_off y
    have ly := h.sz_le y
    let A := addrOf c Dp S x
    let B := addrOf c Dp S y
    let f : Nat → Byte := fun i => if i < c.bs - 1 then s.mem (A + BitVec.ofNat 64 (i + 1)) else s.mem B
    have hwx := h.writable x
    have hwy := h.writable y
    simp only [Core.opCode]
    rw [WP.block_append_iff]
    refine WP.mono (wp_range_flatMap (M := isa) (N := c.bs - 1) (fun j t => (∀ r, r ≠ .r9 → t.gpr r = s.gpr r) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.mem = over s.mem A j f) (fun j t hj hi => ?_) _ (Nat.le_refl _)
        s ⟨fun _ _ => rfl, rfl, rfl, rfl, by rw [VG.Proof.Modes.over_zero]⟩) fun t ⟨g, rd, wr, sp, hm⟩ => ?_
    · obtain ⟨g, rd, wr, sp, hm⟩ := hi
      have h6' : t.gpr .r6 = Dp := by rw [g _ (by decide), h6]
      have h8' : t.gpr .r8 = S := by rw [g _ (by decide), h8]
      refine MdStream.Arm.wp_ldrb (a := A + BitVec.ofNat 64 (j + 1)) (by omega)
        (by rw [Nat.add_assoc]; exact h.byte_addr h6' h8' x (by omega))
        (by rw [rd, wr]; exact h.byte_in (Covers.right (rd := s.rd) hwx) (by omega)) fun t₁ u₁ => ?_
      refine MdStream.Arm.wp_strb (a := A + BitVec.ofNat 64 j) (by omega)
        (by rw [u₁.other _ (base_ne9 c x)]; exact h.byte_addr h6' h8' x (by omega))
        (by rw [u₁.wr, wr]; exact h.byte_in hwx (by omega)) fun t₂ u₂ =>
          WP.block_nil ⟨fun r hr => by rw [u₂.gpr, u₁.other _ hr, g _ hr], by rw [u₂.rd, u₁.rd, rd],
            by rw [u₂.wr, u₁.wr, wr], by rw [u₂.sp, u₁.sp, sp], ?_⟩
      rw [u₂.mem, u₁.gpr, u₁.mem, hm, VG.Proof.Modes.over_out (by
        rw [VG.Proof.Modes.off_self A (by omega)]; omega)]
      rw [show ((s.mem (A + BitVec.ofNat 64 (j + 1))).setWidth 32).setWidth 8 = f j by
        simp only [f, ite_eq_left (show j < c.bs - 1 from hj)]; simp]
      exact writeW_over_step (by omega)
    · have h6' : t.gpr .r6 = Dp := by rw [g _ (by decide), h6]
      have h8' : t.gpr .r8 = S := by rw [g _ (by decide), h8]
      have hB := h.byte_addr h6' h8' y py
      simp only [Nat.add_zero, add0] at hB
      refine MdStream.Arm.wp_ldrb (a := B) (by omega) hB
        (by rw [rd, wr]; have := h.byte_in (Covers.right (rd := s.rd) hwy) py; simpa [add0] using this) fun t₁ u₁ => ?_
      refine MdStream.Arm.wp_strb (a := A + BitVec.ofNat 64 (c.bs - 1)) (by omega)
        (by rw [u₁.other _ (base_ne9 c x)]; exact h.byte_addr h6' h8' x (by omega))
        (by rw [u₁.wr, wr]; exact h.byte_in hwx (by omega)) fun t₂ u₂ => WP.block_nil ?_
      have em : t₂.mem = over s.mem A c.bs f := by
        rw [u₂.mem, u₁.gpr, u₁.mem, hm]
        have eB : over s.mem A (c.bs - 1) f B = f (c.bs - 1) := by
          have := VG.Proof.Modes.over_sep (m := s.mem) (f := f) (P := A) (Q := B) (n := c.bs - 1) (k := sz c ds y)
            (((h.disjoint hxy).sub_left (Region.sub_prefix (by omega)))) (i := 0) py (by omega)
          simp only [add0] at this
          rw [this]; simp only [f, show ¬ (c.bs - 1 < c.bs - 1) from Nat.lt_irrefl _, ite_false]
        rw [eB, show ((f (c.bs - 1)).setWidth 32).setWidth 8 = f (c.bs - 1) by simp,
          writeW_over_step (by omega), Nat.sub_add_cancel (by omega)]
      refine ⟨fun r a b => by rw [u₂.gpr, u₁.other _ a, g _ a], by rw [u₂.rd, u₁.rd, rd], by rw [u₂.wr, u₁.wr, wr],
        by rw [u₂.sp, u₁.sp, sp], by rw [em]; exact frame_over _ x _ (by rw [hx]), ?_⟩
      rw [em]
      refine blkMem_over h hb x _ f ?_ hx.symm
      rw [hx, ← hb x, ← hb y]
      obtain ⟨n, hn⟩ : ∃ n, c.bs = n + 1 := ⟨c.bs - 1, by omega⟩
      obtain ⟨k, hk⟩ : ∃ k, sz c ds y = k + 1 := ⟨sz c ds y - 1, by omega⟩
      have e1 : (List.range (n + 1)).map f =
          (List.range n).map (fun i => s.mem (A + BitVec.ofNat 64 (i + 1))) ++ [s.mem B] := by
        rw [List.range_succ, List.map_append, List.map_singleton]
        congr 1
        · exact List.map_congr_left fun i hi => by
            simp only [f, hn, Nat.add_sub_cancel, ite_eq_left (List.mem_range.mp hi)]
        · simp [f, hn]
      rw [hx, hk, hn, e1]
      simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map, List.headD_cons, add0]
      rfl

theorem runOp_length {op : Op} {byte : Bool} (hok : opOk byte op = true) {b : Blks} {c : Core} {ds : Nat}
    (hpos : ∀ x, 0 < sz c ds x) (hl : ∀ x, (b.get x).length = sz c ds x)
    (hds : byte = false → ds = c.bs) : ∀ x, ((runOp op b).get x).length = sz c ds x := by
  intro z
  cases op with
  | copy x y =>
    by_cases hz : z = x
    · subst hz; simp only [runOp, Blks.get_set_self, hl]
      simp only [opOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
      rcases hok.2 with hb' | hb'
      · cases z <;> cases y <;> simp [sz, hds hb']
      · cases z <;> cases y <;> simp_all [sz]
    · simp [runOp, Blks.get_set_of_ne _ _ hz, hl]
  | xor x y =>
    by_cases hz : z = x
    · subst hz; simp only [runOp, Blks.get_set_self, Spec.Cbc.xor, List.length_zipWith, hl]
      simp only [opOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
      rcases hok.2 with hb' | hb'
      · cases z <;> cases y <;> simp [sz, hds hb']
      · cases z <;> cases y <;> simp_all [sz]
    · simp [runOp, Blks.get_set_of_ne _ _ hz, hl]
  | xorB x y =>
    by_cases hz : z = x
    · subst hz; simp only [runOp, Blks.get_set_self]
      have := hl z
      cases hh : b.get z <;> simp_all [xorHead]
    · simp [runOp, Blks.get_set_of_ne _ _ hz, hl]
  | shift x y =>
    by_cases hz : z = x
    · subst hz; simp only [runOp, Blks.get_set_self, List.length_append, List.length_tail, hl,
        List.length_singleton]
      have := hpos z; omega
    · simp [runOp, Blks.get_set_of_ne _ _ hz, hl]

/-- The code of a list of operations. -/
theorem opsCode_wp {c : Core} {ds : Nat} {byte : Bool} (hds : byte = false → ds = c.bs) {Dp S : BitVec 32}
    {s : State} (h : Lay c ds Dp S s.wr) (h6 : s.gpr .r6 = Dp) (h8 : s.gpr .r8 = S) {b : Blks}
    (hb : BlkMem c ds Dp S s.mem b) {ops : List Op} (hok : ops.all (opOk byte) = true) :
    WP isa (.block (c.opsCode ops)) s (OpsInv c ds Dp S s (runOps ops b)) := by
  induction ops generalizing s b with
  | nil => exact WP.block_nil (OpsInv.refl hb)
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [Core.opsCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (opCode_wp hds h h6 h8 hb hok.1) fun s₁ h₁ => ?_
    have h6' : s₁.gpr .r6 = Dp := by rw [h₁.regs _ (by decide) (by decide), h6]
    have h8' : s₁.gpr .r8 = S := by rw [h₁.regs _ (by decide) (by decide), h8]
    exact WP.mono (ih (h₁.wr ▸ h) h6' h8' h₁.blks hok.2) fun s₂ h₂ => h₁.trans h₂

end VG.Proof.Modes.Arm
