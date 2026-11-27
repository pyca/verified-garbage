module

public import VerifiedGarbage.Proof.AesCbc.Arm.Body
public import VerifiedGarbage.Impl.AesCbc.Arm.Groups
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.AesXts.Arm
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.MdStream.Arm.Common

/-! ### `AesXts.Arm.Steps`, which this module and modules that import it used -/

section

/-!
# XTS-AES on ARMv7: multiplication by `α`

`mulA` run once, with its memory as explicit writes (`alphaMem`): the
canonical words of `mulAlpha_words32` (`Proof/AesXts/Alpha.lean`), from
shifted-register operands, `sub`, `and`, `eor` and `orr`.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.Arm
open VG.Impl.AesCbc.Arm (mulA)
open VG.Spec.Aes (bytesAt)

/-- The memory after `mulA` on the tweak at `Q`. -/
def alphaMem (m : Mem) (Q : Addr) : Mem :=
  let w (d : Nat) := m.readW (Q + BitVec.ofNat 64 d) 32
  (((m.writeW Q ((w 0 <<< 1) ^^^ (if (w 12).msb then (0x87 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 4) ((w 4 <<< 1) ||| (if (w 0).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 8) ((w 8 <<< 1) ||| (if (w 4).msb then (1 : BitVec 32) else 0))).writeW
      (Q + BitVec.ofNat 64 12) ((w 12 <<< 1) ||| (if (w 8).msb then (1 : BitVec 32) else 0))

theorem ushr31 (x : BitVec 32) : x >>> 31 = if x.msb then (1 : BitVec 32) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := x.isLt
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [decide_eq_true h]; show _ = 1; omega_using [h]
  · rw [decide_eq_false h]; show _ = 0; omega_using [h]

theorem mask_87 (x : BitVec 32) :
    (0 - (if x.msb then (1 : BitVec 32) else 0)) &&& (0x87 : BitVec 32) = if x.msb then (0x87 : BitVec 32) else 0 := by
  cases x.msb <;> decide

theorem mulA_ok (s : State) {Q : Addr} (hq : State.addr (s.gpr .r6) = Q)
    (hfit : (s.gpr .r6).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa mulA s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = alphaMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : State.addr (s.gpr .r6 + BitVec.ofNat 32 d) = Q + BitVec.ofNat 64 d := by
    rw [addr_add (by omega_using [hfit, hd]), hq]
  have a0 : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = Q := by rw [a 0 (by decide)]; simp
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := Proof.MdStream.Arm.op2_imm (by decide)
  have i87 (t : State) : (Op2.imm 0x87).eval t = some 0x87 := Proof.MdStream.Arm.op2_imm (by decide)
  have l1 (t : State) (r : Reg) : (Op2.shifted r .lsl 1).eval t = some (t.gpr r <<< 1) :=
    Proof.MdStream.Arm.op2_lsl (by decide)
  have r31 (t : State) (r : Reg) : (Op2.shifted r .lsr 31).eval t = some (t.gpr r >>> 31) :=
    Proof.MdStream.Arm.op2_lsr (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, mulA, runBlock_cons, runStep_some, runBlock_nil, exec,
      i0, i87, l1, r31, Proof.MdStream.Arm.op2_reg, State.load32, State.store32, Option.map_some, Nat.reduceLT,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, a0, a 4 (by decide), a 8 (by decide), a 12 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide),
      hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ h₅ h₆ => by simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅, h₆], rfl, ?_, rfl, rfl⟩
  have e0 : Q + BitVec.ofNat 64 0 = Q := by simp
  simp only [alphaMem, e0, ushr31, mask_87]

theorem alphaMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (alphaMem m Q) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))

theorem alphaMem_bytes (m : Mem) (Q : Addr) : bytesAt (alphaMem m Q) Q 16 = Spec.Xts.mulAlpha (bytesAt m Q 16) := by
  have := AesXts.mulAlpha_words32 m Q
  have e0 : Q + BitVec.ofNat 64 0 = Q := by simp
  simp only [e0] at this
  simp only [alphaMem, e0]
  exact this

end VG.Proof.AesXts.Arm

end

end

/-!
# A group's block operations on ARMv7, and what they compute

A group of AES's modes (`Impl/AesCbc/Arm/Groups.lean`) works on its `G` data
blocks (at `r7`), the `G` blocks of the buffer in the scratch buffer (at
`r10 + wOff`) and the chaining value (at `r6`): `GBlks` holds their
contents, `grunOp` is what an operation does to them, and `opsCode_wp` says
that the code of a list of operations (`opsCode`) leaves them as `grunOps`
says, changing only them, `r0`–`r3`, `r12` and `lr` (`GBlkMem`, with the
blocks where `GLay` puts them). `UPre.glay`: the blocks of the group after `k` blocks are
laid out so.
-/

-- separate module: the operations' proofs cost more than their imports, so a change to the groups' proof (`Groups.lean`) does not check them again.

@[expose] public section

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (xor4)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR add0)
open VG.Spec.Aes (bytesAt)

/-- The contents of a group's blocks. -/
abbrev GBlks := GBlk → List Byte

/-- The blocks, with `v` as block `x`. -/
def gset (b : GBlks) (x : GBlk) (v : List Byte) : GBlks := fun y => if y = x then v else b y

theorem gset_self (b : GBlks) (x : GBlk) (v : List Byte) : gset b x v x = v := by
  simp only [gset, ↓reduceIte]

theorem gset_of_ne (b : GBlks) {x y : GBlk} (v : List Byte) (h : y ≠ x) : gset b x v y = b y := by
  simp only [gset, h, ↓reduceIte]

/-- What an operation does to the blocks. -/
def grunOp : GOp → GBlks → GBlks
  | .copy x y, b => gset b x (b y)
  | .xor x y, b => gset b x (Spec.Cbc.xor (b x) (b y))
  | .mulA, b => gset b .iv (Spec.Xts.mulAlpha (b .iv))

/-- The operations, in order. -/
def grunOps (ops : List GOp) (b : GBlks) : GBlks := ops.foldl (fun b op => grunOp op b) b

/-- A block of a group of `G`. -/
def _root_.VG.Impl.AesCbc.Arm.GBlk.ok (G : Nat) : GBlk → Bool
  | .d j => decide (j < G)
  | .w j => decide (j < G)
  | .iv => true

/-- An operation on two different blocks of a group of `G`. -/
def gopOk (G : Nat) : GOp → Bool
  | .copy x y => x != y && x.ok G && y.ok G
  | .xor x y => x != y && x.ok G && y.ok G
  | .mulA => true

/-! ## Where the blocks are -/

/-- What a block's base register holds, with the group's data at `D`, the
scratch buffer at `Sb` and the chaining value at `I`. -/
def gptr (D Sb I : BitVec 32) : GBlk → BitVec 32
  | .d _ => D
  | .w _ => Sb
  | .iv => I

/-- The address of each block. -/
def gaddr (D Sb I : BitVec 32) (x : GBlk) : Addr := State.addr (gptr D Sb I x) + BitVec.ofNat 64 x.base.2

/-- The regions of a group's blocks. -/
abbrev gRegions (G : Nat) (D Sb I : BitVec 32) : List Region :=
  [⟨State.addr D, 16 * G⟩, ⟨State.addr Sb + BitVec.ofNat 64 wOff, 80⟩, ⟨State.addr I, 16⟩]

/-- The blocks' layout: each within the address space and in reach of its
base register, writable (in `wr`), and apart from the others. -/
structure GLay (G : Nat) (D Sb I : BitVec 32) (wr : List Region) : Prop where
  g5 : G ≤ 5
  fit : ∀ x, x.ok G = true → (gptr D Sb I x).toNat + x.base.2 + 16 ≤ 2 ^ 32
  cov : ∀ x, x.ok G = true → Covers [⟨gaddr D Sb I x, 16⟩] wr
  sep : ∀ x y, x.ok G = true → y.ok G = true → x ≠ y →
    Region.Disjoint ⟨gaddr D Sb I x, 16⟩ ⟨gaddr D Sb I y, 16⟩

/-- The blocks' contents in memory. -/
def GBlkMem (G : Nat) (D Sb I : BitVec 32) (m : Mem) (b : GBlks) : Prop :=
  ∀ x, x.ok G = true → bytesAt m (gaddr D Sb I x) 16 = b x

theorem gbase_ne (x : GBlk) : x.base.1 ≠ .r12 ∧ x.base.1 ≠ .lr := by cases x <;> simp [GBlk.base]

theorem gbase_gpr {s : State} {D Sb I : BitVec 32} (h7 : s.gpr .r7 = D) (h10 : s.gpr .r10 = Sb)
    (h6 : s.gpr .r6 = I) (x : GBlk) : s.gpr x.base.1 = gptr D Sb I x := by
  cases x
  · exact h7
  · exact h10
  · exact h6

theorem goff {G : Nat} (hG : G ≤ 5) {x : GBlk} (hx : x.ok G = true) : x.base.2 + 12 < 4096 := by
  cases x with
  | d j => have : j < G := by simpa [GBlk.ok] using hx
           show 16 * j + 12 < 4096; omega_using [this, hG]
  | w j => have : j < G := by simpa [GBlk.ok] using hx
           show wOff + 16 * j + 12 < 4096; unfold wOff; omega_using [this, hG]
  | iv => decide

/-- A block, within the regions of the blocks. -/
theorem gsub {G : Nat} (hG : G ≤ 5) {D Sb I : BitVec 32} {x : GBlk} (hx : x.ok G = true) :
    ∃ r ∈ gRegions G D Sb I, Region.Sub ⟨gaddr D Sb I x, 16⟩ r := by
  cases x with
  | d j =>
    have : j < G := by simpa [GBlk.ok] using hx
    exact ⟨_, List.mem_cons_self, Offset.sub_base _ (show 16 * j + 16 ≤ 16 * G by omega_using [this])⟩
  | w j =>
    have : j < G := by simpa [GBlk.ok] using hx
    exact ⟨⟨State.addr Sb + BitVec.ofNat 64 wOff, 80⟩, by simp,
      Offset.sub _ (show wOff ≤ wOff + 16 * j from Nat.le_add_right _ _)
        (show wOff + 16 * j + 16 ≤ wOff + 80 by omega_using [this, hG])⟩
  | iv => exact ⟨⟨State.addr I, 16⟩, by simp, Offset.sub_base _ (by decide)⟩

/-! ## One operation, and a list of them -/

/-- What the code of operations from `s` keeps. -/
structure GOpsInv (G : Nat) (D Sb I : BitVec 32) (s : State) (b : GBlks) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (gRegions G D Sb I) s.mem s'.mem
  blks : GBlkMem G D Sb I s'.mem b

theorem GOpsInv.refl {G : Nat} {D Sb I : BitVec 32} {s : State} {b : GBlks} (hb : GBlkMem G D Sb I s.mem b) :
    GOpsInv G D Sb I s b s :=
  ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, hb⟩

theorem GOpsInv.trans {G : Nat} {D Sb I : BitVec 32} {s s₁ s₂ : State} {b b' : GBlks}
    (h₁ : GOpsInv G D Sb I s b s₁) (h₂ : GOpsInv G D Sb I s₁ b' s₂) : GOpsInv G D Sb I s b' s₂ :=
  ⟨fun x h0 h1 h2 h3 h12 hlr => by rw [h₂.regs x h0 h1 h2 h3 h12 hlr, h₁.regs x h0 h1 h2 h3 h12 hlr],
    by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr],
    by rw [h₂.sp, h₁.sp], h₁.frame.trans h₂.frame, h₂.blks⟩

/-- The blocks after block `x` was written, the others as they were. -/
theorem gblkMem_set {G : Nat} {D Sb I : BitVec 32} {wr : List Region} (h : GLay G D Sb I wr) {m m' : Mem}
    {b : GBlks} (hb : GBlkMem G D Sb I m b) {x : GBlk} (hx : x.ok G = true)
    (hf : Frame [⟨gaddr D Sb I x, 16⟩] m m') {v : List Byte} (hv : bytesAt m' (gaddr D Sb I x) 16 = v) :
    GBlkMem G D Sb I m' (gset b x v) := by
  intro z hz
  by_cases e : z = x
  · subst e; rw [gset_self, hv]
  · rw [gset_of_ne _ _ e, Proof.Cmac.bytesAt_frame hf (one (h.sep z x hz hx e)) (by decide), hb z hz]

theorem gframe_one {G : Nat} (hG : G ≤ 5) {D Sb I : BitVec 32} {m m' : Mem} {x : GBlk} (hx : x.ok G = true)
    (hf : Frame [⟨gaddr D Sb I x, 16⟩] m m') : Frame (gRegions G D Sb I) m m' := by
  obtain ⟨r, hr, hs⟩ := gsub hG (D := D) (Sb := Sb) (I := I) hx
  exact hf.sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact ⟨r, hr, hs⟩

theorem copy_code (x y : GBlk) : (GOp.copy x y).code =
    zero4 x.base.1 x.base.2 ++ (xor4 x.base.1 y.base.1 x.base.1 x.base.2 y.base.2 x.base.2 ++ []) := by
  rw [List.append_nil]; rfl

theorem xor_code (x y : GBlk) : (GOp.xor x y).code =
    xor4 x.base.1 y.base.1 x.base.1 x.base.2 y.base.2 x.base.2 ++ [] := by
  rw [List.append_nil]; rfl

/-- The code of one operation. -/
theorem gopCode_wp {G : Nat} {D Sb I : BitVec 32} {s : State} (h : GLay G D Sb I s.wr)
    (h7 : s.gpr .r7 = D) (h10 : s.gpr .r10 = Sb) (h6 : s.gpr .r6 = I) {b : GBlks}
    (hb : GBlkMem G D Sb I s.mem b) {op : GOp} (hok : gopOk G op = true) :
    WP isa (.block op.code) s (GOpsInv G D Sb I s (grunOp op b)) := by
  cases op with
  | copy x y =>
    obtain ⟨hxy, hx, hy⟩ : x ≠ y ∧ x.ok G = true ∧ y.ok G = true := by
      simpa [gopOk, and_assoc] using hok
    obtain ex := gbase_gpr h7 h10 h6 x
    obtain ey := gbase_gpr h7 h10 h6 y
    rw [copy_code]
    refine copy_wp (gbase_ne y) (gbase_ne x) (goff h.g5 hx) (goff h.g5 hy) (by rw [ey]; exact h.fit y hy)
      (by rw [ex]; exact h.fit x hx) (by rw [ey]; exact Covers.right (h.cov y hy)) (by rw [ex]; exact h.cov x hx)
      fun s' g => WP.block_nil ?_
    obtain m' : s'.mem = copy4Mem s.mem (gaddr D Sb I x) (gaddr D Sb I y) := by rw [g.mem, ex, ey]; rfl
    obtain f := copy4Mem_frame s.mem (gaddr D Sb I x) (gaddr D Sb I y)
    rw [← m'] at f
    refine ⟨fun r _ _ _ _ => g.gpr r, g.rd, g.wr, g.sp, gframe_one h.g5 hx f, gblkMem_set h hb hx f ?_⟩
    rw [m', copy4Mem_bytes _ (h.sep x y hx hy hxy), hb y hy]
  | xor x y =>
    obtain ⟨hxy, hx, hy⟩ : x ≠ y ∧ x.ok G = true ∧ y.ok G = true := by
      simpa [gopOk, and_assoc] using hok
    obtain ex := gbase_gpr h7 h10 h6 x
    obtain ey := gbase_gpr h7 h10 h6 y
    rw [xor_code]
    refine xorIn_wp (gbase_ne y) (gbase_ne x) (goff h.g5 hx) (goff h.g5 hy) (by rw [ey]; exact h.fit y hy)
      (by rw [ex]; exact h.fit x hx) (by rw [ey]; exact Covers.right (h.cov y hy)) (by rw [ex]; exact h.cov x hx)
      fun s' g => WP.block_nil ?_
    obtain m' : s'.mem = Proof.Cmac.xor4Mem s.mem (gaddr D Sb I x) (gaddr D Sb I x) (gaddr D Sb I y) := by
      rw [g.mem, ex, ey]; rfl
    obtain f := Proof.Cmac.xor4Mem_frame s.mem (gaddr D Sb I x) (gaddr D Sb I x) (gaddr D Sb I y)
    rw [← m'] at f
    refine ⟨fun r _ _ _ _ => g.gpr r, g.rd, g.wr, g.sp, gframe_one h.g5 hx f, gblkMem_set h hb hx f ?_⟩
    rw [m', xorIn4_bytes _ (h.sep x y hx hy hxy), hb x hx, hb y hy]
  | mulA =>
    have hiv : GBlk.ok G .iv = true := rfl
    obtain a0 : gaddr D Sb I .iv = State.addr I := add0 _
    obtain w := h.cov .iv hiv
    have inW (d n : Nat) (hd : d + n ≤ 16) : InRegions s.wr (State.addr I + BitVec.ofNat 64 d) n :=
      w _ _ ⟨_, List.mem_singleton_self _, by rw [a0]; exact Offset.contains_base _ hd (by omega_using [hd])⟩
    obtain ⟨s', he, hg, hsp, hm, hrd, hwr⟩ := Proof.AesXts.Arm.mulA_ok s (Q := State.addr I) (by rw [h6])
      (by have := h.fit .iv hiv; rw [h6]; exact this)
      (fun d n hd => by
        obtain ⟨r, hr, hc⟩ := inW d n hd
        exact ⟨r, List.mem_append_right _ hr, hc⟩) inW
    obtain f : Frame [⟨gaddr D Sb I .iv, 16⟩] s.mem s'.mem := by
      rw [hm, a0]; exact Proof.AesXts.Arm.alphaMem_frame _ _
    refine WP.of_runBlock ⟨s', he, hg, hrd, hwr, hsp, gframe_one h.g5 hiv f, gblkMem_set h hb hiv f ?_⟩
    rw [hm, a0, Proof.AesXts.Arm.alphaMem_bytes, ← a0, hb .iv hiv]

/-- The code of a list of operations. -/
theorem opsCode_wp {G : Nat} {D Sb I : BitVec 32} {s : State} (h : GLay G D Sb I s.wr)
    (h7 : s.gpr .r7 = D) (h10 : s.gpr .r10 = Sb) (h6 : s.gpr .r6 = I) {b : GBlks}
    (hb : GBlkMem G D Sb I s.mem b) {ops : List GOp} (hok : ops.all (gopOk G) = true) :
    WP isa (.block (opsCode ops)) s (GOpsInv G D Sb I s (grunOps ops b)) := by
  induction ops generalizing s b with
  | nil => exact WP.block_nil (GOpsInv.refl hb)
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [opsCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (gopCode_wp h h7 h10 h6 hb hok.1) fun s₁ h₁ => ?_
    obtain h7' : s₁.gpr .r7 = D := by
      rw [h₁.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h7]
    obtain h10' : s₁.gpr .r10 = Sb := by
      rw [h₁.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h10]
    obtain h6' : s₁.gpr .r6 = I := by
      rw [h₁.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]
    exact WP.mono (ih (h₁.wr ▸ h) h7' h10' h6' h₁.blks hok.2) fun s₂ h₂ => h₁.trans h₂

/-- The registers the invariant pins, after operations. -/
theorem Regs.ofOps {s₀ : State} {k : Nat} {s s' : State} (h : Regs s₀ k s)
    (g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r)
    (sp : s'.sp = s.sp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : Regs s₀ k s' :=
  ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r4],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r5],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10], by rw [sp, h.sp],
    by rw [rd, h.rd], by rw [wr, h.wr]⟩

/-! ## The blocks of the group after `k` blocks -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The address of block `j` of the group after `k` blocks. -/
theorem UPre.gaddr_d {k j : Nat} (hk : k < N s₀) (Sb I : BitVec 32) :
    gaddr (D32 s₀ k) Sb I (.d j) = blk s₀ (k + j) := by
  show State.addr (Dp s₀ + BitVec.ofNat 32 (16 * k)) + BitVec.ofNat 64 (16 * j) = _
  rw [hp.dataA hk, Offset.add_add, ← Nat.mul_add]

/-- The address of block `j` of the buffer. -/
abbrev wblk (s₀ : State) (j : Nat) : Addr := State.addr (S s₀) + BitVec.ofNat 64 (wOff + 16 * j)

theorem UPre.wblk_sub {j : Nat} (hj : j < 5) : Region.Sub ⟨wblk s₀ j, 16⟩ (scrR s₀) :=
  have _ := hp
  Offset.sub_base _ (by unfold wOff; omega_using [hj])

/-- The blocks of the group of `G` after `k` blocks are laid out as the
operations need. -/
theorem UPre.glay {k G : Nat} (hG : 0 < G) (hG5 : G ≤ 5) (hk : k + G ≤ N s₀) :
    GLay G (D32 s₀ k) (S s₀) (Iv s₀) s₀.wr := by
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  have hiv := hp.iv_fit
  obtain hk' : k < N s₀ := by omega_using [hG, hk]
  obtain qN := hp.dataN hk'
  have jd : ∀ {x : GBlk} {j : Nat}, x.ok G = true → (x = .d j ∨ x = .w j) → j < G := by
    intro x j hx e
    rcases e with rfl | rfl <;> simpa [GBlk.ok] using hx
  refine ⟨hG5, fun x hx => ?_, fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · cases x with
    | d j => have := jd hx (.inl rfl)
             show (D32 s₀ k).toNat + 16 * j + 16 ≤ 2 ^ 32; rw [qN]; omega_using [this, hk, hdf]
    | w j => have := jd hx (.inr rfl)
             show (S s₀).toNat + (wOff + 16 * j) + 16 ≤ 2 ^ 32; unfold wOff; omega_using [this, hG5, hsc]
    | iv => show (Iv s₀).toNat + 0 + 16 ≤ 2 ^ 32; omega_using [hiv]
  · rw [hp.wr]
    cases x with
    | d j => have := jd hx (.inl rfl)
             rw [hp.gaddr_d hk']; exact covBlk (by omega_using [this, hk]) (by simp)
    | w j =>
      have := jd hx (.inr rfl)
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scrR s₀, by simp, wOff + 16 * j, rfl, by show wOff + 16 * j + 16 ≤ 2176; unfold wOff; omega_using [this, hG5]⟩
    | iv => show Covers [⟨State.addr (Iv s₀) + BitVec.ofNat 64 0, 16⟩] _
            rw [add0]; exact covIv (by simp)
  · have dw : ∀ i j, i < G → j < G → Region.Disjoint ⟨blk s₀ (k + i), 16⟩ ⟨wblk s₀ j, 16⟩ := fun i j hi hj =>
      (hp.data_scr.sub_left (UPre.data_sub (by omega_using [hi, hk]))).sub_right (hp.wblk_sub (by omega_using [hj, hG5]))
    have di : ∀ i, i < G → Region.Disjoint ⟨blk s₀ (k + i), 16⟩ (ivR s₀) := fun i hi =>
      hp.blk_iv (by omega_using [hi, hk])
    have wi : ∀ j, j < G → Region.Disjoint ⟨wblk s₀ j, 16⟩ (ivR s₀) := fun j hj =>
      (hp.iv_scr.sub_right (hp.wblk_sub (by omega_using [hj, hG5]))).symm
    have ivE : gaddr (D32 s₀ k) (S s₀) (Iv s₀) .iv = State.addr (Iv s₀) := add0 _
    cases x with
    | d i =>
      have hi := jd hx (.inl rfl)
      rw [hp.gaddr_d hk']
      cases y with
      | d j =>
        have hj := jd hy (.inl rfl)
        rw [hp.gaddr_d hk']
        exact hp.blk_disjoint (by omega_using [hi, hk]) (by omega_using [hj, hk])
          (fun e => hxy (by rw [show i = j by omega_using [e]]))
      | w j => exact dw i j hi (jd hy (.inr rfl))
      | iv => rw [ivE]; exact di i hi
    | w i =>
      have hi := jd hx (.inr rfl)
      cases y with
      | d j => rw [hp.gaddr_d hk']; exact (dw j i (jd hy (.inl rfl)) hi).symm
      | w j =>
        have hj := jd hy (.inr rfl)
        have hij : i ≠ j := fun e => hxy (by rw [e])
        exact Offset.disjoint _ (d := wOff + 16 * i) (e := wOff + 16 * j) (by omega_using [hij])
          (by unfold wOff; omega_using [hi, hG5]) (by unfold wOff; omega_using [hj, hG5])
      | iv => rw [ivE]; exact wi i hi
    | iv =>
      rw [ivE]
      cases y with
      | d j => rw [hp.gaddr_d hk']; exact (di j (jd hy (.inl rfl))).symm
      | w j => exact (wi j (jd hy (.inr rfl))).symm
      | iv => exact absurd rfl hxy

end

end VG.Proof.AesCbc.Arm
