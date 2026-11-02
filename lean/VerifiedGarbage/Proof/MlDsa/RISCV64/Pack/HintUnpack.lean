module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintBase
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_unpack`, the steps

As on 32-bit ARM (`Proof/MlDsa/Arm/Pack/HintUnpack.lean`), the code follows
the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Proof/MlDsa/Pack/Hint.lean`) step by step: while no check has failed, the
words of `h` are the hint of the spec (`HArr`) and `t1` its index; once one
has, `t1` is 256, which skips the rest (`SRel`). Here: the arguments,
zeroing `h`, one coefficient (`set_ok`, `next_ok`) and the coefficients of a
polynomial (`coefs_ok`); the polynomials, the trailing bytes and the return
value are in `HintUnpackMain.lean`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_add)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint (add0 ofNat_toNat64)

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `y`, `len`, `ω`, `h` and `hlen`. -/
abbrev uY : Addr := s₀.gpr .a0
abbrev uLen : Nat := (s₀.gpr .a1).toNat
abbrev uω : Nat := w32 s₀ .a2
abbrev uH : Addr := s₀.gpr .a3
abbrev uk : Nat := uLen s₀ - uω s₀
abbrev uyR : Region := ⟨uY s₀, uLen s₀⟩
abbrev uhR : Region := ⟨uH s₀, (s₀.gpr .a4).toNat * 4⟩
/-- The bytes of `y`, as the spec reads them. -/
abbrev uYs : Array Byte := (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray

end

/-- The precondition, as `sig_pre` states it. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [uyR s]
  wr : s.wr = [uhR s]
  d_yh : (uyR s).Disjoint (uhR s)
  fitY : (uY s).toNat + uLen s ≤ 2 ^ 64
  fitH : (uH s).toNat + (s.gpr .a4).toNat * 4 ≤ 2 ^ 64
  par : (uω s, uk s) ∈ hintParams
  ωle : uω s ≤ uLen s
  hlen : (s.gpr .a4).toNat = 256 * uk s
  al : (uH s).toNat % 4 = 0

theorem ufacts {s₀ : State} (hp : UPre s₀) :
    4 ≤ uk s₀ ∧ uk s₀ ≤ 8 ∧ 55 ≤ uω s₀ ∧ uω s₀ ≤ 80 ∧ uω s₀ + uk s₀ = uLen s₀ ∧ uLen s₀ ≤ 88 := by
  have := mem_hintParams' hp.par
  have := hp.ωle
  have e : uk s₀ = uLen s₀ - uω s₀ := rfl
  omega_arith

/-! ## Comparisons -/

/-- The register `ltBit` writes, as a condition. -/
theorem eval_lt_zero {s : State} {r : Reg} {a b : Nat} (h : s.gpr r = BitVec.ofNat 64 (if a < b then 1 else 0)) :
    isa.eval (.zero r) s = some (decide (b ≤ a)) := by
  show some (s.gpr r == 0) = _
  rw [h]
  split <;> simp <;> omega_arith

theorem eval_lt_nonzero {s : State} {r : Reg} {a b : Nat}
    (h : s.gpr r = BitVec.ofNat 64 (if a < b then 1 else 0)) :
    isa.eval (.nonzero r) s = some (decide (a < b)) := by
  show some (s.gpr r != 0) = _
  rw [h]
  split <;> simp <;> omega_arith

/-- A byte, as a word offset. -/
theorem shl2_byte (b : Byte) : b.setWidth 64 <<< 2 = BitVec.ofNat 64 (4 * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, ofNat_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem ptr_pred (p : Addr) {x : Nat} (h : 1 ≤ x) :
    p + BitVec.ofNat 64 x - BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (x - 1) := by
  rw [show x = (x - 1) + 1 by omega_arith, ← ofNat_succ, ← BitVec.add_assoc, BitVec.add_sub_cancel,
    Nat.add_sub_cancel]

/-! ## The hint in memory -/

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `t1`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .t1 = BitVec.ofNat 64 idx ∧ idx ≤ uω s₀ ∧ HArr s.mem (uH s₀) (uk s₀) hA
  | none, s => s.gpr .t1 = BitVec.ofNat 64 256

/-- What stays the same throughout the loops. -/
structure UCom (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = uY s₀
  a2 : s.gpr .a2 = BitVec.ofNat 64 (uω s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [uhR s₀] s₀.mem s.mem

theorem UCom.of {s₀ s s' : State} (h : UCom s₀ s) {rs : List Reg} (hk : Keep rs s s') (h3 : Reg.a0 ∉ rs)
    (h5 : Reg.a2 ∉ rs) (hm : Frame [uhR s₀] s.mem s'.mem) : UCom s₀ s' :=
  ⟨(hk.gpr h3).trans h.a0, (hk.gpr h5).trans h.a2, hk.2.1.trans h.rd, hk.2.2.trans h.wr, h.frame.trans hm⟩

/-- Where the loops of polynomial `i` are, with the bound in `a5`. -/
structure PCom (s₀ : State) (i bound : Nat) (s : State) : Prop where
  com : UCom s₀ s
  a3 : s.gpr .a3 = uH s₀ + BitVec.ofNat 64 (1024 * i)
  a5 : s.gpr .a5 = BitVec.ofNat 64 bound

/-- The coefficient steps write only `t0`, `a6` and `t1`. -/
abbrev cRegs : List Reg := [.t0, .a6, .t1]

theorem PCom.of {s₀ s s' : State} {i bound : Nat} (h : PCom s₀ i bound s) (hk : Keep cRegs s s')
    (hm : Frame [uhR s₀] s.mem s'.mem) : PCom s₀ i bound s' :=
  ⟨h.com.of hk (by decide) (by decide) hm, (hk.gpr (by decide)).trans h.a3, (hk.gpr (by decide)).trans h.a5⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s : State} (hc : UCom s₀ s) {t : Nat} (ht : t < uLen s₀) :
    s.mem (uY s₀ + BitVec.ofNat 64 t) = (uYs s₀).getD t 0 := by
  have fY := hp.fitY
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.d_yh _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc'

theorem yIn {s : State} (hc : UCom s₀ s) {t : Nat} (ht : t < uLen s₀) :
    InRegions (s.rd ++ s.wr) (uY s₀ + BitVec.ofNat 64 t) 1 := by
  have fY := hp.fitY
  rw [hc.rd, hp.rd]; exact ⟨_, .head _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-! ## Zeroing `h` -/

/-- What zeroing `h` leaves. -/
structure ZPost (s s' : State) : Prop where
  com : UCom s s'
  a3 : s'.gpr .a3 = uH s
  t1 : s'.gpr .t1 = 0
  t2 : s'.gpr .t2 = BitVec.ofNat 64 (uk s)
  zero : ∀ t < 256 * uk s, coeffAt s'.mem (uH s) t = 0

/-- The zeroing loop after `t` words, from `s₁`. -/
structure ZInv (s₀ s₁ : State) (t : Nat) (s : State) : Prop where
  a7 : s.gpr .a7 = uH s₀ + BitVec.ofNat 64 (4 * t)
  a6 : s.gpr .a6 = BitVec.ofNat 64 (256 * uk s₀ - t)
  keep : Keep [.a6, .a7] s₁ s
  frame : Frame [uhR s₀] s₀.mem s.mem
  zero : ∀ u < t, coeffAt s.mem (uH s₀) u = 0

omit hp in
theorem coeffAt_writeW_ne' (m : Mem) (p : Addr) {i j : Nat} (hi : i < 2048) (hj : j < 2048) (h : i ≠ j)
    (v : BitVec 32) : coeffAt (m.writeW (coeffAddr p j) v) p i = coeffAt m p i := by
  rw [coeffAt_eq, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]

theorem zero_ok : WP isa hbuZero s₀ (ZPost s₀) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  unfold hbuZero zextOmega
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (Steps.wp_sll (by decide) fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => Steps.wp_sub fun s₃ o₃ =>
    Steps.wp_addi (by decide) fun s₄ o₄ => Steps.wp_li (by decide) fun s₅ o₅ =>
    Steps.wp_addi (by decide) fun s₆ o₆ => WP.block_nil ?_)
  have k₅ := (((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH
  have k₆ := k₅.trans o₆.keepH
  have m₆ : s₆.mem = s₀.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have r5 : s₆.gpr .a2 = BitVec.ofNat 64 (uω s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr,
      o₁.gpr, zext_eq]
  have r0 : s₆.gpr .t0 = 0 := by rw [o₆.other _ (by decide), o₅.gpr]; rfl
  have r12 : s₆.gpr .t2 = BitVec.ofNat 64 (uk s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.gpr,
      o₂.other _ (by decide), o₁.other _ (by decide), o₂.gpr, o₁.gpr, zext_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_lt (by omega_arith)]; exact hp.ωle), ofNat_lt (by omega_arith),
      ofNat_lt (by omega_arith)]
  have hwr : s₆.wr = [uhR s₀] := by rw [k₆.2.2, hp.wr]
  refine WP.seq (wp_loop_nz (ZInv s₀ s₆) (N := 256 * uk s₀) (by omega_arith) (fun t ht s h => ?_) (fun s h => ?_)
    ⟨by rw [o₆.gpr, k₅.gpr (r := .a3) (by decide), add0], ?_, Keep.refl _ _,
      by rw [m₆]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
  · -- A word.
    have hc : (uhR s₀).Contains (coeffAddr (uH s₀) t) 4 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine Steps.wp_sw (by decide) (by rw [h.a7, add0]) (VG.Proof.MlKem.RISCV64.align4_add hp.al t)
      (by rw [h.keep.2.2, hwr]; exact ⟨_, List.mem_singleton_self _, hc⟩) fun s₁ m₁ =>
      Steps.wp_addi (by decide) fun s₂ o₂ => Steps.wp_subi (by decide) fun s₃ o₃ => WP.block_nil ?_
    have c9 : s₃.gpr .a6 = BitVec.ofNat 64 (256 * uk s₀ - (t + 1)) := by
      rw [o₃.gpr, o₂.other _ (by decide), m₁.gpr, h.a6, count_sub ht]
    have m₃ : s₃.mem = s.mem.writeW (coeffAddr (uH s₀) t) ((s.gpr .t0).setWidth 32) := by
      rw [o₃.mem, o₂.mem, m₁.mem]
    have z0 : (s.gpr .t0).setWidth 32 = 0 := by rw [h.keep.gpr (by decide), r0]; rfl
    refine ⟨⟨?_, c9, (h.keep.trans ((m₁.keepH.trans o₂.keepH).trans o₃.keepH)).mono (by decide), ?_,
      fun u hu => ?_⟩, by rw [c9]; exact count_nz ht (by omega_arith)⟩
    · rw [o₃.other _ (by decide), o₂.gpr, m₁.gpr, h.a7, ptr_add, Nat.mul_succ]
    · rw [m₃]; exact h.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [m₃, z0]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
      · rw [coeffAt_writeW_ne' _ _ (by omega_arith) (by omega_arith) e, h.zero u (by omega_arith)]
  · refine Steps.wp_li (by decide) fun s' o' => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, o'.gpr, ?_, ?_⟩
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), k₆.gpr (by decide)]
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), r5]
    · rw [o'.rd, h.keep.2.1, k₆.2.1]
    · rw [o'.wr, h.keep.2.2, k₆.2.2]
    · rw [o'.mem]; exact h.frame
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), k₆.gpr (by decide)]
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), r12]
    · rw [o'.mem]; exact h.zero

  · rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.gpr, add0, Nat.sub_zero, ← hl, ofNat_toNat64,
      o₃.other _ (by decide), o₂.other _ (by decide), o₁.other _ (by decide)]
/-! ## One coefficient -/

/-- The index of a state of the spec: 256 once a check failed. -/
def ixOf : Option (Array (Vector Bool n) × Nat) → Nat
  | some (_, idx) => idx
  | none => 256

/-- Setting coefficient `y[index]` of polynomial `i`. -/
theorem set_ok {i bound idx : Nat} (hi : i < uk s₀) (hidx : idx < uLen s₀) {hA : Array (Vector Bool n)}
    {s : State} (hP : PCom s₀ i bound s) (h11 : s.gpr .t1 = BitVec.ofNat 64 idx)
    (hh : HArr s.mem (uH s₀) (uk s₀) hA) :
    WP isa (.block hbuSet) s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧
      s'.gpr .t1 = BitVec.ofNat 64 (idx + 1) ∧
      HArr s'.mem (uH s₀) (uk s₀) (huSet i ((uYs s₀).getD idx 0).toNat hA) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  have hb := ((uYs s₀).getD idx 0).isLt
  have hc : (uhR s₀).Contains (coeffAddr (uH s₀) (256 * i + ((uYs s₀).getD idx 0).toNat)) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold hbuSet
  refine Steps.wp_add fun s₁ o₁ => wp_lbz (a := uY s₀ + BitVec.ofNat 64 idx) (by decide) (by decide)
    (by rw [o₁.gpr, hP.com.a0, h11, add0]) (by rw [o₁.rd, o₁.wr]; exact yIn hp hP.com hidx) fun s₂ o₂ =>
    Steps.wp_sll (by decide) fun s₃ o₃ => Steps.wp_add fun s₄ o₄ => Steps.wp_li (by decide) fun s₅ o₅ =>
    Steps.wp_sw (a := coeffAddr (uH s₀) (256 * i + ((uYs s₀).getD idx 0).toNat)) (by decide) ?_
      (VG.Proof.MlKem.RISCV64.align4_add hp.al _) (by rw [o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr, hP.com.wr, hp.wr]; exact ⟨_, .head _, hc⟩) fun s₆ m₆ =>
    Steps.wp_addi (by decide) fun s₇ o₇ => WP.block_nil ?_
  · rw [o₅.other _ (by decide), o₄.gpr, o₃.other _ (by decide), o₃.gpr, o₂.other _ (by decide),
      o₁.other _ (by decide), hP.a3, o₂.gpr, o₁.mem, yByte hp hP.com hidx, shl2_byte, add0, ptr_add]
    congr 2; omega_arith
  have k₇ := (((((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH).trans m₆.keepH).trans
    o₇.keepH
  have mem₇ : s₇.mem = s.mem.writeW (coeffAddr (uH s₀) (256 * i + ((uYs s₀).getD idx 0).toNat)) (1 : BitVec 32) := by
    rw [o₇.mem, m₆.mem, o₅.gpr, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]; rfl
  refine ⟨hP.of (k₇.mono (by decide)) (by rw [mem₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc),
    k₇.mono (by decide), ?_, by rw [mem₇]; exact harr_set hk8 hh hi hb⟩
  rw [o₇.gpr, m₆.gpr, o₅.other _ (by decide), o₄.other _ (by decide), o₃.other _ (by decide),
    o₂.other _ (by decide), o₁.other _ (by decide), h11, ofNat_succ]

omit hp in
/-- `r0 ← (index < bound)`. -/
theorem more_ok {i bound idx : Nat} (hb : bound < 256) (hidx : idx ≤ 256) {s : State}
    (hP : PCom s₀ i bound s) (h11 : s.gpr .t1 = BitVec.ofNat 64 idx) :
    WP isa (.block hbuMore) s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧ s'.mem = s.mem ∧
      s'.gpr .t1 = BitVec.ofNat 64 idx ∧ s'.gpr .t0 = BitVec.ofNat 64 (if idx < bound then 1 else 0) := by
  unfold hbuMore ltBit
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => WP.block_nil ?_
  have k₂ := o₁.keepH.trans o₂.keepH
  refine ⟨hP.of (k₂.mono (by decide)) (by rw [o₂.mem, o₁.mem]; exact Frame.refl _ _), k₂.mono (by decide),
    by rw [o₂.mem, o₁.mem], by rw [k₂.gpr (by decide), h11], ?_⟩
  rw [o₂.gpr, o₁.gpr, h11, hP.a5, ltBit_eq (by omega_arith) (by omega_arith)]

/-- A coefficient after the first: checked against the previous one. -/
theorem next_ok {i bound first idx : Nat} (hi : i < uk s₀) (hfi : first < idx) (hib : idx < bound)
    (hbω : bound ≤ uω s₀) {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s)
    (h11 : s.gpr .t1 = BitVec.ofNat 64 idx) (hh : HArr s.mem (uH s₀) (uk s₀) hA) :
    WP isa hbuNext s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧
      SRel s₀ (huStep (uYs s₀) i first (hA, idx) 0) s' ∧
      s'.gpr .t0 = BitVec.ofNat 64 (if ixOf (huStep (uYs s₀) i first (hA, idx) 0) < bound then 1 else 0) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have hcb := ((uYs s₀).getD idx 0).isLt
  have hpb := ((uYs s₀).getD (idx - 1) 0).isLt
  unfold hbuNext ltBit
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (Steps.wp_add fun s₁ o₁ => wp_lbz (a := uY s₀ + BitVec.ofNat 64 idx) (by decide) (by decide)
    (by rw [o₁.gpr, hP.com.a0, h11, add0]) (by rw [o₁.rd, o₁.wr]; exact yIn hp hP.com (by omega_arith)) fun s₂ o₂ =>
    Steps.wp_subi (by decide) fun s₃ o₃ =>
    wp_lbz (a := uY s₀ + BitVec.ofNat 64 (idx - 1)) (by decide) (by decide)
      (by rw [o₃.gpr, o₂.other _ (by decide), o₁.gpr, hP.com.a0, h11, add0, ptr_pred _ (by omega_arith)])
      (by rw [o₃.rd, o₃.wr, o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact yIn hp hP.com (by omega_arith)) fun s₄ o₄ =>
    Steps.wp_sub fun s₅ o₅ => Steps.wp_srl (by decide) fun s₆ o₆ => WP.block_nil ?_)
  have k₆ := ((((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH).trans o₆.keepH
  have m₆ : s₆.mem = s.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have hP₆ : PCom s₀ i bound s₆ := hP.of (k₆.mono (by decide)) (by rw [m₆]; exact Frame.refl _ _)
  have r0 : s₆.gpr .t0 = BitVec.ofNat 64
      (if ((uYs s₀).getD (idx - 1) 0).toNat < ((uYs s₀).getD idx 0).toNat then 1 else 0) := by
    rw [o₆.gpr, o₅.gpr, o₄.gpr, o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr, o₃.mem, o₂.mem, o₁.mem,
      yByte hp hP.com (by omega_arith), yByte hp hP.com (by omega_arith), byte_ofNat, byte_ofNat,
      ltBit_eq (by omega_arith) (by omega_arith)]
  have h11₆ : s₆.gpr .t1 = BitVec.ofNat 64 idx := by rw [k₆.gpr (by decide), h11]
  refine WP.seq (WP.ite _ (eval_lt_zero r0) (fun hge => ?_) (fun hlt => ?_))
  · -- Not increasing: fail.
    have hge : ((uYs s₀).getD idx 0).toNat ≤ ((uYs s₀).getD (idx - 1) 0).toNat := of_decide_eq_true hge
    have hs : huStep (uYs s₀) i first (hA, idx) 0 = none := by
      simp only [huStep]; exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hfi, hge⟩)
    rw [hs]
    refine Steps.wp_li (by decide) fun s₇ o₇ => WP.block_nil ?_
    have hP₇ : PCom s₀ i bound s₇ := hP₆.of (o₇.keepH.mono (by decide)) (by rw [o₇.mem]; exact Frame.refl _ _)
    refine WP.mono (more_ok (by omega_arith) (by decide) hP₇ o₇.gpr) fun s₈ ⟨hP₈, k₈, _, h11₈, r0₈⟩ =>
      ⟨hP₈, ((k₆.trans o₇.keepH).trans k₈).mono (by decide), h11₈, r0₈⟩
  · -- `y[index - 1] < y[index]`: set it.
    have hlt : ((uYs s₀).getD (idx - 1) 0).toNat < ((uYs s₀).getD idx 0).toNat := by
      have := of_decide_eq_false hlt; omega_arith
    have hs : huStep (uYs s₀) i first (hA, idx) 0 = some (huSet i ((uYs s₀).getD idx 0).toNat hA, idx + 1) := by
      simp only [huStep]; exact ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))
    rw [hs]
    refine WP.mono (set_ok hp hi (hA := hA) (by omega_arith) hP₆ h11₆ (by rw [m₆]; exact hh)) fun s₇ ⟨hP₇, k₇, h11₇, hh₇⟩ => ?_
    refine WP.mono (more_ok (by omega_arith) (by omega_arith) hP₇ h11₇) fun s₈ ⟨hP₈, k₈, m₈, h11₈, r0₈⟩ =>
      ⟨hP₈, ((k₆.trans k₇).trans k₈).mono (by decide), ⟨h11₈, by omega_arith, by rw [m₈]; exact hh₇⟩, r0₈⟩

/-! ## The coefficients of a polynomial -/

/-- The coefficients of polynomial `i`, from the index `first` up to `bound`. -/
theorem coefs_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s) (h11 : s.gpr .t1 = BitVec.ofNat 64 first)
    (hh : HArr s.mem (uH s₀) (uk s₀) hA) :
    WP isa hbuCoefs s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧
      SRel s₀ (optFold (huStep (uYs s₀) i first) (List.range (bound - first)) (hA, first)) s' := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuCoefs
  refine WP.seq (WP.mono (more_ok (by omega_arith) (by omega_arith) hP h11) fun s₁ ⟨hP₁, k₁, m₁, h11₁, r0₁⟩ => ?_)
  refine WP.ite _ (eval_lt_zero r0₁) (fun hge => ?_) (fun hlt => ?_)
  · -- `first = bound`: nothing.
    have e : bound - first = 0 := by have := of_decide_eq_true hge; omega_arith
    rw [e]
    exact WP.block_nil ⟨hP₁, k₁, h11₁, by omega_arith, by rw [m₁]; exact hh⟩
  have hlt : first < bound := by have := of_decide_eq_false hlt; omega_arith
  have F1 : optFold (huStep (uYs s₀) i first) (List.range 1) (hA, first) =
      some (huSet i ((uYs s₀).getD first 0).toNat hA, first + 1) := by
    simp only [List.range_one, optFold, huStep, gt_iff_lt, Nat.lt_irrefl, false_and, ↓reduceIte, Option.bind_some]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (set_ok hp hi (hA := hA) (by omega_arith) hP₁ h11₁ (by rw [m₁]; exact hh)) fun s₂ ⟨hP₂, k₂, h11₂, hh₂⟩ =>
    WP.mono (more_ok (by omega_arith) (by omega_arith) hP₂ h11₂) fun s₃ ⟨hP₃, k₃, m₃, h11₃, r0₃⟩ => ?_
  refine WP.ite _ (eval_lt_zero r0₃) (fun hge => ?_) (fun hlt' => ?_)
  · -- `first + 1 = bound`.
    have e : bound - first = 1 := by have := of_decide_eq_true hge; omega_arith
    rw [e, F1]
    exact WP.block_nil ⟨hP₃, ((k₁.trans k₂).trans k₃).mono (by decide), h11₃, by omega_arith, by rw [m₃]; exact hh₂⟩
  have hlt' : first + 1 < bound := by have := of_decide_eq_false hlt'; omega_arith
  -- The loop: after `t ≥ 1` coefficients, the state of the spec's fold.
  refine WP.loop (M := isa) (fun m s' => ∃ t, 1 ≤ t ∧ first + t < bound ∧ m = bound - first - t ∧
      ∃ hA' : Array (Vector Bool n), optFold (huStep (uYs s₀) i first) (List.range t) (hA, first) = some (hA', first + t) ∧
        PCom s₀ i bound s' ∧ Keep cRegs s s' ∧ s'.gpr .t1 = BitVec.ofNat 64 (first + t) ∧
        HArr s'.mem (uH s₀) (uk s₀) hA')
    (fun m s' ⟨t, ht1, htb, hm, hA', hF, hP', k', h11', hh'⟩ => ?_) _ s₃
    ⟨1, Nat.le_refl _, hlt', rfl, _, F1, hP₃, ((k₁.trans k₂).trans k₃).mono (by decide), h11₃, by rw [m₃]; exact hh₂⟩
  refine WP.mono (next_ok hp hi (first := first) (by omega_arith) htb hbω hP' h11' hh') fun s₄ ⟨hP₄, k₄, hS, r0₄⟩ => ?_
  have hF1 : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA, first) =
      huStep (uYs s₀) i first (hA', first + t) 0 := by
    rw [optFold_range_succ, hF]; rfl
  have k₄' : Keep cRegs s s₄ := (k'.trans k₄).mono (by decide)
  cases hst : huStep (uYs s₀) i first (hA', first + t) 0 with
  | none =>
    rw [hst] at hS r0₄
    refine .inl ⟨by rw [eval_lt_nonzero r0₄]; simp only [ixOf]; exact congrArg some (decide_eq_false (by omega_arith)),
      hP₄, k₄', ?_⟩
    rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega_arith) (by rw [hF1, hst])]
    exact hS
  | some st =>
    obtain ⟨hA'', idx''⟩ := st
    have e := huStep_idx hst
    simp only at e
    rw [hst] at hS r0₄
    simp only [ixOf] at r0₄
    by_cases hc : idx'' < bound
    · exact .inr ⟨by rw [eval_lt_nonzero r0₄]; exact congrArg some (decide_eq_true hc), _, by omega_arith,
        t + 1, by omega_arith, by omega_arith, rfl, hA'', by rw [hF1, hst, e]; rfl, hP₄, k₄', by rw [hS.1, e]; rfl, hS.2.2⟩
    · refine .inl ⟨by rw [eval_lt_nonzero r0₄]; exact congrArg some (decide_eq_false hc), hP₄, k₄', ?_⟩
      rw [show bound - first = t + 1 by omega_arith, hF1, hst]
      exact hS

end

/-! ## The whole function

The polynomials (`upoly_ok`: one of them is `huPoly` of the spec, or nothing
once a check failed), the trailing bytes (`trail_ok`: `huTrail`), the return
value, and the whole function (`correct`), from the steps above.
-/

/-- The spec's state after `i` polynomials. -/
abbrev uSt (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (uω s₀) (uYs s₀)) (List.range i) (Array.replicate (uk s₀) noHint, 0)

/-- Before polynomial `i`. -/
structure OInv (s₀ : State) (i : Nat) (s : State) : Prop where
  com : UCom s₀ s
  a3 : s.gpr .a3 = uH s₀ + BitVec.ofNat 64 (1024 * i)
  a7 : s.gpr .a7 = uY s₀ + BitVec.ofNat 64 (uω s₀ + i)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (uk s₀ - i)
  st : SRel s₀ (uSt s₀ i) s

theorem fail_ok {s : State} :
    WP isa hbuFail s fun s' => Keep [.t1] s s' ∧ s'.mem = s.mem ∧ s'.gpr .t1 = BitVec.ofNat 64 256 :=
  Steps.wp_li (by decide) fun _ o => WP.block_nil ⟨o.keepH, o.mem, o.gpr⟩

/-- `ltBit t x y` of numbers. -/
theorem lt_ok {t x y : Reg} {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) {s : State}
    (hx : s.gpr x = BitVec.ofNat 64 a) (hy : s.gpr y = BitVec.ofNat 64 b) :
    WP isa (.block (ltBit t x y)) s fun s' => Keep [t] s s' ∧ s'.mem = s.mem ∧
      s'.gpr t = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  unfold ltBit
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => WP.block_nil ⟨(o₁.keepH.trans o₂.keepH).mono (by simp),
    by rw [o₂.mem, o₁.mem], by rw [o₂.gpr, o₁.gpr, hx, hy, ltBit_eq ha hb]⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- What a polynomial leaves before the pointers move on. -/
def PPost (s₀ : State) (i : Nat) (s s' : State) : Prop :=
  Keep [.t0, .a5, .a6, .t1] s s' ∧ UCom s₀ s' ∧ SRel s₀ (uSt s₀ (i + 1)) s'

omit hp in
theorem uSt_succ (i : Nat) : uSt s₀ (i + 1) = (uSt s₀ i).bind fun st => huPoly (uω s₀) (uYs s₀) st i :=
  optFold_range_succ _ _ _

/-- Polynomial `i`, unless a check failed. -/
theorem poly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa hbuPoly s (PPost s₀ i s) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have hS := hI.st
  have hsucc := uSt_succ (s₀ := s₀) i
  unfold hbuPoly
  cases hst : uSt s₀ i with
  | none =>
    rw [hst] at hS hsucc
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := 256) (by omega_arith) (by decide) hI.com.a2 hS)
      fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₁) (fun h => absurd (of_decide_eq_true h) (by omega_arith)) fun _ =>
      WP.block_nil ⟨k₁.mono (by decide), hI.com.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _), ?_⟩
    rw [hsucc]; show s₁.gpr .t1 = _; rw [k₁.gpr (by decide), hS]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hst] at hS hsucc
    obtain ⟨h11, hidx, hh⟩ := hS
    have hP : huPoly (uω s₀) (uYs s₀) (hA, idx) i = if ((uYs s₀).getD (uω s₀ + i) 0).toNat < idx ∨
        ((uYs s₀).getD (uω s₀ + i) 0).toNat > uω s₀ then none else
        optFold (huStep (uYs s₀) i idx) (List.range (((uYs s₀).getD (uω s₀ + i) 0).toNat - idx)) (hA, idx) := rfl
    simp only [Option.bind_some] at hsucc
    rw [hP] at hsucc
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := idx) (by omega_arith) (by omega_arith) hI.com.a2 h11)
      fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₁) (fun _ => ?_) fun h => absurd (of_decide_eq_false h) (by omega_arith)
    obtain ⟨bound, hbound⟩ : ∃ b, ((uYs s₀).getD (uω s₀ + i) 0).toNat = b := ⟨_, rfl⟩
    rw [hbound] at hsucc
    have hb : bound < 256 := hbound ▸ ((uYs s₀).getD (uω s₀ + i) 0).isLt
    have hc₁ : UCom s₀ s₁ := hI.com.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine wp_lbz (a := uY s₀ + BitVec.ofNat 64 (uω s₀ + i)) (by decide) (by decide)
      (by rw [k₁.gpr (by decide), hI.a7, add0]) (yIn hp hc₁ (by omega_arith)) fun s₂ o₂ => WP.block_nil ?_
    have hc₂ : UCom s₀ s₂ := hc₁.of o₂.keepH (by decide) (by decide) (by rw [o₂.mem]; exact Frame.refl _ _)
    have r8 : s₂.gpr .a5 = BitVec.ofNat 64 bound := by rw [o₂.gpr, yByte hp hc₁ (by omega_arith), byte_ofNat, hbound]
    have h11₂ : s₂.gpr .t1 = BitVec.ofNat 64 idx := by rw [o₂.other _ (by decide), k₁.gpr (by decide), h11]
    refine WP.mono (lt_ok (by omega_arith) (by omega_arith) r8 h11₂) fun s₃ ⟨k₃, m₃, r0₃⟩ => ?_
    have k₃' : Keep [.t0, .a5, .a6, .t1] s s₃ := ((k₁.trans o₂.keepH).trans k₃).mono (by decide)
    have m₃' : s₃.mem = s.mem := by rw [m₃, o₂.mem, m₁]
    have hc₃ : UCom s₀ s₃ := hc₂.of k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
    have fail : ∀ {s'}, Keep [.t0, .t1] s₃ s' → s'.mem = s₃.mem → s'.gpr .t1 = BitVec.ofNat 64 256 →
        bound < idx ∨ bound > uω s₀ → PPost s₀ i s s' := fun k' m' h11' hc => by
      refine ⟨(k₃'.trans k').mono (by decide), hc₃.of k' (by decide) (by decide) (by rw [m']; exact Frame.refl _ _),
        ?_⟩
      rw [hsucc, ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact h11'
    refine WP.ite _ (eval_lt_zero r0₃) (fun hge => ?_)
      fun hlt => WP.mono fail_ok fun s' ⟨k', m', h11'⟩ => fail (k'.mono (by decide)) m' h11' (.inl (by have := of_decide_eq_false hlt; omega_arith))
    have hge : idx ≤ bound := of_decide_eq_true hge
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := bound) (by omega_arith) (by omega_arith) hc₃.a2
      (by rw [k₃.gpr (by decide), r8])) fun s₄ ⟨k₄, m₄, r0₄⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₄) (fun hle => ?_)
      fun hgt => WP.mono fail_ok fun s' ⟨k', m', h11'⟩ => fail (s' := s') ((k₄.trans k').mono (by decide))
        (by rw [m', m₄]) h11' (.inr (by have := of_decide_eq_false hgt; omega_arith))
    have hle : bound ≤ uω s₀ := of_decide_eq_true hle
    have hP₄ : PCom s₀ i bound s₄ := ⟨hc₃.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _),
      by rw [k₄.gpr (by decide), k₃.gpr (by decide), o₂.other _ (by decide), k₁.gpr (by decide), hI.a3],
      by rw [k₄.gpr (by decide), k₃.gpr (by decide), r8]⟩
    refine WP.mono (coefs_ok hp hi (hA := hA) hge hle hP₄ (by rw [k₄.gpr (by decide), k₃.gpr (by decide), h11₂])
      (by rw [m₄, m₃']; exact hh))
      fun s' ⟨hP', k', hS'⟩ => ⟨((k₃'.trans k₄).trans k').mono (by decide), hP'.com, ?_⟩
    rw [hsucc, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]; exact hS'

omit hp in
theorem SRel.of {st : Option (Array (Vector Bool n) × Nat)} {s s' : State} (h : SRel s₀ st s)
    (h11 : s'.gpr .t1 = s.gpr .t1) (hm : s'.mem = s.mem) : SRel s₀ st s' := by
  cases st with
  | none => exact h11.trans h
  | some st => obtain ⟨hA, idx⟩ := st; exact ⟨h11.trans h.1, h.2.1, by rw [hm]; exact h.2.2⟩

/-- Polynomial `i`, and the pointers and the count moved on. -/
theorem upoly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa (.seq hbuPoly (.block [.addi .a7 .a7 1, .addi .a3 .a3 1024, .addi .t2 .t2 (-1)])) s fun s' =>
      OInv s₀ (i + 1) s' ∧ (s'.gpr .t2 != 0) = decide (i + 1 ≠ uk s₀) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  refine WP.seq (WP.mono (poly_ok hp hi hI) fun s₁ ⟨k₁, hc₁, hS₁⟩ => ?_)
  refine Steps.wp_addi (by decide) fun s₂ o₂ => Steps.wp_addi (by decide) fun s₃ o₃ =>
    Steps.wp_subi (by decide) fun s₄ o₄ => WP.block_nil ?_
  have k₄ := (o₂.keepH.trans o₃.keepH).trans o₄.keepH
  have m₄ : s₄.mem = s₁.mem := by rw [o₄.mem, o₃.mem, o₂.mem]
  have c12 : s₄.gpr .t2 = BitVec.ofNat 64 (uk s₀ - (i + 1)) := by
    rw [o₄.gpr, o₃.other _ (by decide), o₂.other _ (by decide), k₁.gpr (by decide), hI.t2, count_sub hi]
  refine ⟨⟨hc₁.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _), ?_, ?_, c12,
    hS₁.of (k₄.gpr (by decide)) m₄⟩, by rw [c12]; exact count_nz hi (by omega_arith)⟩
  · rw [o₄.other _ (by decide), o₃.gpr, o₂.other _ (by decide), k₁.gpr (by decide), hI.a3, ptr_add, Nat.mul_succ]
  · rw [o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr, k₁.gpr (by decide), hI.a7, ptr_add,
      Nat.add_assoc]

/-- The polynomials, from the state after zeroing `h`. -/
theorem main_ok {s : State} (hz : ZPost s₀ s) : WP isa hbuMain s (OInv s₀ (uk s₀)) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuMain
  refine WP.seq (Steps.wp_add fun s₁ o₁ => WP.block_nil ?_)
  refine wp_loop_nz (OInv s₀) (N := uk s₀) (by omega_arith) (fun i hi s hI => upoly_ok hp hi hI) (fun _ h => h)
    ⟨hz.com.of o₁.keepH (by decide) (by decide) (by rw [o₁.mem]; exact Frame.refl _ _),
      by rw [o₁.other _ (by decide), hz.a3, Nat.mul_zero]; exact (add0 _).symm,
      by rw [o₁.gpr, hz.com.a0, hz.com.a2, Nat.add_zero],
      by rw [o₁.other _ (by decide), hz.t2, Nat.sub_zero],
      ⟨by rw [o₁.other _ (by decide), hz.t1]; rfl, Nat.zero_le _, by rw [o₁.mem]; exact harr_zero hz.zero⟩⟩

/-! ## The bytes after the last index -/

/-- Once a check failed, nothing. -/
theorem trail_none {s : State} (hc : UCom s₀ s) (h11 : s.gpr .t1 = BitVec.ofNat 64 256) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .t1 = BitVec.ofNat 64 256 := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (lt_ok (by decide) (by omega_arith) h11 hc.a2) fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
  refine WP.ite _ (eval_lt_zero r0₁) (fun _ => WP.block_nil ⟨hc.of k₁ (by decide) (by decide)
    (by rw [m₁]; exact Frame.refl _ _), m₁, by rw [k₁.gpr (by decide), h11]⟩)
    fun h => absurd (of_decide_eq_false h) (by omega_arith)

/-- The bytes from the index `idx` up to `ω` are zero, or the index becomes 256. -/
theorem trail_some {idx : Nat} (hidx : idx ≤ uω s₀) {s : State} (hc : UCom s₀ s)
    (h11 : s.gpr .t1 = BitVec.ofNat 64 idx) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .t1 = BitVec.ofNat 64
        (if (optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) ()).isSome then uω s₀ else 256) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (lt_ok (by omega_arith) (by omega_arith) h11 hc.a2) fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
  have hc₁ : UCom s₀ s₁ := hc.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
  refine WP.ite _ (eval_lt_zero r0₁) (fun hge => ?_) (fun hlt => ?_)
  · -- `idx = ω`: nothing.
    have e : uω s₀ - idx = 0 := by have := of_decide_eq_true hge; omega_arith
    refine WP.block_nil ⟨hc₁, m₁, ?_⟩
    rw [k₁.gpr (by decide), h11, e]
    simp only [List.range'_zero, optFold, Option.isSome_some, ↓reduceIte]
    congr 1; omega_arith
  have hlt : idx < uω s₀ := by have := of_decide_eq_false hlt; omega_arith
  refine WP.loop (M := isa) (fun m s' => ∃ u, m = uω s₀ - idx - u ∧ idx + u < uω s₀ ∧
      optFold (huTrail (uYs s₀)) (List.range' idx u) () = some () ∧ s'.gpr .t1 = BitVec.ofNat 64 (idx + u) ∧
      UCom s₀ s' ∧ s'.mem = s.mem)
    (fun m s' ⟨u, hm, hu, hF, h11', hc', hm'⟩ => ?_) _ s₁
    ⟨0, rfl, by omega_arith, rfl, by rw [k₁.gpr (by decide), h11]; rfl, hc₁, m₁⟩
  have hF1 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = huTrail (uYs s₀) () (idx + u) := by
    rw [optFold_range'_succ, hF]; rfl
  refine WP.seq (Steps.wp_add fun s₂ o₂ => wp_lbz (a := uY s₀ + BitVec.ofNat 64 (idx + u)) (by decide) (by decide)
    (by rw [o₂.gpr, hc'.a0, h11', add0]) (by rw [o₂.rd, o₂.wr]; exact yIn hp hc' (by omega_arith)) fun s₃ o₃ =>
    WP.block_nil ?_)
  have k₃ := o₂.keepH.trans o₃.keepH
  have m₃ : s₃.mem = s'.mem := by rw [o₃.mem, o₂.mem]
  have hc₃ : UCom s₀ s₃ := hc'.of k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
  have r9 : s₃.gpr .a6 = BitVec.ofNat 64 ((uYs s₀).getD (idx + u) 0).toNat := by
    rw [o₃.gpr, o₂.mem, yByte hp hc' (by omega_arith), byte_ofNat]
  have hyb := ((uYs s₀).getD (idx + u) 0).isLt
  refine WP.seq (WP.ite _ (eval_zero_ofNat s₃ .a6 (by omega_arith) r9) (fun hz => ?_) (fun hnz => ?_))
  · -- A zero byte: next.
    have hz : (uYs s₀).getD (idx + u) 0 = 0 := by
      apply BitVec.eq_of_toNat_eq; exact of_decide_eq_true hz
    have hF2 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = some () := by
      rw [hF1]; simp only [huTrail, hz, ne_eq, not_true_eq_false, ↓reduceIte]
    refine Steps.wp_addi (by decide) fun s₄ o₄ => WP.block_nil ?_
    have h11₄ : s₄.gpr .t1 = BitVec.ofNat 64 (idx + (u + 1)) := by
      rw [o₄.gpr, k₃.gpr (by decide), h11', ofNat_succ, Nat.add_assoc]
    have hc₄ : UCom s₀ s₄ := hc₃.of o₄.keepH (by decide) (by decide) (by rw [o₄.mem]; exact Frame.refl _ _)
    refine WP.mono (lt_ok (by omega_arith) (by omega_arith) h11₄ hc₄.a2) fun s₅ ⟨k₅, m₅, r0₅⟩ => ?_
    have hc₅ : UCom s₀ s₅ := hc₄.of k₅ (by decide) (by decide) (by rw [m₅]; exact Frame.refl _ _)
    have h11₅ : s₅.gpr .t1 = BitVec.ofNat 64 (idx + (u + 1)) := by rw [k₅.gpr (by decide), h11₄]
    have hm₅ : s₅.mem = s.mem := by rw [m₅, o₄.mem, m₃, hm']
    by_cases e : idx + (u + 1) < uω s₀
    · exact .inr ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_true e), _, by omega_arith, u + 1, rfl, e,
        hF2, h11₅, hc₅, hm₅⟩
    · refine .inl ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_false e), hc₅, hm₅, ?_⟩
      rw [show uω s₀ - idx = u + 1 by omega_arith, hF2, h11₅]
      simp only [Option.isSome_some, ↓reduceIte]
      congr 1; omega_arith
  · -- A nonzero byte: fail.
    have hnz : (uYs s₀).getD (idx + u) 0 ≠ 0 := fun e => by
      have := of_decide_eq_false hnz; rw [e] at this; exact this rfl
    have hn : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () = none :=
      optFold_range'_none _ _ (show u + 1 ≤ uω s₀ - idx by omega_arith)
        (by rw [hF1, huTrail, ite_eq_left_of_eq_true _ _ (eq_true hnz)])
    refine WP.mono fail_ok fun s₄ ⟨k₄, m₄, h11₄⟩ => ?_
    have hc₄ : UCom s₀ s₄ := hc₃.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _)
    refine WP.mono (lt_ok (by decide) (by omega_arith) h11₄ hc₄.a2) fun s₅ ⟨k₅, m₅, r0₅⟩ => ?_
    refine .inl ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_false (by omega_arith)),
      hc₄.of k₅ (by decide) (by decide) (by rw [m₅]; exact Frame.refl _ _), by rw [m₅, m₄, m₃, hm'], ?_⟩
    rw [k₅.gpr (by decide), h11₄, hn]
    rfl

/-! ## The return value -/

omit hp in
theorem ret_ok {x ω : Nat} (hx : x ≤ 256) (hω : ω ≤ 80) {s : State} (h11 : s.gpr .t1 = BitVec.ofNat 64 x)
    (h5 : s.gpr .a2 = BitVec.ofNat 64 ω) :
    WP isa (.block hbuRet) s fun s' => s'.mem = s.mem ∧
      (s'.gpr .a0).setWidth 32 = if x ≤ ω then 1 else 0 := by
  unfold hbuRet
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => Steps.wp_li (by decide) fun s₃ o₃ =>
    Steps.wp_sub fun s₄ o₄ => WP.block_nil ⟨by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem], ?_⟩
  rw [o₄.gpr, o₃.gpr, o₃.other _ (by decide), o₂.gpr, o₁.gpr, h5, h11, ltBit_eq (by omega_arith) (by omega_arith)]
  by_cases e : x ≤ ω
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true e)]; rfl
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false e)]; rfl

/-! ## The function -/

/-- The registers `hintBitUnpack` writes. -/
abbrev hbuRegs : List Reg := [.t0, .a0, .a2, .a3, .a5, .a6, .a7, .t1, .t2]

/-- The postcondition, as `sig_post` states it. -/
def UPost (s₀ s' : State) : Prop :=
  match hintBitUnpack (uω s₀) (uk s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)) with
  | some hint => (s'.gpr .a0).setWidth 32 = 1 ∧ HintIs s'.mem (uH s₀) (uk s₀) hint
  | none => (s'.gpr .a0).setWidth 32 = 0

theorem correct : WP isa Impl.MlDsa.RISCV64.Pack.hintBitUnpack s₀ fun s' => UPost s₀ s' ∧ Keep hbuRegs s₀ s' := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  refine WP.keep hbuRegs ?_ (by decide +kernel)
  unfold Impl.MlDsa.RISCV64.Pack.hintBitUnpack
  refine WP.seq (WP.mono (zero_ok hp) fun s₁ hz => WP.seq (WP.mono (main_ok hp hz) fun s₂ hI => ?_))
  have hS := hI.st
  cases hst : uSt s₀ (uk s₀) with
  | none =>
    rw [hst] at hS
    have e : optFold (huPoly (uω s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range (uk s₀))
        (Array.replicate (uk s₀) noHint, 0) = none := hst
    refine WP.seq (WP.mono (trail_none hp hI.com hS) fun s₃ ⟨hc₃, m₃, h11₃⟩ =>
      WP.mono (ret_ok (by decide) hω80 h11₃ hc₃.a2) fun s₄ ⟨_, r3₄⟩ => ?_)
    simp only [UPost, hintBitUnpack_eq, e]
    rw [r3₄, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hst] at hS
    obtain ⟨h11, hidx, hh⟩ := hS
    have e : optFold (huPoly (uω s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range (uk s₀))
        (Array.replicate (uk s₀) noHint, 0) = some (hA, idx) := hst
    refine WP.seq (WP.mono (trail_some hp hidx hI.com h11) fun s₃ ⟨hc₃, m₃, h11₃⟩ =>
      WP.mono (ret_ok (by split <;> omega_arith) hω80 h11₃ hc₃.a2) fun s₄ ⟨m₄, r3₄⟩ => ?_)
    cases hT : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () with
    | none =>
      have eT : optFold (huTrail (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range' idx (uω s₀ - idx)) () =
        none := hT
      simp only [UPost, hintBitUnpack_eq, e, eT, Option.map_none]
      rw [hT] at r3₄
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at r3₄
      rw [r3₄, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    | some u =>
      have eT : optFold (huTrail (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range' idx (uω s₀ - idx)) () =
        some u := hT
      simp only [UPost, hintBitUnpack_eq, e, eT, Option.map_some]
      rw [hT] at r3₄
      simp only [Option.isSome_some, ↓reduceIte] at r3₄
      refine ⟨by rw [r3₄, ite_eq_left_of_eq_true _ _ (eq_true (Nat.le_refl _))], ?_⟩
      rw [m₄, m₃]
      exact harr_hintIs hh

end

end VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack
