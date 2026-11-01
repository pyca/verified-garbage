module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintPack
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

end VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack
