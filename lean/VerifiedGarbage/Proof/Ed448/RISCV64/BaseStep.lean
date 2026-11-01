module

import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

/-!
# Ed448 on RISCV64: one iteration of base-point multiplication

An iteration with the counter `c` (`h = c - 1` after it) selects `P`: `R` if
`h` is odd, else the base point `Q` (`head_ok`); adds `T = R + P` with X448's
field operations (`addition_ok`); and swaps `T` into `R` if `h` is odd or bit
`h / 2` of the scalar set (`swap_ok`). The point in `R` after the counter
`c` is `Rv k c` (`step_ok`): the point after the top `456 - c / 2` bits
(`ladder2`) for `c` even, and that point doubled for `c` odd (`rv_step`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC BITS X2 Z2 R)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point pointAdd basePoint)
open VG.Proof.Ed448 (ladder2 ladderStep2 ladder2_bit bitAt)

/-- `p` or, if `sw = 1`, `q`. -/
abbrev pick {α : Type} (sw : Nat) (p q : α) : α := VG.Proof.X25519.sel sw p q

theorem pick_X (sw : Nat) (p q : Point) : (pick sw p q).X = pick sw p.X q.X := by
  unfold pick VG.Proof.X25519.sel; split <;> rfl

theorem pick_Y (sw : Nat) (p q : Point) : (pick sw p q).Y = pick sw p.Y q.Y := by
  unfold pick VG.Proof.X25519.sel; split <;> rfl

theorem pick_Z (sw : Nat) (p q : Point) : (pick sw p q).Z = pick sw p.Z q.Z := by
  unfold pick VG.Proof.X25519.sel; split <;> rfl

/-! ## The slots -/

/-- The elements of `R = r`, `P = p` and `d`. -/
def ptV (r p : Point) (q : Nat) : Fe :=
  if q = RX then r.X else if q = RY then r.Y else if q = RZ then r.Z else if q = PX then p.X
  else if q = PY then p.Y else if q = PZ then p.Z else Spec.Ed448.d

/-- The slots of `R` and `d`, between iterations. -/
def RQ : List Nat := [RX, RY, RZ, DK]

/-- With `P`'s, after the selection. -/
def SQ : List Nat := [PZ, PY, PX, RX, RY, RZ, DK]

/-- The base point at `Q`, above the field area. -/
def QOk (b : Addr) (m : Mem) : Prop :=
  FS m b QX = basePoint.X ∧ FS m b QY = basePoint.Y ∧ FS m b QZ = basePoint.Z

/-- The addition but its last operation. -/
def addOps : List FOp :=
  [.mul TA RZ PZ, .mul TY TA TA, .mul TC RX PX, .mul TD RY PY, .mul TZ DK TC, .mul TZ TZ TD,
    .sub TF TY TZ, .add TG TY TZ, .add TH RX RY, .add TX PX PY, .mul TH TH TX, .mul TX TA TF,
    .sub TH TH TC, .sub TH TH TD, .mul TX TX TH, .mul TY TA TG, .sub TH TD TC, .mul TY TY TH]

theorem addition_eq : addition = R64.opsCode addOps (R64.fcode (FOp.mul TZ TF TG)) := rfl

theorem addOps_ok : R64.opsOk addOps SQ = true := by decide

/-- The slots after the addition. -/
def FQ : List Nat := TZ :: outsQ addOps SQ

theorem last_ok : R64.Sep8 TZ (outsQ addOps SQ) = true ∧ TZ + 56 ≤ ACC ∧ TF ∈ outsQ addOps SQ ∧
    TG ∈ outsQ addOps SQ := by decide

/-- The elements after the addition. -/
def addV (r p : Point) : Nat → Fe :=
  upd (runOps addOps (ptV r p)) TZ (runOps addOps (ptV r p) TF * runOps addOps (ptV r p) TG)

theorem addV_vals (r p : Point) :
    addV r p RX = r.X ∧ addV r p RY = r.Y ∧ addV r p RZ = r.Z ∧ addV r p DK = Spec.Ed448.d ∧
      addV r p TX = (pointAdd r p).X ∧ addV r p TY = (pointAdd r p).Y ∧
      addV r p TZ = (pointAdd r p).Z := by
  simp only [addV, addOps, runOps, FOp.out, FOp.val, upd, ptV, pointAdd, RX, RY, RZ, PX, PY, PZ, DK, TX,
    TY, TZ, TA, TC, TD, TF, TG, TH, X2, Z2, R, Nat.reduceEqDiff, ↓reduceIte, and_self]

/-! ## The points -/

/-- The point in `R` while the counter is `c`. -/
def Rv (k c : Nat) : Point :=
  if c % 2 = 0 then ladder2 k (456 - c / 2)
  else pointAdd (ladder2 k (456 - (c + 1) / 2)) (ladder2 k (456 - (c + 1) / 2))

theorem or_one {x : Nat} (hx : x ≤ 1) : x ||| 1 = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;> rfl

theorem bit_le (k t : Nat) : (k >>> t) &&& 1 ≤ 1 := by
  rw [Nat.and_one_is_mod]; omega_arith

/-- An iteration: `R + P`, `P = R` if `h` is odd and the base point if it is
even, kept if `h` is odd or bit `h / 2` set. -/
theorem rv_step (k : Nat) {c : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ 912) :
    pick (((k >>> ((c - 1) / 2)) &&& 1) ||| (c - 1) % 2) (Rv k c)
      (pointAdd (Rv k c) (pick ((c - 1) % 2) basePoint (Rv k c))) = Rv k (c - 1) := by
  have hb := bit_le k ((c - 1) / 2)
  rcases Nat.mod_two_eq_zero_or_one (c - 1) with h0 | h1
  · -- `h` even: the bit.
    have hc : c % 2 = 1 := by omega_arith
    have ht : (c - 1) / 2 < 456 := by omega_arith
    have e1 : (c + 1) / 2 = (c - 1) / 2 + 1 := by omega_arith
    rw [h0, Nat.or_zero, Rv, Rv, ite_eq_right (by omega_arith), ite_eq_left h0, e1, ladder2_bit k ht]
    simp only [pick, VG.Proof.X25519.sel, ladderStep2, bitAt, Nat.reduceEqDiff, ↓reduceIte]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h <;> simp [h]
  · -- `h` odd: the doubling.
    have hc : c % 2 = 0 := by omega_arith
    have e1 : (c - 1 + 1) / 2 = c / 2 := by omega_arith
    rw [h1, or_one hb, Rv, Rv, ite_eq_left hc, ite_eq_right (by omega_arith), e1]
    rfl

/-! ## The selection -/

section
variable {b : Addr} {sL : State}

theorem par_shift (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x <<< 63) >>> 63 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  have := bit_shift (BitVec.ofNat 64 x) (j := 0) (by decide)
  rw [Nat.sub_zero, Nat.shiftRight_zero, toNat_imm hx, Nat.and_one_is_mod] at this
  rw [this, toNat_imm (by omega_arith)]

theorem head_ok (hQ : QOk b sL.mem) {c : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ 912) {r : Point} {a : BitVec 64}
    {s : State} (h : R64.Cur b sL a (BitVec.ofNat 64 c) RQ (ptV r r) s) :
    WP isa (.block (([.addi .t1 .t1 (-1)] : List Instr) ++ baseSelect)) s
      (R64.Cur b sL (BitVec.ofNat 64 ((c - 1) % 2)) (BitVec.ofNat 64 (c - 1)) SQ
        (ptV r (pick ((c - 1) % 2) basePoint r))) := by
  have hc := h.ctx
  have hA := ACC_eq
  have hsw : (c - 1) % 2 ≤ 1 := by omega_arith
  simp only [baseSelect, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_subi (by decide) fun s1 u1 => ?_
  have e12 : s1.gpr .t1 = BitVec.ofNat 64 (c - 1) := by
    rw [u1.gpr, h.t1, ofNat_sub_one hc1 (by omega_arith)]
  refine wp_sll (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  have e4 : s3.gpr .a1 = BitVec.ofNat 64 ((c - 1) % 2) := by
    rw [u3.gpr, u2.gpr, e12, par_shift _ (by omega_arith)]
  refine wp_addi (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => wp_sub fun s6 u6 => ?_
  have e0 : s6.gpr .t2 = BitVec.ofNat 64 ((c - 1) % 2) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, e4, BitVec.add_zero]
  have e11 : s6.gpr .t0 = 0 - BitVec.ofNat 64 ((c - 1) % 2) := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.other _ (by decide), e4]; rfl
  have hr6 : Rest [.t2, .a1, .t0, .t1] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hc6 : Ctx b s6 := hc.of_rest hr6 (by decide)
  have hf6 : Frame [FA b] sL.mem s6.mem := by rw [hm6]; exact h.stp.frame
  have hS6 : SlotsOk s6.mem b RQ (ptV r r) := by rw [hm6]; exact h.slots
  have q6 : QOk b s6.mem := by
    obtain ⟨h1, h2, h3⟩ := hQ
    exact ⟨by rw [fs_above hf6 (by decide) (by decide), h1], by rw [fs_above hf6 (by decide) (by decide), h2],
      by rw [fs_above hf6 (by decide) (by decide), h3]⟩
  refine WP.append (selS (o := PX) (q := QX) (r := RX) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc6 hsw e11 hS6 q6.1) fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (selS (o := PY) (q := QY) (r := RY) (x := basePoint.Y) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc7 hsw (by rw [hr7.gpr _ (by decide), e11]) hS7
    (by rw [fs_above hf7 (by decide) (by decide)]; exact q6.2.1)) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  have hc8 : Ctx b s8 := hc7.of_rest hr8 (by decide)
  refine WP.mono (selS (o := PZ) (q := QZ) (r := RZ) (x := basePoint.Z) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc8 hsw (by rw [hr8.gpr _ (by decide), hr7.gpr _ (by decide), e11]) hS8
    (by rw [fs_above hf8 (by decide) (by decide), fs_above hf7 (by decide) (by decide)]; exact q6.2.2))
    fun s9 ⟨hr9, hf9, hS9⟩ => ?_
  have hr9' : Rest [.t2, .a1, .a2, .a4, .t0, .t1] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (hr9.mono (by decide))))
  refine ⟨hc.of_rest hr9' (by decide), h.stp.trans ⟨hr9'.mono (by decide), ?_⟩, ?_, ?_, ?_⟩
  · rw [← hm6]; exact hf7.trans (hf8.trans hf9)
  · rw [hr9.gpr _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), e0]
  · rw [hr9.gpr _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e12]
  · refine (hS9.mono (by decide)).congr fun q hq => ?_
    simp only [SQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd, ptV, pick_X, pick_Y, pick_Z, RX, RY, RZ, PX, PY, PZ, DK, X2, Z2,
        Nat.reduceEqDiff, ↓reduceIte] <;> rfl

/-! ## The swap -/

theorem ofNat_or {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 y = BitVec.ofNat 64 (x ||| y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, toNat_imm hx, toNat_imm hy, toNat_imm (Nat.or_lt_two_pow hx hy)]

theorem half_shift (x : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 1 = BitVec.ofNat 64 (x / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shr, toNat_imm hx, toNat_imm (by omega_arith), Nat.pow_one]

theorem wp_or {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- The mask of an iteration: the parity or the bit `h / 2`. -/
abbrev swb (k h : Nat) : Nat := ((k >>> (h / 2)) &&& 1) ||| h % 2

theorem swap_ok {k : Nat} (hbits : Bits b k sL.mem) {h : Nat} (hh : h < 912) {r p : Point} {s : State}
    (hcur : R64.Cur b sL (BitVec.ofNat 64 (h % 2)) (BitVec.ofNat 64 h) FQ (addV r p) s) :
    WP isa (.block baseSwap) s (R64.Cur b sL (BitVec.ofNat 64 (h % 2)) (BitVec.ofNat 64 h) FQ
      (swapV RZ TZ (swb k h) (swapV RY TY (swb k h) (swapV RX TX (swb k h) (addV r p))))) := by
  have hc := hcur.ctx
  have hB : BITS = 1064 := rfl
  have hA := ACC_eq
  have hb := bit_le k (h / 2)
  have hsw : swb k h ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with e | e <;>
      rcases Nat.mod_two_eq_zero_or_one h with e' | e' <;> simp [swb, e, e']
  simp only [baseSwap, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_srl (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e2 : s2.gpr .a1 = b + BitVec.ofNat 64 (h / 2) := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), hc.a3, hcur.t1, half_shift _ (by omega_arith)]
  refine wp_lbz (a := b + BitVec.ofNat 64 (BITS + h / 2)) (by decide)
    (by rw [e2, Offset.add_add, Nat.add_comm])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s3 u3 => ?_
  have e3 : s3.gpr .a1 = BitVec.ofNat 64 ((k >>> (h / 2)) &&& 1) := by
    rw [u3.gpr, u2.mem, u1.mem, byte_above hcur.stp.frame (by omega_using [hA, hB]) (by omega_using [hh, hB]),
      hbits _ (by omega_arith), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  refine wp_or fun s4 u4 => wp_li (by decide) fun s5 u5 => wp_sub fun s6 u6 => ?_
  have e11 : s6.gpr .t0 = 0 - BitVec.ofNat 64 (swb k h) := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.gpr, e3, u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), hcur.t2, ofNat_or (by omega_arith) (by omega_arith)]; rfl
  have hr6 : Rest [.a1, .t0] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hc6 : Ctx b s6 := hc.of_rest hr6 (by decide)
  have hS6 : SlotsOk s6.mem b FQ (addV r p) := by rw [hm6]; exact hcur.slots
  refine WP.append (R64.cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc6 hsw e11 hS6) fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (R64.cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc7 hsw (by rw [hr7.gpr _ (by decide), e11]) hS7) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  have hc8 : Ctx b s8 := hc7.of_rest hr8 (by decide)
  refine WP.mono (R64.cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc8 hsw (by rw [hr8.gpr _ (by decide), hr7.gpr _ (by decide), e11]) hS8) fun s9 ⟨hr9, hf9, hS9⟩ => ?_
  have hr9' : Rest [.a1, .a2, .a4, .a5, .t0] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (hr9.mono (by decide))))
  exact ⟨hc.of_rest hr9' (by decide), hcur.stp.trans ⟨hr9'.mono (by decide), by
      rw [← hm6]; exact hf7.trans (hf8.trans hf9)⟩,
    by rw [hr9'.gpr _ (by decide), hcur.t2], by rw [hr9'.gpr _ (by decide), hcur.t1], hS9⟩

/-! ## An iteration -/

/-- The loop invariant from `sL` with the counter `c`. -/
structure LoopInv (b : Addr) (k : Nat) (sL : State) (c : Nat) (s : State) : Prop where
  cur : R64.Cur b sL (s.gpr .t2) (BitVec.ofNat 64 c) RQ (ptV (Rv k c) (Rv k c)) s

theorem baseStep_eq : baseStep =
    .seq (.block (([.addi .t1 .t1 (-1)] : List Instr) ++ baseSelect))
      (.seq (R64.opsCode addOps (R64.fcode (FOp.mul TZ TF TG))) (.block baseSwap)) := rfl

theorem step_ok {k : Nat} (hbits : Bits b k sL.mem) (hQ : QOk b sL.mem) {c : Nat} (hc1 : 1 ≤ c)
    (hc2 : c ≤ 912) {s : State} (h : LoopInv b k sL c s) :
    WP isa baseStep s fun s' => LoopInv b k sL (c - 1) s' ∧ (s'.gpr .t1 != 0) = decide (c - 1 ≠ 0) := by
  rw [baseStep_eq]
  obtain ⟨o1, o2, o3, o4⟩ := last_ok
  refine WP.seq (WP.mono (head_ok hQ hc1 hc2 h.cur) fun s1 h1 => WP.seq
    (R64.ops_ok addOps SQ _ s1 addOps_ok h1 fun s2 h2 => WP.mono (R64.op_ok (.mul TZ TF TG) o1 o2 o3 o4 h2)
      fun s3 h3 => WP.mono (swap_ok (r := Rv k c) (p := pick ((c - 1) % 2) basePoint (Rv k c)) hbits
        (by omega_arith) h3) fun s4 h4 => ?_))
  refine ⟨⟨⟨h4.ctx, h4.stp, rfl, ?_, ?_⟩⟩, ?_⟩
  · exact h4.t1
  · refine (h4.slots.mono (by decide)).congr fun q hq => ?_
    obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := addV_vals (Rv k c) (pick ((c - 1) % 2) basePoint (Rv k c))
    rw [← rv_step k hc1 hc2]
    simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp only [swapV, ptV, pick_X, pick_Y, pick_Z, RX, RY, RZ, PX, PY, PZ, DK, TX, TY, TZ, X2, Z2,
        Nat.reduceEqDiff, ↓reduceIte] at v1 v2 v3 v4 v5 v6 v7 ⊢ <;>
      simp only [v1, v2, v3, v4, v5, v6, v7]
  · rw [h4.t1, ofNat_ne_zero (by omega_arith)]


theorem rv_912 (k : Nat) : Rv k 912 = Spec.Ed448.identity := by
  simp only [Rv, Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub, ↓reduceIte]; rfl

theorem rv_0 (k : Nat) : Rv k 0 = ladder2 k 456 := by
  simp only [Rv, Nat.zero_mod, Nat.zero_div, Nat.sub_zero, ↓reduceIte]

/-- The loop, from `R` the neutral point: `R = ladder2 k 456`. -/
theorem baseLoop_ok {k : Nat} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem) (hQ : QOk b s.mem)
    (hS : SlotsOk s.mem b RQ (ptV Spec.Ed448.identity Spec.Ed448.identity)) :
    WP isa baseLoop s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b RQ (ptV (ladder2 k 456) (ladder2 k 456)) := by
  unfold baseLoop
  refine WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_)
  have hr1 : Rest [.t1] s s1 := u1.rest (by decide)
  have hm1 : s1.mem = s.mem := u1.mem
  have h912 : LoopInv b k s1 912 s1 :=
    ⟨⟨hc.of_rest hr1 (by decide), R64.Stp.refl _ _, rfl, by rw [u1.gpr], by rw [hm1, rv_912]; exact hS⟩⟩
  have hst : R64.Stp b s s1 := R64.Stp.of_rest hr1 (by decide) hm1
  have hb1 : Bits b k s1.mem := by rw [hm1]; exact hbits
  have hq1 : QOk b s1.mem := by rw [hm1]; exact hQ
  refine WP.mono (Q := LoopInv b k s1 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 912 ∧ LoopInv b k s1 m s') ?_ 912 s1 ⟨by decide, Nat.le_refl _, h912⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, by rw [← rv_0]; exact h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hb1 hq1 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

end

end VG.Proof.Ed448.RISCV64
