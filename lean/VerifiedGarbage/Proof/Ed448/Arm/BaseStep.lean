module

public import VerifiedGarbage.Proof.Ed448.CombRef
import VerifiedGarbage.Proof.X448.Arm.Counters
public import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase
public import VerifiedGarbage.Proof.X448.Arm.Ops
import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.Arm.Env

/-! ### `Ed448.Arm.BaseInit`, which this module and modules that import it used -/

section

/-!
# Ed448 base-point multiplication on ARMv7: the entry

The callee-saved registers saved (X448's `setupHead`) and every slot set to
its initial value (`initSlots_ok`): `R = (0 : 1 : 1)`, `Q` the base point, `d`,
and zero elsewhere, every limb below `2¹⁶`.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot ACC st)

theorem initVal_lt (i : Nat) : initVal i < Spec.X448.P := by
  unfold initVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | split)
  decide +kernel

theorem initLimb_lt (i k : Nat) : initLimb i k < 65536 := Nat.mod_lt _ (by decide)

theorem valN_digits (v : Nat) : ∀ n, valN (fun k => v / 2 ^ (16 * k) % 65536) n = v % radix ^ n
  | 0 => by simp [valN, Nat.mod_one]
  | n + 1 => by
    rw [valN_succ, valN_digits v n, Nat.mod_pow_succ, radix, ← Nat.pow_mul]

theorem initStep_ok {s : State} {base : Addr} (hs : Scr s base) (h4 : s.gpr .r4 = 0) {i k : Nat}
    (hi : i < 22) (hk : k < 28) :
    WP isa (.block (initStep i k)) s fun t =>
      t.mem = s.mem.writeW (off base (slot i + 4 * k)) (BitVec.ofNat 32 (initLimb i k)) ∧
        Keeps [.r3] s t := by
  have hsl : slot i + 4 * k + 4 ≤ 4096 := by simp only [slot]; omega_using [hi, hk]
  unfold initStep
  split
  · rename_i h0
    refine store_ok hs (by omega_using [hsl]) fun t ht => WP.block_nil ⟨?_, ⟨fun r _ => by rw [ht.gpr], ht.rd, ht.wr⟩⟩
    rw [ht.mem, h4, h0]; rfl
  · refine VG.Proof.X25519.Arm.wp_movw fun u hu => ?_
    refine store_ok (hs.of_upd hu (by decide) (by decide)) (by omega_using [hsl]) fun t ht => WP.block_nil ⟨?_, ?_⟩
    · rw [ht.mem, hu.mem, hu.gpr]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (initLimb_lt i k)]
    · exact ⟨fun r hr => by rw [ht.gpr, hu.other r (fun h => hr (by simp [h]))], by rw [ht.rd, hu.rd],
        by rw [ht.wr, hu.wr]⟩

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base) (h4 : s.gpr .r4 = 0) {i : Nat}
    (hi : i < 22) :
    WP isa (.block (initSlot i)) s fun t =>
      (∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.r3] s t := by
  have hsl : slot i + 112 ≤ 4096 := by simp only [slot]; omega_using [hi]
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.r3] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (initStep_ok (hs.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans h4) hi hn)
    fun u ⟨um, uk⟩ => ⟨fun k hk => ?_, tm.trans ?_, tk.trans uk⟩
  · change (word u.mem base (slot i + 4 * k)).toNat = _
    rw [um, word_write t.mem base (by omega_using [hsl, hn]) (by omega_using [hsl, hn, hk])]
    by_cases h : k = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := initLimb_lt i n; omega_using [this])]
    · rw [ite_eq_right h]; exact tf k (by omega_using [hk, h])
  · rw [um]; exact (writeW_outside _ _ _ (by omega_using [hsl, hn])).mono (by omega_using []) (by omega_using [hn])

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block initSlots) s fun t =>
      (∀ i < 22, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base 64 2816 s.mem t.mem ∧ Keeps [.r3, .r4] s t := by
  unfold initSlots
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have hsu := hs.of_upd hu (by decide) (by decide)
  have ku : Keeps [.r3, .r4] s u := rest_keeps (hu.rest (by decide))
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base 64 2816 u.mem t.mem ∧ Keeps [.r3] u t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 22
    (by decide) u ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, tm, tk⟩ => ⟨tf, by rw [← hu.mem]; exact tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (initSlot_ok (hsu.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans hu.gpr) hn)
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, tm.trans (vm.mono (by simp only [slot]; omega_using [])
      (by simp only [slot]; omega_using [hn])), tk.trans vk⟩
  by_cases h : i = n
  · subst h; exact vf k hk
  · rw [vm.limbs (by simp only [slot]; omega_using [h]) (by simp only [slot]; omega_using [hn, hi]) hk]
    exact tf i (by omega_using [hi, h]) k hk

/-- The slots' values. -/
theorem initSlots_E {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) (i : Index) :
    E m base i = Proof.X448.toFe (initVal i.val) := by
  simp only [E, F, fe]
  rw [valN_congr (g := fun k => initVal i.val / 2 ^ (16 * k) % 65536) (h i.val i.isLt), valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans (initVal_lt _) (by decide +kernel))]

theorem initSlots_bounded {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) : BoundedEnv m base :=
  fun i k hk => by rw [h i.val i.isLt k hk]; exact initLimb_lt _ _

end VG.Proof.Ed448.Arm

end

end

/-!
# Ed448 base-point multiplication on ARMv7: the comb's rows

The doubling and addition programs run as X448's verified field operations
on the slots (`ops_ok`), and evaluate to `double` and the specification's
`pointAdd` (`rowEnv_r`): `Proof/Ed448/CombRef.lean`'s `combRow`. One row
(`combStep_ok`) doubles `R` (slots 0–2), computes the index of its four bits
of the scalar (`combDigit_ok`), selects the table's entry of that index into
`Q`'s `x` and `y` (slots 8 and 9: `combSelect_ok`, every entry ORed in under
the mask of its index being the row's), and adds `Q` into `T` (slots 3–5),
copied into `R`; the loop (`combLoop_ok`) leaves `R` as the comb over all 114
rows, `comb k 114`.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.Ed448 (double comb combRow combDigit combPoint comb_row combDigit_lt)
open VG.Impl.X448.Arm (BITS slot ACC ld st)
open VG.Proof.X25519.Arm (wp_mov wp_dp wp_movw wp_ldrb wp_cmp op2_imm op2_reg op2_lsl op2_lsr)

variable {fv : Bool}

/-! ## The field programs -/

def doubleFields : List FieldOp := [
  .add 12 0 1, .mul 12 12 12, .mul 13 0 0, .mul 14 1 1, .add 15 13 14, .mul 16 2 2,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul 0 18 17, .sub 19 13 14, .mul 1 15 19,
  .mul 2 15 17]

def addFields : List FieldOp := [
  .mul 12 2 10, .mul 13 12 12, .mul 14 0 8, .mul 15 1 9, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 8 9, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

/-- `T` (slots 3–5) into `R` (slots 0–2). -/
def takeFields : List FieldOp := [.copy 0 3, .copy 1 4, .copy 2 5]

theorem doubleFields_impl : doubleFields.map FieldOp.impl = doubleOps := by decide +kernel
theorem addTake_impl : (addFields ++ takeFields).map FieldOp.impl = addOps ++ takeOps := by decide +kernel

/-- The point in slots `i`, `j`, `k`. -/
def pt (e : Env) (i j k : Index) : Spec.Ed448.Point := ⟨e i, e j, e k⟩

/-- The table's entry `i` in `Q`'s `x` and `y`. -/
def selEnv (i : Nat) (e : Env) : Env :=
  Function.update (Function.update e 8 (Impl.Ed448.Comb.entry i).1) 9 (Impl.Ed448.Comb.entry i).2

/-- The slots after a row of index `i`. -/
def rowEnv (i : Nat) (e : Env) : Env :=
  applyOps (addFields ++ takeFields) (selEnv i (applyOps doubleFields e))

/-- The specification's addition, with `d` a parameter. -/
def addWith (dd : Spec.X448.Fe) (p q : Spec.Ed448.Point) : Spec.Ed448.Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let d' := p.Y * q.Y
  let e := dd * c * d'
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (q.X + q.Y)
  ⟨a * f * (h - c - d'), a * g * (d' - c), f * g⟩

theorem rowEnv_pt (i : Nat) (e : Env) :
    pt (rowEnv i e) 0 1 2 = addWith (e 11) (double (pt e 0 1 2))
      ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e 10⟩ := rfl

theorem rowEnv_r (k t : Nat) (e : Env) (h1 : e 10 = 1) (hd : e 11 = Spec.Ed448.d) :
    pt (rowEnv (combDigit k t) e) 0 1 2 = combRow k t (pt e 0 1 2) := by
  rw [rowEnv_pt, h1, hd]; rfl

theorem rowEnv_one (i : Nat) (e : Env) : rowEnv i e 10 = e 10 := rfl

theorem rowEnv_d (i : Nat) (e : Env) : rowEnv i e 11 = e 11 := rfl

/-! ## The counter and the row's index -/

theorem decR11_ok {s : State} {t : Nat}
    (hb : s.gpr .r11 = BitVec.ofNat 32 (t + 1)) :
    WP isa (.block [.dp .sub .r11 .r11 (.imm 1)]) s fun u =>
      u.gpr .r11 = BitVec.ofNat 32 t ∧ (∀ r, r ≠ .r11 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧
        u.rd = s.rd ∧ u.wr = s.wr :=
  wp_dp (op2_imm (by decide)) fun u hu => WP.block_nil
    ⟨by rw [hu.gpr]; change s.gpr .r11 - BitVec.ofNat 32 1 = _
        rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel], hu.other, hu.mem, hu.rd, hu.wr⟩

theorem bit_lt (k t : Nat) : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Four bits, each a byte, as the row's index. -/
theorem digit_val : ∀ b0 < 2, ∀ b1 < 2, ∀ b2 < 2, ∀ b3 < 2,
    (BitVec.ofNat 8 b0).setWidth 32 + ((BitVec.ofNat 8 b1).setWidth 32 +
      ((BitVec.ofNat 8 b2).setWidth 32 + (BitVec.ofNat 8 b3).setWidth 32 <<< 1) <<< 1) <<< 1 =
      BitVec.ofNat 32 (b0 + 2 * b1 + 4 * b2 + 8 * b3) := by
  decide

theorem combDigit_ok {s : State} {base : Addr} (hs : Scr s base) {k t : Nat} (ht : t < 114)
    (hb : s.gpr .r11 = BitVec.ofNat 32 t)
    (hbits : ∀ i < 456, s.mem (off base (BITS + i)) = BitVec.ofNat 8 ((k >>> i) &&& 1)) :
    WP isa (.block Impl.Ed448.Arm.combDigit) s fun u =>
      u.gpr .r5 = BitVec.ofNat 32 (combDigit k t) ∧ Keeps [.r7, .r5, .r3] s u ∧ u.mem = s.mem := by
  have hB : BITS = 3072 := rfl
  unfold Impl.Ed448.Arm.combDigit
  refine wp_dp (op2_reg _ _) fun u1 v1 => ?_
  obtain e7 : u1.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 t := by
    rw [v1.gpr]; change s.gpr .r0 + s.gpr .r11 = _; rw [hb]
  obtain ea : ∀ c, t + c < 8192 → State.addr (u1.gpr .r7 + BitVec.ofNat 32 c) = off base (c + t) := fun c hc => by
    rw [e7, Offset.add_add]
    exact (hs.ea hc).trans (congrArg (off base) (Nat.add_comm t c))
  obtain rd : ∀ c, t + c < 8192 → InRegions (s.rd ++ s.wr) (off base (c + t)) 1 := fun c hc =>
    hs.read (by omega_using [hc])
  refine wp_ldrb (a := off base (BITS + 342 + t)) (by omega_arith) (ea _ (by omega_arith))
    (by rw [v1.rd, v1.wr]; exact rd _ (by omega_arith)) fun u2 v2 => ?_
  refine wp_ldrb (a := off base (BITS + 228 + t)) (by omega_arith)
    (by rw [v2.other _ (by decide)]; exact ea _ (by omega_arith))
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact rd _ (by omega_arith)) fun u3 v3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun u4 v4 => ?_
  refine wp_ldrb (a := off base (BITS + 114 + t)) (by omega_arith)
    (by rw [v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide)]; exact ea _ (by omega_arith))
    (by rw [v4.rd, v4.wr, v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact rd _ (by omega_arith)) fun u5 v5 => ?_
  refine wp_dp (op2_lsl (by decide)) fun u6 v6 => ?_
  refine wp_ldrb (a := off base (BITS + t)) (by omega_arith)
    (by rw [v6.other _ (by decide), v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
          v2.other _ (by decide)]; exact ea _ (by omega_arith))
    (by rw [v6.rd, v6.wr, v5.rd, v5.wr, v4.rd, v4.wr, v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]
        exact rd _ (by omega_arith)) fun u7 v7 => ?_
  refine wp_dp (op2_lsl (by decide)) fun u8 v8 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v8.gpr]; change u7.gpr .r3 + u7.gpr .r5 <<< 1 = _
    rw [v7.gpr, v7.other _ (by decide), v6.gpr]; change _ + (u5.gpr .r3 + u5.gpr .r5 <<< 1) <<< 1 = _
    rw [v5.gpr, v5.other _ (by decide), v4.gpr]; change _ + (_ + (u3.gpr .r3 + u3.gpr .r5 <<< 1) <<< 1) <<< 1 = _
    rw [v3.gpr, v3.other _ (by decide), v2.gpr, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem,
      show BITS + 342 + t = BITS + (t + 342) by omega_arith, show BITS + 228 + t = BITS + (t + 228) by omega_arith,
      show BITS + 114 + t = BITS + (t + 114) by omega_arith,
      hbits t (by omega_using [ht]), hbits (t + 114) (by omega_using [ht]), hbits (t + 228) (by omega_using [ht]),
      hbits (t + 342) (by omega_using [ht])]
    exact digit_val _ (bit_lt k t) _ (bit_lt k (t + 114)) _ (bit_lt k (t + 228)) _ (bit_lt k (t + 342))
  · obtain r2 := (v1.rest (ws := [.r7, .r5, .r3]) (by decide)).trans (v2.rest (by decide))
    obtain r4 := (r2.trans (v3.rest (by decide))).trans (v4.rest (by decide))
    obtain r6 := (r4.trans (v5.rest (by decide))).trans (v6.rest (by decide))
    exact rest_keeps ((r6.trans (v7.rest (by decide))).trans (v8.rest (by decide)))
  · rw [v8.mem, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

/-! ## The selection -/

/-- The mask of entry `i`, for the index `d`. -/
theorem selMask_val : ∀ d < 16, ∀ i < 16,
    (0 : BitVec 32) - ((BitVec.ofNat 32 d ^^^ BitVec.ofNat 32 i) - 1) >>> 31 = mask (decide (d = i)) := by
  decide

theorem selMask_ok (s : State) {d i : Nat} (hd : d < 16) (hi : i < 16) (h5 : s.gpr .r5 = BitVec.ofNat 32 d) :
    WP isa (.block (selMask i)) s fun u =>
      u.gpr .r4 = mask (decide (d = i)) ∧ Keeps [.r2, .r4] s u ∧ u.mem = s.mem := by
  unfold selMask
  refine wp_dp (op2_imm (by revert i; decide)) fun u1 v1 => ?_
  refine wp_dp (op2_imm (by decide)) fun u2 v2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun u3 v3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun u5 v5 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v5.gpr]; change u4.gpr .r4 - u4.gpr .r2 = _
    rw [v4.gpr, v4.other _ (by decide), v3.gpr, v2.gpr]; change (0 : BitVec 32) - (u1.gpr .r2 - 1) >>> 31 = _
    rw [v1.gpr]; change (0 : BitVec 32) - ((s.gpr .r5 ^^^ BitVec.ofNat 32 i) - 1) >>> 31 = _
    rw [h5]; exact selMask_val d hd i hi
  · exact rest_keeps ((v1.rest (ws := [.r2, .r4]) (by decide)).trans ((v2.rest (by decide)).trans
      ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans (v5.rest (by decide))))))
  · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

theorem selLimb_ok {s : State} {base : Addr} (hs : Scr s base) {o j : Nat} (ho : o + 112 ≤ 4096)
    (hj : j < 28) (v : Nat → Nat) {b : Bool} (h4 : s.gpr .r4 = mask b) :
    WP isa (.block (selLimb o v j)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 4 * j))
        (word s.mem base (o + 4 * j) ||| ((BitVec.ofNat 16 (v j)).setWidth 32 &&& mask b)) ∧
      Keeps [.r2, .r3] s t := by
  unfold selLimb
  refine wp_movw fun u1 v1 => ?_
  refine wp_dp (op2_reg _ _) fun u2 v2 => ?_
  obtain hs2 : Scr u2 base := (hs.of_upd v1 (by decide) (by decide)).of_upd v2 (by decide) (by decide)
  refine load_ok hs2 (by omega_using [ho, hj]) fun u3 v3 => ?_
  refine wp_dp (op2_reg _ _) fun u4 v4 => ?_
  refine store_ok ((hs2.of_upd v3 (by decide) (by decide)).of_upd v4 (by decide) (by decide))
    (by omega_using [ho, hj]) fun u5 v5 => WP.block_nil ⟨?_, ?_⟩
  · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem, v4.gpr]
    change s.mem.writeW _ (u3.gpr .r3 ||| u3.gpr .r2) = _
    rw [v3.gpr, v3.other _ (by decide), v2.gpr, v2.mem, v1.mem]
    change s.mem.writeW _ (word s.mem base _ ||| (u1.gpr .r2 &&& u1.gpr .r4)) = _
    rw [v1.gpr, v1.other _ (by decide), h4]
  · exact rest_keeps ((v1.rest (ws := [.r2, .r3]) (by decide)).trans ((v2.rest (by decide)).trans
      ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans (v5.rest _)))))

theorem selCoord_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (v : Nat → Nat) {b : Bool} (h4 : s.gpr .r4 = mask b) :
    WP isa (.block (selCoord o v)) s fun t =>
      (∀ j < 28, word t.mem base (o + 4 * j) =
        word s.mem base (o + 4 * j) ||| ((BitVec.ofNat 16 (v j)).setWidth 32 &&& mask b)) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.r2, .r3] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, word t.mem base (o + 4 * j) =
      word s.mem base (o + 4 * j) ||| ((BitVec.ofNat 16 (v j)).setWidth 32 &&& mask b)) ∧
    (∀ j, n ≤ j → j < 28 → word t.mem base (o + 4 * j) = word s.mem base (o + 4 * j)) ∧
    Outside base o 112 s.mem t.mem ∧ Keeps [.r2, .r3] s t
  obtain step : ∀ n t, n < 28 → inv n t → WP isa (.block (selLimb o v n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (selLimb_ok (hs.of_keeps tk (by decide)) ho hn v ((tk.1 _ (by decide)).trans h4))
      fun u ⟨um, uk⟩ => ?_
    obtain out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨fun j hj => ?_, fun j hj hj' => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans uk⟩
    · rw [um, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hj])]
      by_cases h : j = n
      · rw [ite_eq_left h, h, ta n (Nat.le_refl _) hn]
      · rw [ite_eq_right h]; exact tf j (by omega_using [hj, h])
    · rw [out.word (by omega_using [hj]) (by omega_using [ho, hj'])]
      exact ta j (by omega_using [hj]) hj'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hj => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

theorem zeroSlot_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (h3 : s.gpr .r3 = 0) :
    WP isa (.block (zeroSlot o)) s fun t =>
      (∀ j < 28, word t.mem base (o + 4 * j) = 0) ∧ Outside base o 112 s.mem t.mem ∧ Keeps [] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, word t.mem base (o + 4 * j) = 0) ∧ Outside base o 112 s.mem t.mem ∧ Keeps [] s t
  obtain step : ∀ n t, n < 28 → inv n t → WP isa (.block [st .r3 (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine store_ok (hs.of_keeps tk (by decide)) (by omega_using [ho, hn]) fun u hu => WP.block_nil ?_
    obtain out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [hu.mem]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨fun j hj => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans (rest_keeps (hu.rest _))⟩
    rw [hu.mem, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hj])]
    by_cases h : j = n
    · rw [ite_eq_left h, tk.1 _ (by decide), h3]
    · rw [ite_eq_right h]; exact tf j (by omega_using [hj, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- After the first `n` entries: slots 8 and 9 hold the entry of index `d` if it is below `n`,
and zero otherwise. -/
def Sel (base : Addr) (d n : Nat) (m : Mem) : Prop :=
  ∀ c < 2, ∀ j < 28, word m base (slot (8 + c) + 4 * j) =
    if d < n then BitVec.ofNat 32 (combLimb d c j) else 0

theorem combLimb_lt (i c j : Nat) : combLimb i c j < 65536 := Nat.mod_lt _ (by decide)

theorem movw_limb {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h]),
    Nat.mod_eq_of_lt (by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [h])]

theorem or_and_mask_true (x : BitVec 32) : (0 : BitVec 32) ||| (x &&& mask true) = x := by
  show 0 ||| (x &&& BitVec.allOnes 32) = x
  rw [BitVec.and_allOnes]
  exact BitVec.zero_or

theorem or_and_mask_false (w x : BitVec 32) : w ||| (x &&& mask false) = w := by
  have e : x &&& (0 : BitVec 32) = 0 := BitVec.and_zero
  show w ||| (x &&& 0) = w
  rw [e]
  exact BitVec.or_zero

/-- A limb of the selection after entry `n`. -/
theorem sel_word {d n : Nat} {w : BitVec 32} {v v' : Nat} (hv : v < 65536)
    (hw : w = if d < n then BitVec.ofNat 32 v' else 0) (hv' : d = n → v = v') :
    w ||| ((BitVec.ofNat 16 v).setWidth 32 &&& mask (decide (d = n))) =
      if d < n + 1 then BitVec.ofNat 32 v' else 0 := by
  by_cases h : d = n
  · subst h
    rw [hw, ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), decide_eq_true rfl, movw_limb hv,
      hv' rfl]
    exact or_and_mask_true _
  · rw [decide_eq_false h, or_and_mask_false, hw]
    by_cases hlt : d < n
    · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
    · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt, h])]

theorem selEntry_ok {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d < 16) (hn : n < 16)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 d) (hsel : Sel base d n s.mem) :
    WP isa (.block (selEntry n)) s fun t =>
      Sel base d (n + 1) t.mem ∧ Outside base (slot 8) 240 s.mem t.mem ∧ Keeps [.r2, .r3, .r4] s t := by
  have h8 : slot 8 = 1088 := rfl
  have h9 : slot 9 = 1216 := rfl
  unfold selEntry
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (selMask_ok s hd hn h5) fun u ⟨u4, uk, um⟩ => ?_
  obtain hsu := hs.of_keeps uk (by decide)
  refine VG.Proof.X25519.Arm.WP.append (selCoord_ok hsu (o := slot 8) (by omega_using [h8]) (combLimb n 0) u4)
    fun v ⟨vf, vm, vk⟩ => ?_
  obtain hsv := hsu.of_keeps vk (by decide)
  refine WP.mono (selCoord_ok hsv (o := slot 9) (by omega_using [h9]) (combLimb n 1)
    ((vk.1 _ (by decide)).trans u4)) fun w ⟨wf, wm, wk⟩ => ⟨?_, ?_, ?_⟩
  · intro c hc j hj
    rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
    · rw [show slot (8 + 0) = slot 8 from rfl, wm.word (by omega_using [h8, h9, hj]) (by omega_using [h8, hj]), vf j hj, um]
      exact sel_word (combLimb_lt _ _ _) (hsel 0 (by decide) j hj) (fun h => by rw [h])
    · rw [show slot (8 + 1) = slot 9 from rfl, wf j hj, vm.word (by omega_using [h8, h9, hj]) (by omega_using [h9, hj]), um]
      exact sel_word (combLimb_lt _ _ _) (hsel 1 (by decide) j hj) (fun h => by rw [h])
  · rw [← um]
    exact (vm.mono (by omega_using [h8]) (by omega_using [h8])).trans
      (wm.mono (by omega_using [h8, h9]) (by omega_using [h8, h9]))
  · exact (uk.mono (by decide)).trans ((vk.mono (by decide)).trans (wk.mono (by decide)))

/-- A slot whose limbs are the digits of a field element holds it. -/
theorem F_digits {m : Mem} {base : Addr} {o : Nat} (x : Spec.X448.Fe)
    (h : ∀ k < 28, limbs m base o k = x.val / 2 ^ (16 * k) % 65536) : F m base o = x := by
  simp only [F, fe]
  rw [valN_congr (g := fun k => x.val / 2 ^ (16 * k) % 65536) h, valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide +kernel)), Proof.X448.toFe_self]

theorem combSelect_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {d : Nat}
    (hd : d < 16) (h5 : s.gpr .r5 = BitVec.ofNat 32 d) :
    WP isa (.block combSelect) s fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = selEnv d (E s.mem base) := by
  have h8 : slot 8 = 1088 := rfl
  have h9 : slot 9 = 1216 := rfl
  have hA : ACC = 3584 := rfl
  unfold combSelect
  rw [List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun u hu => ?_
  obtain ku : Keeps [.r2, .r3, .r4] s u := rest_keeps (hu.rest (by decide))
  obtain hsu := hs.of_keeps ku (by decide)
  refine VG.Proof.X25519.Arm.WP.append (zeroSlot_ok hsu (o := slot 8) (by omega_using [h8]) hu.gpr)
    fun v ⟨vf, vm, vk⟩ => ?_
  obtain hsv := hsu.of_keeps vk (by decide)
  refine VG.Proof.X25519.Arm.WP.append (zeroSlot_ok hsv (o := slot 9) (by omega_using [h9])
    ((vk.1 _ (by decide)).trans hu.gpr)) fun w ⟨wf, wm, wk⟩ => ?_
  obtain kw : Keeps [.r2, .r3, .r4] s w := ku.trans ((vk.mono (by simp)).trans (wk.mono (by simp)))
  obtain ow : Outside base (slot 8) 240 s.mem w.mem := by
    rw [← hu.mem]
    exact (vm.mono (by omega_using [h8]) (by omega_using [h8])).trans
      (wm.mono (by omega_using [h8, h9]) (by omega_using [h8, h9]))
  obtain sel0 : Sel base d 0 w.mem := by
    intro c hc j hj
    rw [ite_eq_right (Nat.not_lt_zero _)]
    rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
    · rw [show slot (8 + 0) = slot 8 from rfl, wm.word (by omega_using [h8, h9, hj]) (by omega_using [h8, hj])]
      exact vf j hj
    · exact wf j hj
  let inv := fun n (t : State) =>
    Sel base d n t.mem ∧ Outside base (slot 8) 240 s.mem t.mem ∧ Keeps [.r2, .r3, .r4] s t
  obtain step : ∀ n t, n < 16 → inv n t → WP isa (.block (selEntry n)) t (inv (n + 1)) := by
    intro n t hn ⟨ts, tm, tk⟩
    exact WP.mono (selEntry_ok (hs.of_keeps tk (by decide)) hd hn ((tk.1 _ (by decide)).trans h5) ts)
      fun x ⟨xs, xm, xk⟩ => ⟨xs, tm.trans xm, tk.trans xk⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) w ⟨sel0, ow, kw⟩)
    fun t ⟨ts, tm, tk⟩ => ?_
  obtain lx : ∀ j < 28, limbs t.mem base (slot 8) j = (Impl.Ed448.Comb.entry d).1.val / 2 ^ (16 * j) % 65536 :=
    fun j hj => by
      change (word t.mem base (slot (8 + 0) + 4 * j)).toNat = _
      rw [ts 0 (by decide) j hj, ite_eq_left hd, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (combLimb_lt _ _ _) (by decide))]
      rfl
  obtain ly : ∀ j < 28, limbs t.mem base (slot 9) j = (Impl.Ed448.Comb.entry d).2.val / 2 ^ (16 * j) % 65536 :=
    fun j hj => by
      change (word t.mem base (slot (8 + 1) + 4 * j)).toNat = _
      rw [ts 1 (by decide) j hj, ite_eq_left hd, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (combLimb_lt _ _ _) (by decide))]
      rfl
  obtain other : ∀ i : Index, i ≠ 8 → i ≠ 9 → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := fun i h8' h9' j hj => by
    have e8 := slot_sep h8'
    have e9 := slot_sep h9'
    have hi := slot_bound i
    change slot i.val + 112 ≤ 3584 at hi
    exact tm.limbs (by change slot i.val + 112 ≤ slot 8 ∨ slot 8 + 112 ≤ slot i.val at e8
                       change slot i.val + 112 ≤ slot 9 ∨ slot 9 + 112 ≤ slot i.val at e9
                       omega_using [e8, e9, h8, h9]) (by omega_using [hi]) hj
  refine ⟨⟨tk.mono (by decide), fun p hp _ => tm p (by omega_using [hp, h8])⟩, fun i j hj => ?_, ?_⟩
  · by_cases i8 : i = 8
    · subst i8; change limbs t.mem base (slot 8) j < radix; rw [lx j hj]; exact Nat.mod_lt _ (by decide)
    · by_cases i9 : i = 9
      · subst i9; change limbs t.mem base (slot 9) j < radix; rw [ly j hj]; exact Nat.mod_lt _ (by decide)
      · rw [other i i8 i9 j hj]; exact hbd i j hj
  · funext i
    by_cases i9 : i = 9
    · subst i9; rw [selEnv, Function.update_self]; exact F_digits _ ly
    · rw [selEnv, Function.update_of_ne i9]
      by_cases i8 : i = 8
      · subst i8; rw [Function.update_self]; exact F_digits _ lx
      · rw [Function.update_of_ne i8]
        exact congrArg Proof.X448.toFe (valN_congr (other i i8 i9))

/-! ## One row -/

/-- The loop's invariant, after the rows above `n`. -/
structure CombInv (base : Addr) (k : Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.r11 :: workRegs) s₀ s
  r11 : s.gpr .r11 = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  r : pt (E s.mem base) 0 1 2 = comb k (114 - n)
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d

theorem combStep_ok {s₀ s : State} {base : Addr} {k n : Nat} (hn : n < 114)
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : CombInv base k s₀ s (n + 1)) :
    WP isa (combStep fv) s fun t => CombInv base k s₀ t n ∧ t.z = decide (n = 0) := by
  have hs := hi.scr
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  unfold combStep
  refine WP.seq (WP.mono (decR11_ok hi.r11) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain K₁ : Keeps [.r11] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  rw [← doubleFields_impl]
  refine WP.seq (WP.mono (ops_ok hs₁ (m₁ ▸ hi.bounded) doubleFields) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain b₂ : s₂.gpr .r11 = BitVec.ofNat 32 n := by rw [k₂.regs.1 _ (by decide), b₁]
  obtain bits₂ : ∀ t < 456, s₂.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1) := fun t ht => by
    rw [k₂.mem _ (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [hB])
      (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB, hA]), m₁,
      hi.mem _ (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [hB])
        (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB, hA])]
    exact hbits t ht
  refine WP.seq (VG.Proof.X25519.Arm.WP.append (combDigit_ok hs₂ hn b₂ bits₂) fun s₃ ⟨d₃, k₃, m₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (combSelect_ok hs₃ (m₃ ▸ bb₂) (combDigit_lt k n) d₃) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_
  obtain hs₄ := k₄.scr hs₃
  rw [← addTake_impl]
  refine WP.seq (WP.mono (ops_ok hs₄ bb₄ (addFields ++ takeFields)) fun s₅ ⟨k₅, bb₅, e₅⟩ => ?_)
  refine wp_cmp (op2_imm (by decide)) fun t vt hz => WP.block_nil ?_
  obtain K₃ : Keep base s₂ s₃ := ⟨k₃.mono (by decide), by rw [m₃]; exact Outside2.refl _ _ _ _ _ _⟩
  obtain core := k₂.trans (K₃.trans (k₄.trans k₅))
  obtain b₅ : s₅.gpr .r11 = BitVec.ofNat 32 n := by rw [core.regs.1 _ (by decide), b₁]
  obtain ee : E t.mem base = rowEnv (combDigit k n) (E s.mem base) := by
    rw [vt.mem, e₅, e₄, m₃, e₂, m₁]; rfl
  refine ⟨⟨(core.scr hs₁).of_keeps (rest_keeps (vt.rest [])) (by decide), vt.mem ▸ bb₅, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [vt.gpr, core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
    · rw [vt.rd, core.regs.2.1, rd₁]
    · rw [vt.wr, core.regs.2.2, wr₁]
  · rw [vt.gpr, b₅]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [vt.mem, core.mem p hp hq, m₁]
  · rw [ee, rowEnv_r _ _ _ hi.one hi.d, hi.r, comb_row k hn]
  · rw [ee, rowEnv_one]; exact hi.one
  · rw [ee, rowEnv_d]; exact hi.d
  · rw [hz, b₅]
    change (BitVec.ofNat 32 n - BitVec.ofNat 32 0 == 0) = _
    rw [BitVec.sub_zero]
    exact VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_using [hn])

theorem combLoop_ok {s₀ s : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1))
    (hi : ∀ s', s'.gpr .r11 = BitVec.ofNat 32 114 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → CombInv base k s₀ s' 114) :
    WP isa (combLoop fv) s fun s' => CombInv base k s₀ s' 0 := by
  unfold combLoop
  refine WP.seq (WP.mono (setCounter_ok s 114 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := combStep fv) (c := .ne) (Q := fun s' => CombInv base k s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 114 ∧ CombInv base k s₀ s m) ?_ 114 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (combStep_ok (by omega_using [h2]) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_using [hm] : ¬m = 0), Bool.not_false], m, by omega_using [],
      by omega_using [hm], by omega_using [h2], hi'⟩

end VG.Proof.Ed448.Arm
