module

-- separate module: `Proof/Bignum/Layout`'s `word` and `Outside`, which `ModExpWin.lean` needs, would shadow `Mont`'s in these proofs
public import VerifiedGarbage.Impl.Bignum.RISCV64.Pow57
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery arithmetic in radix `2⁵⁷` on RISC-V

Of `Impl/Bignum/RISCV64/Pow57.lean`: a number of limbs of 57 bits in words is `lv`, whatever the words' size.

* `rect_ok`: three rows of products, as the multiplication and addition `T + c + X Y`, where `c` (`cVal`) is what the
  columns so far carry; it needs no sums over columns.
* `redRows_ok`, `norm_ok`, `reduce57_ok`: the reduction, and the carry pass.
* `mulRows_ok`, `mulOp57_ok`: the product, with operands below `2 m`, which gives a result below `2 m`.
* `sqrRows_ok` (with a bound for each column, `sqB`), `diag57_ok`, `sqrOp57_ok`: the square.
* `unpackFrom_ok`, `pack_ok`: from and to words of 64 bits.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pow57

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Pow57

/-! ## Numbers in radix `2⁵⁷` -/

/-- The `k` words at `d`, as a little-endian number in radix `2⁵⁷`, whatever their size. -/
def lv (m : Mem) (B : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => lv m B d k + 2 ^ (57 * k) * (word m B (d + 8 * k)).toNat

/-- Word `i` of the `k` words at `d` is at most `f i`. -/
def LimF (m : Mem) (B : Addr) (d k : Nat) (f : Nat → Nat) : Prop := ∀ i < k, (word m B (d + 8 * i)).toNat ≤ f i

/-- The `k` words at `d` are at most `b`. -/
abbrev Lim (m : Mem) (B : Addr) (d k b : Nat) : Prop := LimF m B d k fun _ => b

/-- The largest limb. -/
abbrev L57 : Nat := 2 ^ 57 - 1

theorem lv_append (m : Mem) (B : Addr) (d j k : Nat) :
    lv m B d (j + k) = lv m B d j + 2 ^ (57 * j) * lv m B (d + 8 * j) k := by
  induction k with
  | zero => simp only [lv, Nat.mul_zero, Nat.add_zero]
  | succ k ih =>
    rw [← Nat.add_assoc, lv, ih, lv, Nat.mul_add (2 ^ (57 * j)), Nat.mul_add 57, Nat.pow_add, Nat.mul_assoc (2 ^ (57 * j)),
      show d + 8 * (j + k) = d + 8 * j + 8 * k by omega_arith, Nat.add_assoc]

theorem lv_one (m : Mem) (B : Addr) (d : Nat) : lv m B d 1 = (word m B d).toNat := by
  simp only [lv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]

theorem lv_three (m : Mem) (B : Addr) (d : Nat) : lv m B d 3 =
    (word m B d).toNat + 2 ^ 57 * (word m B (d + 8)).toNat + 2 ^ 114 * (word m B (d + 16)).toNat := by
  simp only [lv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.reduceMul, Nat.mul_one]

theorem lv_congr {m m' : Mem} {B : Addr} {d k : Nat} (h : ∀ i < k, word m' B (d + 8 * i) = word m B (d + 8 * i)) :
    lv m' B d k = lv m B d k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [lv, lv, ih fun i hi => h i (by omega_arith), h k (by omega_arith)]

theorem _root_.VG.Proof.Mont.Outside.lv {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {d k : Nat}
    (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) : Pow57.lv m' B d k = Pow57.lv m B d k :=
  lv_congr fun i hi => h.word (by omega_arith) (by omega_arith)

theorem _root_.VG.Proof.Mont.Outside.lim {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {d k : Nat}
    {f : Nat → Nat} (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) (hl : LimF m B d k f) : LimF m' B d k f :=
  fun i hi => by rw [h.word (by omega_arith) (by omega_arith)]; exact hl i hi

theorem lv_lt {m : Mem} {B : Addr} {d k : Nat} (h : Lim m B d k L57) : lv m B d k < 2 ^ (57 * k) := by
  induction k with
  | zero => exact Nat.one_pos
  | succ k ih =>
    obtain i := ih fun i hi => h i (by omega_arith)
    obtain w := h k (by omega_arith)
    rw [lv, Nat.mul_succ, Nat.pow_add]
    obtain l := Nat.mul_le_mul_left (2 ^ (57 * k)) w
    unfold L57 at l
    rw [Nat.mul_sub_one] at l
    obtain p := Nat.le_mul_of_pos_right (2 ^ (57 * k)) (show 0 < 2 ^ 57 by decide)
    omega_arith

/-! ## A column -/

/-- The low word of a product of two limbs. -/
abbrev lo57 (x y : BitVec 64) : Nat := x.toNat * y.toNat % 2 ^ 57

abbrev hi57 (x y : BitVec 64) : Nat := x.toNat * y.toNat / 2 ^ 57

theorem shl7_mul {x y : BitVec 64} (hx : x.toNat ≤ L57) :
    (x <<< 7).toNat * y.toNat / 2 ^ 64 = hi57 x y := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by unfold L57 at hx; omega_arith), Nat.mul_right_comm,
    show 2 ^ 64 = 2 ^ 57 * 2 ^ 7 by decide, Nat.mul_div_mul_right _ _ (by decide)]

theorem hi57_le {x y : BitVec 64} (hx : x.toNat ≤ L57) (hy : y.toNat ≤ L57) : hi57 x y ≤ L57 := by
  obtain := Nat.mul_le_mul hx hy
  unfold hi57 L57 at *
  omega_arith

theorem mul_ofNat (x y : BitVec 64) : x * y = BitVec.ofNat 64 (x.toNat * y.toNat) := by
  rw [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem ofNat_shl57 (n : Nat) : BitVec.ofNat 64 n <<< 57 = BitVec.ofNat 64 (2 ^ 57 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mul_comm]

theorem lo57_le (x y : BitVec 64) : lo57 x y ≤ L57 :=
  Nat.le_sub_one_of_lt (Nat.mod_lt (x.toNat * y.toNat) (show 2 ^ 57 > 0 by decide))

/-- The high word of a product. -/
def mh (x y : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)

theorem exec_mh {s : State} {d n m : Reg} :
    exec (.mulhu d n m) s = some (s.write d (mh (s.gpr n) (s.gpr m))) := exec_mulhu

/-- A column's carry word. -/
abbrev colH (x₀ x₁ x₂ y₀ y₁ y₂ : BitVec 64) : BitVec 64 := mh (x₀ <<< 7) y₀ + mh (x₁ <<< 7) y₁ + mh (x₂ <<< 7) y₂

/-- A column's sum. -/
abbrev colV (t h x₀ x₁ x₂ y₀ y₁ y₂ : BitVec 64) : BitVec 64 :=
  t + h + (x₀ * y₀ + x₁ * y₁ + x₂ * y₂ - colH x₀ x₁ x₂ y₀ y₁ y₂ <<< 57)

/-- `t + h + (L - (H << 57))`, for `L` the sum of three products' low words and `H` of the rest. -/
theorem col_val {x₀ x₁ x₂ y₀ y₁ y₂ t h : BitVec 64} (hx₀ : x₀.toNat ≤ L57) (hx₁ : x₁.toNat ≤ L57)
    (hx₂ : x₂.toNat ≤ L57) (hy₀ : y₀.toNat ≤ L57) (hy₁ : y₁.toNat ≤ L57) (hy₂ : y₂.toNat ≤ L57)
    (ht : t.toNat + h.toNat + 3 * L57 < 2 ^ 64) :
    (colV t h x₀ x₁ x₂ y₀ y₁ y₂).toNat =
        t.toNat + h.toNat + lo57 x₀ y₀ + lo57 x₁ y₁ + lo57 x₂ y₂ ∧
    (colH x₀ x₁ x₂ y₀ y₁ y₂).toNat = hi57 x₀ y₀ + hi57 x₁ y₁ + hi57 x₂ y₂ := by
  unfold colV colH mh
  rw [shl7_mul hx₀, shl7_mul hx₁, shl7_mul hx₂]
  obtain a₀ := hi57_le hx₀ hy₀
  obtain a₁ := hi57_le hx₁ hy₁
  obtain a₂ := hi57_le hx₂ hy₂
  obtain e₀ := Nat.div_add_mod (x₀.toNat * y₀.toNat) (2 ^ 57)
  obtain e₁ := Nat.div_add_mod (x₁.toNat * y₁.toNat) (2 ^ 57)
  obtain e₂ := Nat.div_add_mod (x₂.toNat * y₂.toNat) (2 ^ 57)
  obtain b₀ := Nat.mod_lt (x₀.toNat * y₀.toNat) (show 2 ^ 57 > 0 by decide)
  obtain b₁ := Nat.mod_lt (x₁.toNat * y₁.toNat) (show 2 ^ 57 > 0 by decide)
  obtain b₂ := Nat.mod_lt (x₂.toNat * y₂.toNat) (show 2 ^ 57 > 0 by decide)
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
  refine ⟨?_, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold L57 at a₀ a₁ a₂; omega_using [a₀, a₁, a₂])]⟩
  obtain key : x₀ * y₀ + x₁ * y₁ + x₂ * y₂ -
      BitVec.ofNat 64 (hi57 x₀ y₀ + hi57 x₁ y₁ + hi57 x₂ y₂) <<< 57 =
      BitVec.ofNat 64 (lo57 x₀ y₀ + lo57 x₁ y₁ + lo57 x₂ y₂) := by
    rw [BitVec.sub_eq_iff_eq_add, ofNat_shl57, ← BitVec.ofNat_add, mul_ofNat, mul_ofNat, mul_ofNat, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add]
    refine congrArg _ ?_
    unfold hi57 lo57
    omega_using [e₀, e₁, e₂]
  rw [key, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_eq_of_lt (by unfold lo57; unfold L57 at ht; omega_using [ht, b₀, b₁, b₂])]
  omega_using []

theorem rd_ne (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) : (m.writeW (off B d) v).readW (off B e) 64 = m.readW (off B e) 64 :=
  (writeW_outside m B v hd).word (by omega_arith) he

theorem wd_ne (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) : word (m.writeW (off B d) v) B e = word m B e :=
  (writeW_outside m B v hd).word (by omega_arith) he

/-- What three columns leave, the columns' words at `dT` and `dY`. -/
structure Cols (s t : State) (B : Addr) (dT dY : Nat) : Prop where
  mem : ∃ v₀ v₁ v₂ : BitVec 64, t.mem = ((s.mem.writeW (off B dT) v₀).writeW (off B (dT + 8)) v₁).writeW (off B (dT + 16)) v₂ ∧
    v₀.toNat = (word s.mem B dT).toNat + (s.gpr .s7).toNat + lo57 (s.gpr .s2) (word s.mem B dY) +
      lo57 (s.gpr .s3) (s.gpr .t5) + lo57 (s.gpr .s4) (s.gpr .t6) ∧
    v₁.toNat = (word s.mem B (dT + 8)).toNat + (hi57 (s.gpr .s2) (word s.mem B dY) + hi57 (s.gpr .s3) (s.gpr .t5) +
      hi57 (s.gpr .s4) (s.gpr .t6)) + lo57 (s.gpr .s2) (word s.mem B (dY + 8)) +
      lo57 (s.gpr .s3) (word s.mem B dY) + lo57 (s.gpr .s4) (s.gpr .t5) ∧
    v₂.toNat = (word s.mem B (dT + 16)).toNat + (hi57 (s.gpr .s2) (word s.mem B (dY + 8)) +
      hi57 (s.gpr .s3) (word s.mem B dY) + hi57 (s.gpr .s4) (s.gpr .t5)) +
      lo57 (s.gpr .s2) (word s.mem B (dY + 16)) + lo57 (s.gpr .s3) (word s.mem B (dY + 8)) +
      lo57 (s.gpr .s4) (word s.mem B dY)
  h : (t.gpr .s7).toNat = hi57 (s.gpr .s2) (word s.mem B (dY + 16)) + hi57 (s.gpr .s3) (word s.mem B (dY + 8)) +
    hi57 (s.gpr .s4) (word s.mem B dY)
  y₁ : t.gpr .t5 = word s.mem B (dY + 16)
  y₂ : t.gpr .t6 = word s.mem B (dY + 8)

/-- The registers three columns write. -/
def colRegs : List Reg := [.s0, .s1, .s7, .a2, .a3, .a4, .a5, .a6, .t0, .t5, .t6]

theorem cols_ok {s : State} {B : Addr} {Z dT dY : Nat} {f : Nat → Nat} (hs : Scr s B Z) (ha0 : s.gpr .a0 = off B dT)
    (ha1 : s.gpr .a1 = off B dY) (hT : dT + 24 ≤ Z) (hY : dY + 24 ≤ Z) (hT8 : dT % 8 = 0) (hY8 : dY % 8 = 0)
    (sep : dY + 24 ≤ dT ∨ dT + 24 ≤ dY)
    (h2 : s.gpr .t2 = s.gpr .s2 <<< 7) (h3 : s.gpr .t3 = s.gpr .s3 <<< 7) (h4 : s.gpr .t4 = s.gpr .s4 <<< 7)
    (x0 : (s.gpr .s2).toNat ≤ L57) (x1 : (s.gpr .s3).toNat ≤ L57) (x2 : (s.gpr .s4).toNat ≤ L57)
    (y1 : (s.gpr .t5).toNat ≤ L57) (y2 : (s.gpr .t6).toNat ≤ L57) (lY : Lim s.mem B dY 3 L57)
    (lT : LimF s.mem B dT 3 f) (hh : (s.gpr .s7).toNat ≤ 3 * L57 + 2 ^ 10)
    (hb : ∀ i < 3, f i + 6 * L57 + 2 ^ 10 < 2 ^ 64) :
    WP isa (.block cols) s fun t => Cols s t B dT dY ∧ Keep colRegs s t := by
  have hn := hs.nowrap
  obtain l0 := lY 0 (by decide)
  obtain l1 := lY 1 (by decide)
  obtain l2 := lY 2 (by decide)
  obtain m0 := lT 0 (by decide)
  obtain m1 := lT 1 (by decide)
  obtain m2 := lT 2 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at l0 l1 l2 m0 m1 m2
  obtain f0 := hb 0 (by decide)
  obtain f1 := hb 1 (by decide)
  obtain f2 := hb 2 (by decide)
  obtain run : WP isa (.block cols) s fun t => (t.mem = ((s.mem.writeW (off B dT)
        (colV (word s.mem B dT) (s.gpr .s7) (s.gpr .s2) (s.gpr .s3) (s.gpr .s4) (word s.mem B dY) (s.gpr .t5) (s.gpr .t6))).writeW
        (off B (dT + 8)) (colV (word s.mem B (dT + 8)) (colH (s.gpr .s2) (s.gpr .s3) (s.gpr .s4) (word s.mem B dY)
          (s.gpr .t5) (s.gpr .t6)) (s.gpr .s2) (s.gpr .s3) (s.gpr .s4) (word s.mem B (dY + 8)) (word s.mem B dY) (s.gpr .t5))).writeW
        (off B (dT + 16)) (colV (word s.mem B (dT + 16)) (colH (s.gpr .s2) (s.gpr .s3) (s.gpr .s4) (word s.mem B (dY + 8))
          (word s.mem B dY) (s.gpr .t5)) (s.gpr .s2) (s.gpr .s3) (s.gpr .s4) (word s.mem B (dY + 16)) (word s.mem B (dY + 8)) (word s.mem B dY)) ∧
      t.gpr .s7 = colH (s.gpr .s2) (s.gpr .s3) (s.gpr .s4) (word s.mem B (dY + 16)) (word s.mem B (dY + 8)) (word s.mem B dY) ∧
      t.gpr .t5 = word s.mem B (dY + 16) ∧ t.gpr .t6 = word s.mem B (dY + 8)) ∧ Keep colRegs s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold cols
    brun [↓exec_mh, ha0, ha1, h2, h3, h4, hs.ld (show dT + 8 ≤ Z by omega_arith), hs.ld (show dT + 8 + 8 ≤ Z by omega_arith),
    hs.ld (show dT + 16 + 8 ≤ Z by omega_arith), hs.ld (show dY + 8 ≤ Z by omega_arith),
    hs.ld (show dY + 8 + 8 ≤ Z by omega_arith), hs.ld (show dY + 16 + 8 ≤ Z by omega_arith),
    hs.st (show dT + 8 ≤ Z by omega_arith), hs.st (show dT + 8 + 8 ≤ Z by omega_arith),
    hs.st (show dT + 16 + 8 ≤ Z by omega_arith),
    hs.al8 (show dT + 8 ≤ Z by omega_arith) hT8, hs.al8 (show dT + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dT + 16 + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dY + 8 ≤ Z by omega_arith) hY8, hs.al8 (show dY + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dY + 16 + 8 ≤ Z by omega_arith) (by omega_arith),
    rd_ne _ B (d := dT) (e := dT + 8) _ (by omega_arith) (by omega_arith) (by omega_arith),
    rd_ne _ B (d := dT) (e := dT + 16) _ (by omega_arith) (by omega_arith) (by omega_arith),
    rd_ne _ B (d := dT + 8) (e := dT + 16) _ (by omega_arith) (by omega_arith) (by omega_arith),
    rd_ne _ B (d := dT) (e := dY + 8) _ (by omega_arith) (by omega_arith) (by omega_arith),
    rd_ne _ B (d := dT) (e := dY + 16) _ (by omega_arith) (by omega_arith) (by omega_arith),
    rd_ne _ B (d := dT + 8) (e := dY + 16) _ (by omega_arith) (by omega_arith) (by omega_arith)]
    simp only [colV, colH, word]
    exact ⟨by ac_rfl, by ac_rfl⟩
  refine WP.mono run fun t ⟨⟨hm, h7, h5, h6⟩, k⟩ => ?_
  obtain ⟨e₀, g₀⟩ := col_val (t := word s.mem B dT) (h := s.gpr .s7) x0 x1 x2 l0 y1 y2 (by omega_arith)
  obtain c₀ : hi57 (s.gpr .s2) (word s.mem B dY) + hi57 (s.gpr .s3) (s.gpr .t5) + hi57 (s.gpr .s4) (s.gpr .t6) ≤
    3 * L57 := by
    obtain a := hi57_le x0 l0; obtain b := hi57_le x1 y1; obtain c := hi57_le x2 y2; omega_using [a, b, c]
  obtain ⟨e₁, g₁⟩ := col_val (t := word s.mem B (dT + 8)) (h := colH (s.gpr .s2) (s.gpr .s3) (s.gpr .s4) (word s.mem B dY)
    (s.gpr .t5) (s.gpr .t6)) x0 x1 x2 l1 l0 y1 (by rw [g₀]; omega_arith)
  obtain c₁ : hi57 (s.gpr .s2) (word s.mem B (dY + 8)) + hi57 (s.gpr .s3) (word s.mem B dY) + hi57 (s.gpr .s4) (s.gpr .t5) ≤
    3 * L57 := by
    obtain a := hi57_le x0 l1; obtain b := hi57_le x1 l0; obtain c := hi57_le x2 y1; omega_using [a, b, c]
  obtain ⟨e₂, g₂⟩ := col_val (t := word s.mem B (dT + 16)) (h := colH (s.gpr .s2) (s.gpr .s3) (s.gpr .s4)
    (word s.mem B (dY + 8)) (word s.mem B dY) (s.gpr .t5)) x0 x1 x2 l2 l1 l0 (by rw [g₁]; omega_arith)
  rw [g₀] at e₁
  rw [g₁] at e₂
  exact ⟨⟨⟨_, _, _, hm, e₀, e₁, e₂⟩, (congrArg BitVec.toNat h7).trans g₂, h5, h6⟩, k⟩

/-! ## The rows -/

/-- The multipliers as a number. -/
abbrev xVal (s : State) : Nat :=
  (s.gpr .s2).toNat + 2 ^ 57 * (s.gpr .s3).toNat + 2 ^ 114 * (s.gpr .s4).toNat

/-- What the columns so far carry: the carry word, and the rest of the products of the last two `y`. -/
abbrev cVal (s : State) : Nat :=
  (s.gpr .s7).toNat + (s.gpr .s3).toNat * (s.gpr .t5).toNat + (s.gpr .s4).toNat * (s.gpr .t6).toNat +
    2 ^ 57 * ((s.gpr .s4).toNat * (s.gpr .t5).toNat)

theorem cols_sum {x₀ x₁ x₂ y₁ y₂ Y₀ Y₁ Y₂ T₀ T₁ T₂ h v₀ v₁ v₂ h' : Nat}
    (e₀ : v₀ = T₀ + h + x₀ * Y₀ % 2 ^ 57 + x₁ * y₁ % 2 ^ 57 + x₂ * y₂ % 2 ^ 57)
    (e₁ : v₁ = T₁ + (x₀ * Y₀ / 2 ^ 57 + x₁ * y₁ / 2 ^ 57 + x₂ * y₂ / 2 ^ 57) + x₀ * Y₁ % 2 ^ 57 + x₁ * Y₀ % 2 ^ 57 +
      x₂ * y₁ % 2 ^ 57)
    (e₂ : v₂ = T₂ + (x₀ * Y₁ / 2 ^ 57 + x₁ * Y₀ / 2 ^ 57 + x₂ * y₁ / 2 ^ 57) + x₀ * Y₂ % 2 ^ 57 + x₁ * Y₁ % 2 ^ 57 +
      x₂ * Y₀ % 2 ^ 57)
    (e₃ : h' = x₀ * Y₂ / 2 ^ 57 + x₁ * Y₁ / 2 ^ 57 + x₂ * Y₀ / 2 ^ 57) :
    v₀ + 2 ^ 57 * v₁ + 2 ^ 114 * v₂ + 2 ^ 171 * (h' + x₁ * Y₂ + x₂ * Y₁ + 2 ^ 57 * (x₂ * Y₂)) =
      T₀ + 2 ^ 57 * T₁ + 2 ^ 114 * T₂ + (h + x₁ * y₁ + x₂ * y₂ + 2 ^ 57 * (x₂ * y₁)) +
        (x₀ + 2 ^ 57 * x₁ + 2 ^ 114 * x₂) * (Y₀ + 2 ^ 57 * Y₁ + 2 ^ 114 * Y₂) := by
  obtain e : (x₀ + 2 ^ 57 * x₁ + 2 ^ 114 * x₂) * (Y₀ + 2 ^ 57 * Y₁ + 2 ^ 114 * Y₂) =
      x₀ * Y₀ + 2 ^ 57 * (x₀ * Y₁ + x₁ * Y₀) + 2 ^ 114 * (x₀ * Y₂ + x₁ * Y₁ + x₂ * Y₀) +
        2 ^ 171 * (x₁ * Y₂ + x₂ * Y₁ + 2 ^ 57 * (x₂ * Y₂)) := by
    grind
  rw [e, e₀, e₁, e₂, e₃]
  obtain d₁ := Nat.div_add_mod (x₀ * Y₀) (2 ^ 57)
  obtain d₂ := Nat.div_add_mod (x₁ * y₁) (2 ^ 57)
  obtain d₃ := Nat.div_add_mod (x₂ * y₂) (2 ^ 57)
  obtain d₄ := Nat.div_add_mod (x₀ * Y₁) (2 ^ 57)
  obtain d₅ := Nat.div_add_mod (x₁ * Y₀) (2 ^ 57)
  obtain d₆ := Nat.div_add_mod (x₂ * y₁) (2 ^ 57)
  obtain d₇ := Nat.div_add_mod (x₀ * Y₂) (2 ^ 57)
  obtain d₈ := Nat.div_add_mod (x₁ * Y₁) (2 ^ 57)
  obtain d₉ := Nat.div_add_mod (x₂ * Y₀) (2 ^ 57)
  clear e e₀ e₁ e₂ e₃
  grind

/-- A do-while loop until two registers are equal, which runs its body `n > 0` times. -/
theorem ptr_loop {body : Prog isa} {a e : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ (s'.gpr a = s'.gpr e ↔ k + 1 = n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.ne a e)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_using [], hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.ne a e) s' = some (decide (k + 1 ≠ n)) := by
    show some (s'.gpr a != s'.gpr e) = _
    by_cases h : s'.gpr a = s'.gpr e
    · simp [h, hc.mp h]
    · obtain h' : ¬k + 1 = n := fun h' => h (hc.mpr h')
      rw [show (s'.gpr a != s'.gpr e) = true from bne_iff_ne.mpr h]
      simp [h']
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi'⟩

theorem off_inj {B : Addr} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : off B a = off B b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  obtain e := congrArg (ofs B) h
  rwa [ofs_off0 B ha, ofs_off0 B hb] at e

/-- What a loop of rows needs of the registers that its columns only read. -/
structure Mult (s : State) : Prop where
  p0 : s.gpr .t2 = s.gpr .s2 <<< 7
  p1 : s.gpr .t3 = s.gpr .s3 <<< 7
  p2 : s.gpr .t4 = s.gpr .s4 <<< 7
  x0 : (s.gpr .s2).toNat ≤ L57
  x1 : (s.gpr .s3).toNat ≤ L57
  x2 : (s.gpr .s4).toNat ≤ L57

theorem Mult.of {s t : State} {rs : List Reg} (h : Mult s) (k : Keep rs s t)
    (hr : ∀ r ∈ [Reg.t2, .t3, .t4, .s2, .s3, .s4], r ∉ rs) : Mult t := by
  obtain g := fun r hr' => k.gpr (r := r) (hr r hr')
  exact ⟨by rw [g .t2 (by decide), g .s2 (by decide), h.p0], by rw [g .t3 (by decide), g .s3 (by decide), h.p1],
    by rw [g .t4 (by decide), g .s4 (by decide), h.p2], by rw [g .s2 (by decide)]; exact h.x0,
    by rw [g .s3 (by decide)]; exact h.x1, by rw [g .s4 (by decide)]; exact h.x2⟩

/-- The registers a loop of rows writes. -/
def rectRegs : List Reg := [.s0, .s1, .s7, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .t0, .t5, .t6]

/-- The most that three rows add to a column. -/
abbrev rowMax : Nat := 6 * L57 + 2 ^ 10

/-- After `k` iterations from `s₀`, at the columns `3 k`. -/
structure Rect (s₀ s : State) (B : Addr) (dT dY : Nat) (f : Nat → Nat) (k : Nat) : Prop where
  a0 : s.gpr .a0 = off B (dT + 24 * k)
  a1 : s.gpr .a1 = off B (dY + 24 * k)
  out : Outside B dT (24 * k) s₀.mem s.mem
  val : lv s.mem B dT (3 * k) + 2 ^ (171 * k) * cVal s =
    lv s₀.mem B dT (3 * k) + cVal s₀ + xVal s₀ * lv s₀.mem B dY (3 * k)
  lim : LimF s.mem B dT (3 * k) fun i => f i + rowMax
  h : (s.gpr .s7).toNat ≤ 3 * L57 + 2 ^ 10
  y1 : (s.gpr .t5).toNat ≤ L57
  y2 : (s.gpr .t6).toNat ≤ L57
  zero : 0 < k → lv s₀.mem B (dY + 24 * (k - 1)) 3 = 0 → cVal s = 0
  keep : Keep rectRegs s₀ s

theorem lv_three_zero {m : Mem} {B : Addr} {d : Nat} (h : lv m B d 3 = 0) :
    (word m B d).toNat = 0 ∧ (word m B (d + 8)).toNat = 0 ∧ (word m B (d + 16)).toNat = 0 := by
  rw [lv_three] at h
  omega_arith

theorem rect_step {W T S c₀ c₁ c₂ X P V t y : Nat} (e₁ : W + P * c₁ = T + c₀ + X * S) (e₂ : V + 2 ^ 171 * c₂ = t + c₁ + X * y) :
    W + P * V + P * 2 ^ 171 * c₂ = T + P * t + c₀ + X * (S + P * y) := by
  obtain e : P * V + P * 2 ^ 171 * c₂ = P * (t + c₁ + X * y) := by rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- Three rows of `3 k` columns. -/
theorem rect_ok {e : Reg} (he : e = .a7 ∨ e = .s5) {s : State} {B : Addr} {Z dT dY k : Nat} {f : Nat → Nat}
    (hs : Scr s B Z) (ha0 : s.gpr .a0 = off B dT) (ha1 : s.gpr .a1 = off B dY) (hse : s.gpr e = off B (dY + 24 * k))
    (hk : 0 < k) (hT : dT + 24 * k ≤ Z) (hY : dY + 24 * k < Z) (hT8 : dT % 8 = 0) (hY8 : dY % 8 = 0)
    (sep : dY + 24 * k ≤ dT ∨ dT + 24 * k ≤ dY) (hx : Mult s)
    (y1 : (s.gpr .t5).toNat ≤ L57) (y2 : (s.gpr .t6).toNat ≤ L57) (lY : Lim s.mem B dY (3 * k) L57)
    (lT : LimF s.mem B dT (3 * k) f) (hh : (s.gpr .s7).toNat ≤ 3 * L57 + 2 ^ 10)
    (hb : ∀ i < 3 * k, f i + 6 * L57 + 2 ^ 10 < 2 ^ 64) :
    WP isa (rect e) s (Rect s · B dT dY f k) := by
  have hn := hs.nowrap
  obtain hZ : dY + 24 * k < 2 ^ 64 := by omega_using [hY, hn]
  unfold rect
  refine ptr_loop hk (fun i t => Rect s t B dT dY f i) (fun i hi t (h : Rect s t B dT dY f i) => ?_)
    ⟨ha0, ha1, Outside.refl _ _ _ _, by simp only [lv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero],
      fun j hj => absurd hj (by omega_using []), hh, y1, y2, fun h => absurd h (by decide), Keep.refl _ _⟩
  obtain g := fun r (hr : r ∉ rectRegs) => h.keep.gpr (r := r) hr
  rw [WP.block_append_iff]
  obtain rdY : ∀ j, j < 3 * k → word t.mem B (dY + 8 * j) = word s.mem B (dY + 8 * j) := fun j hj =>
    h.out.word (by omega_using [sep, hi, hj]) (by omega_using [hZ, hj])
  obtain rdT : ∀ j, j < 3 → word t.mem B (dT + 24 * i + 8 * j) = word s.mem B (dT + 8 * (3 * i + j)) := fun j hj => by
    rw [show dT + 24 * i + 8 * j = dT + 8 * (3 * i + j) by omega_using []]
    exact h.out.word (by omega_using [hj]) (by omega_using [hn, hT, hi, hj])
  refine WP.mono (cols_ok (f := fun j => f (3 * i + j)) (dT := dT + 24 * i) (dY := dY + 24 * i) (hs.congr h.keep.2.2)
    h.a0 h.a1 (by omega_using [hT, hi]) (by omega_using [hY, hi]) (by omega_using [hT8]) (by omega_using [hY8])
    (by omega_using [sep, hi]) (by rw [g .t2 (by decide), g .s2 (by decide), hx.p0]) (by rw [g .t3 (by decide), g .s3 (by decide), hx.p1])
    (by rw [g .t4 (by decide), g .s4 (by decide), hx.p2]) (by rw [g .s2 (by decide)]; exact hx.x0)
    (by rw [g .s3 (by decide)]; exact hx.x1) (by rw [g .s4 (by decide)]; exact hx.x2) h.y1 h.y2
    (fun j hj => by
      rw [show dY + 24 * i + 8 * j = dY + 8 * (3 * i + j) by omega_using [], rdY _ (by omega_using [hi, hj])]
      exact lY _ (by omega_using [hi, hj]))
    (fun j hj => by rw [rdT j hj]; exact lT _ (by omega_using [hi, hj])) h.h
    (fun j hj => hb _ (by omega_using [hi, hj]))) fun u ⟨cu, ku⟩ => ?_
  obtain kr : ∀ r ∈ [Reg.a0, .a1, .s2, .s3, .s4], u.gpr r = t.gpr r := fun r hr => ku.gpr (by revert r hr; decide)
  obtain ⟨v₀, v₁, v₂, hm, e₀, e₁, e₂⟩ := cu.mem
  obtain e₃ := cu.h
  rw [g .s2 (by decide), g .s3 (by decide), g .s4 (by decide)] at e₀ e₁ e₂ e₃
  obtain ou : Outside B (dT + 24 * i) 24 t.mem u.mem := by
    rw [hm]
    exact (((writeW_outside _ B v₀ (by omega_using [hn, hT, hi])).mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside _ B v₁ (by omega_using [hn, hT, hi])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ B v₂ (by omega_using [hn, hT, hi])).mono (by omega_using []) (by omega_using []))
  obtain w₀ : word u.mem B (dT + 24 * i) = v₀ := by
    rw [hm, wd_ne _ B _ (by omega_using []) (by omega_using [hn, hT, hi]) (by omega_using [hn, hT, hi]),
      wd_ne _ B _ (by omega_using []) (by omega_using [hn, hT, hi]) (by omega_using [hn, hT, hi]), word_writeW_self]
  obtain w₁ : word u.mem B (dT + 24 * i + 8) = v₁ := by
    rw [hm, wd_ne _ B _ (by omega_using []) (by omega_using [hn, hT, hi]) (by omega_using [hn, hT, hi]), word_writeW_self]
  obtain w₂ : word u.mem B (dT + 24 * i + 16) = v₂ := by rw [hm, word_writeW_self]
  obtain t₀ := rdT 0 (by decide)
  obtain t₁ := rdT 1 (by decide)
  obtain t₂ := rdT 2 (by decide)
  obtain z₀ := rdY (3 * i) (by omega_using [hi])
  obtain z₁ := rdY (3 * i + 1) (by omega_using [hi])
  obtain z₂ := rdY (3 * i + 2) (by omega_using [hi])
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at t₀ t₁ t₂
  rw [show dY + 8 * (3 * i) = dY + 24 * i by omega_using []] at z₀
  rw [show dY + 8 * (3 * i + 1) = dY + 24 * i + 8 by omega_using []] at z₁
  rw [show dY + 8 * (3 * i + 2) = dY + 24 * i + 16 by omega_using []] at z₂
  rw [t₀, z₀] at e₀
  rw [t₁, z₀, z₁] at e₁
  rw [t₂, z₀, z₁, z₂] at e₂
  rw [z₀, z₁, z₂] at e₃
  obtain sum := cols_sum e₀ e₁ e₂ e₃
  obtain cs : cVal u = (u.gpr .s7).toNat + (s.gpr .s3).toNat * (word s.mem B (dY + 24 * i + 16)).toNat +
      (s.gpr .s4).toNat * (word s.mem B (dY + 24 * i + 8)).toNat +
      2 ^ 57 * ((s.gpr .s4).toNat * (word s.mem B (dY + 24 * i + 16)).toNat) := by
    unfold cVal
    rw [kr .s3 (by decide), kr .s4 (by decide), g .s3 (by decide), g .s4 (by decide), cu.y₁, cu.y₂, z₁, z₂]
  obtain ct : cVal t = (t.gpr .s7).toNat + (s.gpr .s3).toNat * (t.gpr .t5).toNat + (s.gpr .s4).toNat * (t.gpr .t6).toNat +
      2 ^ 57 * ((s.gpr .s4).toNat * (t.gpr .t5).toNat) := by
    unfold cVal
    rw [g .s3 (by decide), g .s4 (by decide)]
  rw [← cs, ← ct] at sum
  obtain l0 := lY (3 * i) (by omega_using [hi])
  obtain l1 := lY (3 * i + 1) (by omega_using [hi])
  obtain l2 := lY (3 * i + 2) (by omega_using [hi])
  rw [show dY + 8 * (3 * i) = dY + 24 * i by omega_using []] at l0
  rw [show dY + 8 * (3 * i + 1) = dY + 24 * i + 8 by omega_using []] at l1
  rw [show dY + 8 * (3 * i + 2) = dY + 24 * i + 16 by omega_using []] at l2
  obtain c₀ : hi57 (s.gpr .s2) (word s.mem B (dY + 24 * i)) + hi57 (s.gpr .s3) (t.gpr .t5) + hi57 (s.gpr .s4) (t.gpr .t6) ≤
    3 * L57 := by
    obtain a := hi57_le hx.x0 l0; obtain b := hi57_le hx.x1 h.y1; obtain c := hi57_le hx.x2 h.y2; omega_using [a, b, c]
  obtain c₁ : hi57 (s.gpr .s2) (word s.mem B (dY + 24 * i + 8)) + hi57 (s.gpr .s3) (word s.mem B (dY + 24 * i)) +
      hi57 (s.gpr .s4) (t.gpr .t5) ≤ 3 * L57 := by
    obtain a := hi57_le hx.x0 l1; obtain b := hi57_le hx.x1 l0; obtain c := hi57_le hx.x2 h.y1; omega_using [a, b, c]
  obtain c₂ : (u.gpr .s7).toNat ≤ 3 * L57 := by
    rw [e₃]
    obtain a := hi57_le hx.x0 l2; obtain b := hi57_le hx.x1 l1; obtain c := hi57_le hx.x2 l0; omega_using [a, b, c]
  obtain lo : ∀ x y : BitVec 64, lo57 x y ≤ L57 := lo57_le
  obtain fin : WP isa (.block [.addi .a0 .a0 24, .addi .a1 .a1 24]) u fun v =>
      (v.gpr .a0 = off B (dT + 24 * i + 24) ∧ v.gpr .a1 = off B (dY + 24 * i + 24) ∧ v.mem = u.mem) ∧
        Keep [.a0, .a1] u v := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [kr .a0 (by decide), kr .a1 (by decide), h.a0, h.a1]
  refine WP.mono fin fun v ⟨⟨a0, a1, vm⟩, kv⟩ => ?_
  obtain cv : cVal v = cVal u := by
    unfold cVal
    rw [kv.gpr (by decide), kv.gpr (by decide), kv.gpr (by decide), kv.gpr (by decide), kv.gpr (by decide)]
  obtain kuv := Keep.trans' (rs := rectRegs) h.keep ((ku.trans kv).mono (by decide))
  refine ⟨⟨a0, a1, ?_, ?_, ?_, ?_, ?_, ?_, fun _ hz => ?_, kuv⟩, ?_⟩
  · rw [vm]
    exact (h.out.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using []))
  · rw [vm, cv, show 3 * (i + 1) = 3 * i + 3 from rfl, lv_append, lv_append s.mem, lv_append s.mem, lv_three, lv_three, lv_three,
      ou.lv (d := dT) (by omega_using []) (by omega_using [hn, hT, hi]),
      show dT + 8 * (3 * i) = dT + 24 * i by omega_using [], show dY + 8 * (3 * i) = dY + 24 * i by omega_using [],
      w₀, w₁, w₂, show 57 * (3 * i) = 171 * i by omega_using [],
      show 2 ^ (171 * (i + 1)) = 2 ^ (171 * i) * 2 ^ 171 by rw [Nat.mul_succ, Nat.pow_add]]
    rw [show dT + 24 * i = dT + 8 * (3 * i) by omega_using [], show dT + 8 * (3 * i) + 8 = dT + 8 * (3 * i + 1) by omega_using [],
      show dT + 8 * (3 * i) + 16 = dT + 8 * (3 * i + 2) by omega_using []]
    exact rect_step h.val sum
  · intro j hj
    rw [vm]
    by_cases hj' : j < 3 * i
    · rw [ou.word (by omega_using [hj']) (by omega_using [hn, hT, hi, hj'])]; exact h.lim j hj'
    · rcases (show j = 3 * i ∨ j = 3 * i + 1 ∨ j = 3 * i + 2 by omega_using [hj, hj']) with rfl | rfl | rfl
      · obtain b := lT (3 * i) (by omega_using [hi])
        obtain a1 := lo (s.gpr .s2) (word s.mem B (dY + 24 * i))
        obtain a2 := lo (s.gpr .s3) (t.gpr .t5)
        obtain a3 := lo (s.gpr .s4) (t.gpr .t6)
        obtain hh := h.h
        rw [show dT + 8 * (3 * i) = dT + 24 * i by omega_using []]
        rw [w₀, e₀]
        show _ ≤ f (3 * i) + (6 * L57 + 2 ^ 10)
        omega_using [b, a1, a2, a3, hh]
      · obtain b := lT (3 * i + 1) (by omega_using [hi])
        obtain a1 := lo (s.gpr .s2) (word s.mem B (dY + 24 * i + 8))
        obtain a2 := lo (s.gpr .s3) (word s.mem B (dY + 24 * i))
        obtain a3 := lo (s.gpr .s4) (t.gpr .t5)
        rw [show dT + 8 * (3 * i + 1) = dT + 24 * i + 8 by omega_using [], w₁, e₁]
        show _ ≤ f (3 * i + 1) + (6 * L57 + 2 ^ 10)
        omega_using [b, a1, a2, a3, c₀]
      · obtain b := lT (3 * i + 2) (by omega_using [hi])
        obtain a1 := lo (s.gpr .s2) (word s.mem B (dY + 24 * i + 16))
        obtain a2 := lo (s.gpr .s3) (word s.mem B (dY + 24 * i + 8))
        obtain a3 := lo (s.gpr .s4) (word s.mem B (dY + 24 * i))
        rw [show dT + 8 * (3 * i + 2) = dT + 24 * i + 16 by omega_using [], w₂, e₂]
        show _ ≤ f (3 * i + 2) + (6 * L57 + 2 ^ 10)
        omega_using [b, a1, a2, a3, c₁]
  · rw [kv.gpr (by decide)]; exact Nat.le_trans c₂ (by omega_using [])
  · rw [kv.gpr (by decide), cu.y₁, z₂]; exact l2
  · rw [kv.gpr (by decide), cu.y₂, z₁]; exact l1
  · rw [show dY + 24 * (i + 1 - 1) = dY + 24 * i by omega_using []] at hz
    obtain ⟨a, b, c⟩ := lv_three_zero hz
    rw [cv, cs, e₃]
    unfold hi57
    rw [a, b, c]
    simp only [Nat.mul_zero, Nat.zero_div, Nat.add_zero]
  · obtain eg : v.gpr e = off B (dY + 24 * k) := by
      rcases he with rfl | rfl <;> rw [kuv.gpr (by decide), hse]
    rw [a1, eg, off_inj (by omega_using [hZ, hi]) hZ]
    omega_using []

/-! ## The working space -/

/-- `A`'s offset, for `M` at `dM`. -/
abbrev oA (q dM : Nat) : Nat := dM + 72 * q + 24
/-- `T`'s offset. -/
abbrev oT (q dM : Nat) : Nat := dM + 144 * q + 48
/-- `E`'s offset. -/
abbrev oE (q dM : Nat) : Nat := dM + 288 * q + 48

/-- The registers and the space of an operation, for `n = 9 q` limbs. -/
structure In (s : State) (B : Addr) (Z q dM : Nat) : Prop where
  scr : Scr s B Z
  q1 : 1 ≤ q
  q6 : q ≤ 6
  dM8 : dM % 8 = 0
  fit : dM + 360 * q + 48 < Z
  a7 : s.gpr .a7 = off B (oA q dM)
  s5 : s.gpr .s5 = off B (oT q dM)

theorem In.of {s t : State} {B : Addr} {Z q dM : Nat} {rs : List Reg} (h : In s B Z q dM) (k : Keep rs s t)
    (h7 : Reg.a7 ∉ rs) (h5 : Reg.s5 ∉ rs) : In t B Z q dM :=
  ⟨h.scr.congr k.2.2, h.q1, h.q6, h.dM8, h.fit, (k.gpr h7).trans h.a7, (k.gpr h5).trans h.s5⟩

/-- The modulus `N` in `M`, and its inverse. -/
structure ModIn (s : State) (B : Addr) (q dM N : Nat) : Prop where
  val : lv s.mem B dM (9 * q) = N
  lim : Lim s.mem B dM (9 * q) L57
  pad : lv s.mem B (dM + 72 * q) 3 = 0
  inv : ((word s.mem B dM).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 57 = 0

theorem sub_off (B : Addr) {a b : Nat} (h : a ≤ b) : off B b - off B a = BitVec.ofNat 64 (b - a) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, off, off, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]

theorem limbs_ok {s : State} {B : Addr} {Z q dM : Nat} (h : In s B Z q dM) :
    WP isa (.block limbs) s fun t => (t.gpr .t2 = BitVec.ofNat 64 (72 * q) ∧ t.mem = s.mem) ∧ Keep [.t2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold limbs
  brun [h.a7, h.s5, sub_off B (show oA q dM ≤ oT q dM by unfold oA oT; omega_arith)]
  rw [show oT q dM - oA q dM = 72 * q + 24 by unfold oA oT; omega_arith, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The mask of a limb. -/
abbrev m57 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 1)

theorem mask57_ok (s : State) :
    WP isa (.block mask57) s fun t => (t.gpr .t6 = m57 ∧ t.mem = s.mem) ∧ Keep [.t6] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold mask57
  brun [exec_li]
  rfl

theorem and_m57 (x : BitVec 64) : (x &&& m57).toNat = x.toNat % 2 ^ 57 := by
  rw [BitVec.toNat_and, show m57.toNat = 2 ^ 57 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem srl57 (x : BitVec 64) : (x >>> 57).toNat = x.toNat / 2 ^ 57 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shl7_and (x : BitVec 64) : x <<< 7 = (x &&& m57) <<< 7 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, and_m57, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega_arith

/-! ## Products and quotients -/

theorem mul57_val {x y : BitVec 64} (hx : x.toNat ≤ L57) :
    (x * y - mh (x <<< 7) y <<< 57).toNat = lo57 x y ∧ (mh (x <<< 7) y).toNat = hi57 x y := by
  obtain hy := y.isLt
  obtain bd : hi57 x y < 2 ^ 64 := by
    unfold hi57 L57 at *
    obtain a := Nat.mul_le_mul hx (Nat.le_of_lt hy)
    omega_using [a]
  obtain e := Nat.div_add_mod (x.toNat * y.toNat) (2 ^ 57)
  obtain b := Nat.mod_lt (x.toNat * y.toNat) (show 2 ^ 57 > 0 by decide)
  unfold mh
  rw [shl7_mul hx]
  refine ⟨?_, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bd]⟩
  obtain key : x * y - BitVec.ofNat 64 (hi57 x y) <<< 57 = BitVec.ofNat 64 (lo57 x y) := by
    rw [BitVec.sub_eq_iff_eq_add, ofNat_shl57, ← BitVec.ofNat_add, mul_ofNat]
    refine congrArg _ ?_
    unfold hi57 lo57
    omega_using [e]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold lo57; omega_using [b])]

theorem mul57_ok {rl rh x xp y tmp : Reg} (s : State) (h1 : rh ≠ x) (h2 : rh ≠ y) (h3 : rl ≠ rh) (h4 : tmp ≠ rl)
    (h5 : tmp ≠ rh) (hp : s.gpr xp = s.gpr x <<< 7) (hx : (s.gpr x).toNat ≤ L57)
    (hw : writesOnly [rl, rh, tmp] (.block (mul57 rl rh x xp y tmp)) = true) :
    WP isa (.block (mul57 rl rh x xp y tmp)) s fun t =>
      ((t.gpr rl).toNat = lo57 (s.gpr x) (s.gpr y) ∧ (t.gpr rh).toNat = hi57 (s.gpr x) (s.gpr y) ∧ t.mem = s.mem) ∧
        Keep [rl, rh, tmp] s t := by
  refine WP.keep _ ?_ hw (by rfl)
  unfold mul57
  brun [↓exec_mh, hp, h1, h2, h3, h4, h5, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  exact mul57_val hx

theorem quot_ok {u up : Reg} (hu : (u = .s2 ∧ up = .t2) ∨ (u = .s3 ∧ up = .t3) ∨ (u = .s4 ∧ up = .t4)) (s : State)
    (h6 : s.gpr .t6 = m57) (hv : (s.gpr .s0).toNat + 2 ^ 57 ≤ 2 ^ 64) :
    WP isa (.block (quot u up .s0)) s fun t =>
      ((t.gpr u).toNat = (s.gpr .s0).toNat * (s.gpr .t1).toNat % 2 ^ 57 ∧ t.gpr up = t.gpr u <<< 7 ∧
        (t.gpr .s0).toNat = ((s.gpr .s0).toNat + (2 ^ 57 - 1)) / 2 ^ 57 ∧ t.mem = s.mem) ∧ Keep [u, up, .s0] s t := by
  obtain a : (s.gpr .s0 * s.gpr .t1 &&& m57).toNat = (s.gpr .s0).toNat * (s.gpr .t1).toNat % 2 ^ 57 := by
    rw [and_m57, BitVec.toNat_mul]
    omega_arith
  obtain b : ((s.gpr .s0 + m57) >>> 57).toNat = ((s.gpr .s0).toNat + (2 ^ 57 - 1)) / 2 ^ 57 := by
    rw [srl57, BitVec.toNat_add, show m57.toNat = 2 ^ 57 - 1 from rfl, Nat.mod_eq_of_lt (by omega_arith)]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold quot
    brun [h6]
    exact ⟨a, shl7_and _, b⟩

/-- The carry of a column `v` that a multiple of the modulus clears. -/
theorem carry_up {v u m mi c : Nat} (hm : (m * mi + 1) % 2 ^ 57 = 0) (hu : u = v * mi % 2 ^ 57)
    (hc : c = (v + (2 ^ 57 - 1)) / 2 ^ 57) : 2 ^ 57 * (c + u * m / 2 ^ 57) = v + u * m := by
  obtain z : (v + u * m) % 2 ^ 57 = 0 := by
    rw [Nat.add_mod, hu, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.mul_assoc, Nat.mul_comm mi m,
      show v + v * (m * mi) = v * (m * mi + 1) by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm], Nat.mul_mod, hm,
      Nat.mul_zero, Nat.zero_mod]
  generalize u * m = p at z ⊢
  subst hc
  omega_arith

/-! ## The reduction -/

theorem toNat_add_lt {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) : (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem red_sum {t₀ t₁ t₂ m₀ m₁ m₂ mi u₀ u₁ u₂ c₀ c₁ c₂ v₁ v₂ h : Nat} (hm : (m₀ * mi + 1) % 2 ^ 57 = 0)
    (eu₀ : u₀ = t₀ * mi % 2 ^ 57) (ec₀ : c₀ = (t₀ + (2 ^ 57 - 1)) / 2 ^ 57)
    (ev₁ : v₁ = c₀ + u₀ * m₀ / 2 ^ 57 + t₁ + u₀ * m₁ % 2 ^ 57)
    (eu₁ : u₁ = v₁ * mi % 2 ^ 57) (ec₁ : c₁ = (v₁ + (2 ^ 57 - 1)) / 2 ^ 57)
    (ev₂ : v₂ = c₁ + u₀ * m₁ / 2 ^ 57 + t₂ + u₁ * m₀ / 2 ^ 57 + u₀ * m₂ % 2 ^ 57 + u₁ * m₁ % 2 ^ 57)
    (eu₂ : u₂ = v₂ * mi % 2 ^ 57) (ec₂ : c₂ = (v₂ + (2 ^ 57 - 1)) / 2 ^ 57)
    (eh : h = u₀ * m₂ / 2 ^ 57 + u₁ * m₁ / 2 ^ 57 + c₂ + u₂ * m₀ / 2 ^ 57) :
    2 ^ 171 * (h + u₁ * m₂ + u₂ * m₁ + 2 ^ 57 * (u₂ * m₂)) =
      t₀ + 2 ^ 57 * t₁ + 2 ^ 114 * t₂ + (u₀ + 2 ^ 57 * u₁ + 2 ^ 114 * u₂) * (m₀ + 2 ^ 57 * m₁ + 2 ^ 114 * m₂) := by
  obtain e₀ := carry_up hm eu₀ ec₀
  obtain e₁ := carry_up hm eu₁ ec₁
  obtain e₂ := carry_up hm eu₂ ec₂
  obtain d₁ := Nat.div_add_mod (u₀ * m₁) (2 ^ 57)
  obtain d₂ := Nat.div_add_mod (u₀ * m₂) (2 ^ 57)
  obtain d₃ := Nat.div_add_mod (u₁ * m₁) (2 ^ 57)
  clear eu₀ eu₁ eu₂ ec₀ ec₁ ec₂ hm
  subst ev₁ ev₂ eh
  obtain x : (u₀ + 2 ^ 57 * u₁ + 2 ^ 114 * u₂) * (m₀ + 2 ^ 57 * m₁ + 2 ^ 114 * m₂) =
      u₀ * m₀ + 2 ^ 57 * (u₀ * m₁ + u₁ * m₀) + 2 ^ 114 * (u₀ * m₂ + u₁ * m₁ + u₂ * m₀) +
        2 ^ 171 * (u₁ * m₂ + u₂ * m₁ + 2 ^ 57 * (u₂ * m₂)) := by
    grind
  rw [x]
  clear x
  grind

/-- The registers the head of a block of the reduction writes. -/
def redHeadRegs : List Reg := [.t2, .a1, .a4, .a5, .a6, .t6, .s0, .s2, .a3, .s1, .a2, .t0, .s3, .t3, .t5, .s7, .s4, .t4, .a0]

theorem redHead_ok {s : State} {B : Addr} {Z q dM N d g : Nat} (h : In s B Z q dM) (hm : ModIn s B q dM N)
    (ha0 : s.gpr .a0 = off B d) (hd8 : d % 8 = 0) (hd : d + 24 ≤ Z) (lT : Lim s.mem B d 3 g)
    (hg : g + 6 * L57 + 2 ^ 10 < 2 ^ 64) :
    WP isa (.block redHead) s fun t =>
      ((Mult t ∧ t.gpr .a0 = off B (d + 24) ∧ t.gpr .a1 = off B (dM + 24) ∧ (t.gpr .s7).toNat ≤ 3 * L57 + 2 ^ 10 ∧
        (t.gpr .t5).toNat ≤ L57 ∧ (t.gpr .t6).toNat ≤ L57 ∧ t.mem = s.mem ∧
        2 ^ 171 * cVal t = lv s.mem B d 3 + xVal t * lv s.mem B dM 3) ∧ Keep redHeadRegs s t) := by
  obtain q1 := h.q1
  obtain fit := h.fit
  obtain dM8 := h.dM8
  obtain l0 := lT 0 (by decide)
  obtain l1 := lT 1 (by decide)
  obtain l2 := lT 2 (by decide)
  obtain n0 := hm.lim 0 (by omega_using [q1])
  obtain n1 := hm.lim 1 (by omega_using [q1])
  obtain n2 := hm.lim 2 (by omega_using [q1])
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at l0 l1 l2 n0 n1 n2
  obtain inv := hm.inv
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  rw [lv_three, lv_three]
  generalize eT0 : word s.mem B d = T0 at l0 ⊢
  generalize eT1 : word s.mem B (d + 8) = T1 at l1 ⊢
  generalize eT2 : word s.mem B (d + 16) = T2 at l2 ⊢
  generalize eM0 : word s.mem B dM = M0 at n0 inv ⊢
  generalize eM1 : word s.mem B (dM + 8) = M1 at n1 ⊢
  generalize eM2 : word s.mem B (dM + 16) = M2 at n2 ⊢
  unfold redHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  obtain r2 : WP isa (.block [.sub .t2 .a7 .t2, .addi .a1 .t2 (-24), .load .d .a4 .a1 0, .load .d .a5 .a1 8,
      .load .d .a6 .a1 16]) s₁ fun t => (t.gpr .a1 = off B dM ∧ t.gpr .a4 = M0 ∧ t.gpr .a5 = M1 ∧ t.gpr .a6 = M2 ∧
        t.mem = s₁.mem) ∧ Keep [.t2, .a1, .a4, .a5, .a6] s₁ t := by
    obtain hs := h.scr.congr k1.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(k1.gpr (r := .a7) (by decide)).trans h.a7, x2, m1, off_sub B (show 72 * q ≤ oA q dM by unfold oA; omega_arith),
      show oA q dM - 72 * q = dM + 24 by unfold oA; omega_arith, off_sub B (show 24 ≤ dM + 24 by omega_arith),
      Nat.add_sub_cancel, hs.ld (show dM + 8 ≤ Z by omega_arith), hs.ld (show dM + 8 + 8 ≤ Z by omega_arith),
      hs.ld (show dM + 16 + 8 ≤ Z by omega_arith), hs.al8 (show dM + 8 ≤ Z by omega_arith) dM8,
      hs.al8 (show dM + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs.al8 (show dM + 16 + 8 ≤ Z by omega_arith) (by omega_arith)]
    exact ⟨eM0, eM1, eM2⟩
  refine WP.mono r2 fun s₂ ⟨⟨a1, a4, a5, a6, m2⟩, k2⟩ => ?_
  obtain K2 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (mask57_ok s₂) fun s₃ ⟨⟨t6, m3⟩, k3⟩ => ?_
  obtain K3 := K2.trans k3
  obtain M3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  rw [WP.block_append_iff]
  obtain hs := h.scr.congr K3.2.2
  obtain r4 : WP isa (.block [.load .d .s0 .a0 0]) s₃ fun t => (t.gpr .s0 = T0 ∧ t.mem = s₃.mem) ∧ Keep [.s0] s₃ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(K3.gpr (r := .a0) (by decide)).trans ha0, M3, hs.ld (show d + 8 ≤ Z by omega_arith),
      hs.al8 (show d + 8 ≤ Z by omega_arith) hd8]
    exact eT0
  refine WP.mono r4 fun s₄ ⟨⟨x0, m4⟩, k4⟩ => ?_
  obtain K4 := K3.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (quot_ok (u := .s2) (up := .t2) (.inl ⟨rfl, rfl⟩) s₄ ((k4.gpr (by decide)).trans t6)
    (by rw [x0]; omega_arith)) fun s₅ ⟨⟨u0, p0, c0, m5⟩, k5⟩ => ?_
  obtain K5 := K4.trans k5
  rw [x0, K4.gpr (r := .t1) (by decide)] at u0
  rw [x0] at c0
  obtain bu0 : (s₅.gpr .s2).toNat ≤ L57 := by rw [u0]; unfold L57; omega_arith
  obtain A4₅ : s₅.gpr .a4 = M0 := by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a4]
  rw [WP.block_append_iff]
  obtain M5 : s₅.mem = s.mem := by rw [m5, m4, M3]
  obtain r6 : WP isa (.block [.mulhu .a3 .t2 .a4, .load .d .s1 .a0 8, .add .s0 .s0 .a3, .add .s0 .s0 .s1]) s₅ fun t =>
      (t.gpr .s0 = s₅.gpr .s0 + mh (s₅.gpr .s2 <<< 7) M0 + T1 ∧ t.mem = s₅.mem) ∧ Keep [.a3, .s1, .s0] s₅ t := by
    obtain hs := h.scr.congr K5.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [↓exec_mh, (K5.gpr (r := .a0) (by decide)).trans ha0, M5, A4₅, p0, hs.ld (show d + 8 + 8 ≤ Z by omega_arith),
      hs.al8 (show d + 8 + 8 ≤ Z by omega_arith) (by omega_arith), show s.mem.readW (off B (d + 8)) 64 = T1 from eT1]
  refine WP.mono r6 fun s₆ ⟨⟨x6, m6⟩, k6⟩ => ?_
  obtain K6 := K5.trans k6
  obtain H0 := (mul57_val (y := M0) bu0).2
  obtain bH0 := hi57_le bu0 n0
  obtain n6 : (s₆.gpr .s0).toNat = (s₅.gpr .s0).toNat + hi57 (s₅.gpr .s2) M0 + T1.toNat := by
    rw [x6, toNat_add_lt (by rw [toNat_add_lt (by rw [H0, c0]; omega_arith), H0, c0]; omega_arith),
      toNat_add_lt (by rw [H0, c0]; omega_arith), H0]
  rw [WP.block_append_iff]
  obtain g6 : ∀ r ∈ [Reg.s2, .t2, .a4, .a5, .a6, .t6], s₆.gpr r = s₅.gpr r := fun r hr => k6.gpr (by revert r hr; decide)
  refine WP.mono (mul57_ok (rl := .a2) (rh := .a3) (x := .s2) (xp := .t2) (y := .a5) (tmp := .t0) s₆ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g6 .t2 (by decide), g6 .s2 (by decide), p0])
    (by rw [g6 .s2 (by decide)]; exact bu0) (by rfl)) fun s₇ ⟨⟨lo01, hi01, m7⟩, k7⟩ => ?_
  obtain K7 := K6.trans k7
  obtain A5₆ : s₆.gpr .a5 = M1 := by rw [k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a5]
  rw [g6 .s2 (by decide), A5₆] at lo01 hi01
  obtain bl01 := lo57_le (s₅.gpr .s2) M1
  obtain bh01 := hi57_le bu0 n1
  obtain r8 : WP isa (.block [.add .s0 .s0 .a2]) s₇ fun t => (t.gpr .s0 = s₇.gpr .s0 + s₇.gpr .a2 ∧ t.mem = s₇.mem) ∧
      Keep [.s0] s₇ t := WP.keep _ (by brun) (by rfl) (by rfl)
  rw [WP.block_append_iff]
  refine WP.mono r8 fun s₈ ⟨⟨x8, m8⟩, k8⟩ => ?_
  obtain K8 := K7.trans k8
  obtain n8 : (s₈.gpr .s0).toNat = (s₅.gpr .s0).toNat + hi57 (s₅.gpr .s2) M0 + T1.toNat + lo57 (s₅.gpr .s2) M1 := by
    rw [x8, k7.gpr (by decide), toNat_add_lt (by rw [n6, lo01, c0]; omega_arith), n6, lo01]
  rw [WP.block_append_iff]
  refine WP.mono (quot_ok (u := .s3) (up := .t3) (.inr (.inl ⟨rfl, rfl⟩)) s₈
    (by rw [k8.gpr (by decide), k7.gpr (by decide), k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), t6])
    (by rw [n8, c0]; omega_arith)) fun s₉ ⟨⟨u1, p1, c1, m9⟩, k9⟩ => ?_
  obtain K9 := K8.trans k9
  rw [K8.gpr (r := .t1) (by decide)] at u1
  obtain bu1 : (s₉.gpr .s3).toNat ≤ L57 := by rw [u1]; omega_arith
  obtain k69 := (k6.trans k7).trans (k8.trans k9)
  obtain g9 : ∀ r ∈ [Reg.s2, .t2, .a4, .a5, .a6, .t6], s₉.gpr r = s₅.gpr r := fun r hr => k69.gpr (by revert r hr; decide)
  obtain M9 : s₉.mem = s.mem := by rw [m9, m8, m7, m6, M5]
  obtain r10 : WP isa (.block [.mulhu .s1 .t3 .a4, .load .d .t5 .a0 16, .add .s0 .s0 .a3, .add .s0 .s0 .t5,
      .add .s0 .s0 .s1]) s₉ fun t => (t.gpr .s0 = s₉.gpr .s0 + s₇.gpr .a3 + T2 + mh (s₉.gpr .s3 <<< 7) M0 ∧
        t.mem = s₉.mem) ∧ Keep [.s1, .t5, .s0] s₉ t := by
    obtain hs := h.scr.congr K9.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [↓exec_mh, (K9.gpr (r := .a0) (by decide)).trans ha0, M9, (g9 .a4 (by decide)).trans A4₅, p1,
      (k9.gpr (r := .a3) (by decide)).trans (k8.gpr (by decide)), hs.ld (show d + 16 + 8 ≤ Z by omega_arith),
      hs.al8 (show d + 16 + 8 ≤ Z by omega_arith) (by omega_arith), show s.mem.readW (off B (d + 16)) 64 = T2 from eT2]
  rw [WP.block_append_iff]
  refine WP.mono r10 fun s₁₀ ⟨⟨x10, m10⟩, k10⟩ => ?_
  obtain K10 := K9.trans k10
  obtain H1 := (mul57_val (y := M0) bu1).2
  obtain bH1 := hi57_le bu1 n0
  obtain n10 : (s₁₀.gpr .s0).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat + hi57 (s₉.gpr .s3) M0 := by
    obtain y1 : (s₉.gpr .s0 + s₇.gpr .a3).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 := by
      rw [toNat_add_lt (by rw [hi01, c1, n8, c0]; omega_arith), hi01]
    obtain y2 : (s₉.gpr .s0 + s₇.gpr .a3 + T2).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat := by
      rw [toNat_add_lt (by rw [y1, c1, n8, c0]; omega_arith), y1]
    rw [x10, toNat_add_lt (by rw [y2, H1, c1, n8, c0]; omega_arith), y2, H1]
  obtain g10 : ∀ r ∈ [Reg.s2, .t2, .a4, .a5, .a6, .t6], s₁₀.gpr r = s₅.gpr r := fun r hr =>
    (k10.gpr (by revert r hr; decide)).trans (g9 r hr)
  obtain A6₅ : s₅.gpr .a6 = M2 := by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a6]
  obtain A5₅ : s₅.gpr .a5 = M1 := by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a5]
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .a2) (rh := .s7) (x := .s2) (xp := .t2) (y := .a6) (tmp := .t0) s₁₀ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g10 .t2 (by decide), g10 .s2 (by decide), p0])
    (by rw [g10 .s2 (by decide)]; exact bu0) (by rfl)) fun s₁₁ ⟨⟨lo02, hi02, m11⟩, k11⟩ => ?_
  obtain K11 := K10.trans k11
  rw [g10 .s2 (by decide), g10 .a6 (by decide), A6₅] at lo02 hi02
  obtain bl02 := lo57_le (s₅.gpr .s2) M2
  obtain bh02 := hi57_le bu0 n2
  rw [WP.block_append_iff]
  obtain r12 : WP isa (.block [.add .s0 .s0 .a2]) s₁₁ fun t => (t.gpr .s0 = s₁₁.gpr .s0 + s₁₁.gpr .a2 ∧ t.mem = s₁₁.mem) ∧
      Keep [.s0] s₁₁ t := WP.keep _ (by brun) (by rfl) (by rfl)
  refine WP.mono r12 fun s₁₂ ⟨⟨x12, m12⟩, k12⟩ => ?_
  obtain K12 := K11.trans k12
  obtain n12 : (s₁₂.gpr .s0).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat + hi57 (s₉.gpr .s3) M0 +
      lo57 (s₅.gpr .s2) M2 := by
    rw [x12, k11.gpr (by decide), toNat_add_lt (by rw [n10, lo02, c1, n8, c0]; omega_arith), n10, lo02]
  obtain k912 := (k10.trans k11).trans k12
  obtain g12 : ∀ r ∈ [Reg.s3, .t3, .s2, .t2, .a4, .a5, .a6, .t6], s₁₂.gpr r = s₉.gpr r := fun r hr =>
    k912.gpr (by revert r hr; decide)
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .a2) (rh := .a3) (x := .s3) (xp := .t3) (y := .a5) (tmp := .t0) s₁₂ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g12 .t3 (by decide), g12 .s3 (by decide), p1])
    (by rw [g12 .s3 (by decide)]; exact bu1) (by rfl)) fun s₁₃ ⟨⟨lo11, hi11, m13⟩, k13⟩ => ?_
  obtain K13 := K12.trans k13
  rw [g12 .s3 (by decide), g12 .a5 (by decide), g9 .a5 (by decide), A5₅] at lo11 hi11
  obtain bl11 := lo57_le (s₉.gpr .s3) M1
  obtain bh11 := hi57_le bu1 n1
  rw [WP.block_append_iff]
  obtain r14 : WP isa (.block [.add .s0 .s0 .a2, .add .s7 .s7 .a3]) s₁₃ fun t => (t.gpr .s0 = s₁₃.gpr .s0 + s₁₃.gpr .a2 ∧
      t.gpr .s7 = s₁₃.gpr .s7 + s₁₃.gpr .a3 ∧ t.mem = s₁₃.mem) ∧
      Keep [.s0, .s7] s₁₃ t := WP.keep _ (by brun) (by rfl) (by rfl)
  refine WP.mono r14 fun s₁₄ ⟨⟨x14, h14, m14⟩, k14⟩ => ?_
  obtain K14 := K13.trans k14
  obtain n14 : (s₁₄.gpr .s0).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat + hi57 (s₉.gpr .s3) M0 +
      lo57 (s₅.gpr .s2) M2 + lo57 (s₉.gpr .s3) M1 := by
    rw [x14, k13.gpr (by decide), toNat_add_lt (by rw [n12, lo11, c1, n8, c0]; omega_arith), n12, lo11]
  obtain h14' : (s₁₄.gpr .s7).toNat = hi57 (s₅.gpr .s2) M2 + hi57 (s₉.gpr .s3) M1 := by
    rw [h14, k13.gpr (by decide), k12.gpr (by decide), toNat_add_lt (by rw [hi02, hi11]; omega_arith), hi02, hi11]
  rw [WP.block_append_iff]
  refine WP.mono (quot_ok (u := .s4) (up := .t4) (.inr (.inr ⟨rfl, rfl⟩)) s₁₄
    (by rw [k14.gpr (by decide), k13.gpr (by decide), g12 .t6 (by decide), g9 .t6 (by decide), k5.gpr (by decide),
      k4.gpr (by decide), t6])
    (by rw [n14, c1, n8, c0]; omega_arith)) fun s₁₅ ⟨⟨u2, p2, c2, m15⟩, k15⟩ => ?_
  obtain K15 := K14.trans k15
  rw [K14.gpr (r := .t1) (by decide)] at u2
  obtain bu2 : (s₁₅.gpr .s4).toNat ≤ L57 := by rw [u2]; omega_arith
  obtain H2 := (mul57_val (y := M0) bu2).2
  obtain bH2 := hi57_le bu2 n0
  obtain k1215 := (k13.trans k14).trans k15
  obtain g15 : ∀ r ∈ [Reg.s3, .t3, .s2, .t2, .a4, .a5, .a6], s₁₅.gpr r = s₉.gpr r := fun r hr =>
    (k1215.gpr (by revert r hr; decide)).trans (g12 r (by revert r hr; decide))
  obtain r16 : WP isa (.block [.mulhu .a3 .t4 .a4, .add .s7 .s7 .s0, .add .s7 .s7 .a3,
      .addi .t5 .a6 0, .addi .t6 .a5 0, .addi .a0 .a0 24, .addi .a1 .a1 24]) s₁₅ fun t =>
      (t.gpr .s7 = s₁₅.gpr .s7 + s₁₅.gpr .s0 + mh (s₁₅.gpr .s4 <<< 7) M0 ∧ t.gpr .t5 = M2 ∧ t.gpr .t6 = M1 ∧
        t.gpr .a0 = off B (d + 24) ∧ t.gpr .a1 = off B (dM + 24) ∧ t.mem = s₁₅.mem) ∧
      Keep [.a3, .s7, .t5, .t6, .a0, .a1] s₁₅ t := by
    obtain e1 : s₁₅.gpr .a1 = off B dM := by
      rw [k1215.gpr (by decide), k912.gpr (by decide), k69.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide),
        k3.gpr (by decide), a1]
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [↓exec_mh, p2, (g15 .a4 (by decide)).trans ((g9 .a4 (by decide)).trans A4₅),
      (g15 .a6 (by decide)).trans ((g9 .a6 (by decide)).trans A6₅),
      (g15 .a5 (by decide)).trans ((g9 .a5 (by decide)).trans A5₅), (K15.gpr (r := .a0) (by decide)).trans ha0, e1,
      BitVec.add_zero]
  refine WP.mono r16 fun t ⟨⟨h7, y5, y6, b0, b1, m16⟩, k16⟩ => ?_
  obtain h7' : (t.gpr .s7).toNat = hi57 (s₅.gpr .s2) M2 + hi57 (s₉.gpr .s3) M1 + (s₁₅.gpr .s0).toNat + hi57 (s₁₅.gpr .s4) M0 := by
    obtain y : (s₁₅.gpr .s7 + s₁₅.gpr .s0).toNat = hi57 (s₅.gpr .s2) M2 + hi57 (s₉.gpr .s3) M1 + (s₁₅.gpr .s0).toNat := by
      rw [k15.gpr (by decide), toNat_add_lt (by rw [h14', c2, n14, c1, n8, c0]; omega_arith), h14']
    rw [h7, toNat_add_lt (by rw [y, H2, c2, n14, c1, n8, c0]; omega_arith), y, H2]
  obtain gs2 : t.gpr .s2 = s₅.gpr .s2 := by rw [k16.gpr (by decide), g15 .s2 (by decide), g9 .s2 (by decide)]
  obtain gs3 : t.gpr .s3 = s₉.gpr .s3 := by rw [k16.gpr (by decide), g15 .s3 (by decide)]
  obtain gs4 : t.gpr .s4 = s₁₅.gpr .s4 := by rw [k16.gpr (by decide)]
  refine ⟨⟨⟨?_, ?_, ?_, by rw [gs2]; exact bu0, by rw [gs3]; exact bu1, by rw [gs4]; exact bu2⟩, b0, b1, ?_, by rw [y5]; exact n2,
    by rw [y6]; exact n1, ?_, ?_⟩, (K15.trans k16).mono (by decide)⟩
  · rw [gs2, k16.gpr (by decide), g15 .t2 (by decide), g9 .t2 (by decide), p0]
  · rw [gs3, k16.gpr (by decide), g15 .t3 (by decide), p1]
  · rw [gs4, k16.gpr (by decide), p2]
  · rw [h7', c2, n14, c1, n8, c0]; omega_arith
  · rw [m16, m15, m14, m13, m12, m11, m10, M9]
  · unfold cVal xVal
    rw [y5, y6, gs2, gs3, gs4]
    exact red_sum inv u0 c0 n8 u1 c1 n14 u2 c2 h7'

/-- The registers an operation writes. -/
def opRegs : List Reg :=
  [.t0, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .s0, .s1, .s2, .s3, .s4, .s7]

theorem ModIn.of {s t : State} {B : Addr} {q dM N o n Z : Nat} {rs : List Reg} (h : ModIn s B q dM N)
    (k : Keep rs s t) (h1 : Reg.t1 ∉ rs) (out : Outside B o n s.mem t.mem) (ho : dM + 72 * q + 24 ≤ o)
    (hs : Scr s B Z) (hZ : dM + 72 * q + 24 ≤ Z) (hq : 1 ≤ q) : ModIn t B q dM N := by
  have hn := hs.nowrap
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [out.lv (by omega_arith) (by omega_arith)]; exact h.val
  · exact out.lim (by omega_arith) (by omega_arith) h.lim
  · rw [out.lv (by omega_arith) (by omega_arith)]; exact h.pad
  · rw [k.gpr h1, out.word (by omega_arith) (by omega_arith)]; exact h.inv

theorem rowNext_ok {s : State} {B : Addr} {Z q dM d : Nat} (h : In s B Z q dM) (ha0 : s.gpr .a0 = off B (d + 72 * q)) :
    WP isa (.block rowNext) s fun t =>
      (t.gpr .a0 = off B d ∧ t.gpr .t3 = off B (oT q dM + 72 * q) ∧ t.mem = s.mem) ∧ Keep [.t2, .a0, .t3] s t := by
  unfold rowNext
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  obtain r : WP isa (.block [.sub .a0 .a0 .t2, .add .t3 .s5 .t2]) s₁ fun t =>
      (t.gpr .a0 = off B d ∧ t.gpr .t3 = off B (oT q dM + 72 * q) ∧ t.mem = s₁.mem) ∧ Keep [.a0, .t3] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [x2, (k1.gpr (r := .a0) (by decide)).trans ha0, (k1.gpr (r := .s5) (by decide)).trans h.s5,
      off_sub B (show 72 * q ≤ d + 72 * q by omega_arith), Nat.add_sub_cancel]
  refine WP.mono r fun t ⟨⟨a0, t3, m2⟩, k2⟩ => ⟨⟨a0, t3, m2.trans m1⟩, (k1.trans k2).mono (by decide)⟩

theorem LimF.append {m : Mem} {B : Addr} {d j k : Nat} {f : Nat → Nat} (h : LimF m B d j f)
    (h' : LimF m B (d + 8 * j) k fun i => f (j + i)) : LimF m B d (j + k) f := fun i hi => by
  by_cases hj : i < j
  · exact h i hj
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hj)
    obtain l := h' c (by omega_arith)
    rw [Nat.mul_add, ← Nat.add_assoc]
    exact l

theorem xVal_lt {s : State} (h : Mult s) : xVal s < 2 ^ 171 := by
  obtain a := h.x0
  obtain b := h.x1
  obtain c := h.x2
  unfold L57 at a b c
  unfold xVal
  omega_using [a, b, c]

theorem lv_split3 (m : Mem) (B : Addr) (d k : Nat) : lv m B d (3 + k) = lv m B d 3 + 2 ^ 171 * lv m B (d + 24) k :=
  lv_append m B d 3 k

/-- After `b` blocks of the reduction of `T` from `s₀`. -/
structure Red (s₀ s : State) (B : Addr) (Z q dM N b : Nat) : Prop where
  ctx : In s B Z q dM
  mod : ModIn s B q dM N
  a0 : s.gpr .a0 = off B (oT q dM + 24 * b)
  out : Outside B (oT q dM) (144 * q) s₀.mem s.mem
  val : ∃ W, W < 2 ^ (171 * b) ∧ 2 ^ (171 * b) * lv s.mem B (oT q dM + 24 * b) (18 * q - 3 * b) =
    lv s₀.mem B (oT q dM) (18 * q) + W * N
  lim : Lim s.mem B (oT q dM + 24 * b) (18 * q - 3 * b) (L57 + b * rowMax)
  keep : Keep opRegs s₀ s

theorem red_step {P V V' T₀ W X N : Nat} (e : P * V = T₀ + W * N) (e' : 2 ^ 171 * V' = V + X * N) :
    P * 2 ^ 171 * V' = T₀ + (W + P * X) * N := by
  rw [Nat.mul_assoc, e', Nat.mul_add, e]
  grind

theorem redRows_ok {s : State} {B : Addr} {Z q dM N : Nat} (h : In s B Z q dM) (hm : ModIn s B q dM N)
    (lT : Lim s.mem B (oT q dM) (18 * q) L57) :
    WP isa redRows s fun t => Red s t B Z q dM N (3 * q) := by
  obtain q1 := h.q1
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  obtain hR : rowMax = 6 * L57 + 2 ^ 10 := rfl
  unfold redRows
  obtain r0 : WP isa (.block [.addi .a0 .s5 0]) s fun t => (t.gpr .a0 = off B (oT q dM) ∧ t.mem = s.mem) ∧ Keep [.a0] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s5, BitVec.add_zero]
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  obtain hm1 : ModIn s₁ B q dM N := ⟨by rw [m1]; exact hm.val, by rw [m1]; exact hm.lim, by rw [m1]; exact hm.pad,
    by rw [m1, k1.gpr (by decide)]; exact hm.inv⟩
  refine ptr_loop (n := 3 * q) (by omega_using [q1]) (fun b t => Red s t B Z q dM N b) (fun b hb t ht => ?_)
    ⟨h.of k1 (by decide) (by decide), hm1, a0, by rw [m1]; exact Outside.refl _ _ _ _,
      ⟨0, Nat.one_pos, by rw [m1]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_mul, Nat.sub_zero]⟩,
      by rw [m1, Nat.zero_mul, Nat.mul_zero, Nat.sub_zero, Nat.add_zero, Nat.add_zero]; exact lT, k1.mono (by decide)⟩
  obtain hbm : b * rowMax ≤ 17 * rowMax := Nat.mul_le_mul_right _ (by omega_using [hb, q6])
  obtain sp : 18 * q - 3 * b = 3 + (9 * q + (9 * q - 3 * (b + 1))) := by omega_using [hb]
  obtain sp' : 18 * q - 3 * (b + 1) = 9 * q + (9 * q - 3 * (b + 1)) := by omega_using [hb]
  refine WP.seq (WP.mono (redHead_ok (d := oT q dM + 24 * b) (g := L57 + b * rowMax) ht.ctx ht.mod ht.a0
    (by unfold oT; omega_using [dM8]) (by unfold oT; omega_using [fit, hb]) (fun i hi => ht.lim i (by omega_using [hi, sp]))
    (by omega_using [hbm, hL, hR])) fun u ⟨⟨mu, ua0, ua1, u7, u5, u6, um, uv⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (rect_ok (e := .a7) (.inl rfl) (k := 3 * q) (f := fun _ => L57 + b * rowMax) (dT := oT q dM + 24 * b + 24)
    (dY := dM + 24) (ht.ctx.scr.congr ku.2.2) ua0 ua1
    (by rw [ku.gpr (by decide), ht.ctx.a7, show oA q dM = dM + 24 + 24 * (3 * q) by unfold oA; omega_using []])
    (by omega_using [q1]) (by unfold oT; omega_using [fit, hb]) (by omega_using [fit]) (by unfold oT; omega_using [dM8])
    (by omega_using [dM8]) (by unfold oT; omega_using []) mu u5 u6 ?_ ?_ u7 (fun i _ => by omega_using [hbm, hL, hR]))
    fun v hv => ?_)
  · intro i hi
    rw [um]
    by_cases hi' : i + 3 < 9 * q
    · rw [show dM + 24 + 8 * i = dM + 8 * (i + 3) by omega_using []]; exact ht.mod.lim _ hi'
    · obtain ⟨z0, z1, z2⟩ := lv_three_zero ht.mod.pad
      rcases (show i = 9 * q - 3 ∨ i = 9 * q - 2 ∨ i = 9 * q - 1 by omega_using [hi, hi']) with rfl | rfl | rfl
      · rw [show dM + 24 + 8 * (9 * q - 3) = dM + 72 * q by omega_using [q1], z0]; exact Nat.zero_le _
      · rw [show dM + 24 + 8 * (9 * q - 2) = dM + 72 * q + 8 by omega_using [q1], z1]; exact Nat.zero_le _
      · rw [show dM + 24 + 8 * (9 * q - 1) = dM + 72 * q + 16 by omega_using [q1], z2]; exact Nat.zero_le _
  · intro i hi
    rw [um, show oT q dM + 24 * b + 24 + 8 * i = oT q dM + 24 * b + 8 * (i + 3) by omega_using []]
    exact ht.lim _ (by omega_using [hi, hb])
  obtain kv := ku.trans hv.keep
  obtain cv := ht.ctx.of kv (by decide) (by decide)
  refine WP.mono (rowNext_ok (d := oT q dM + 24 * b + 24) cv (by rw [hv.a0, show oT q dM + 24 * b + 24 + 24 * (3 * q) =
    oT q dM + 24 * b + 24 + 72 * q by omega_using []])) fun w ⟨⟨wa0, wt3, wm⟩, kw⟩ => ?_
  obtain ov : Outside B (oT q dM + 24 * b + 24) (72 * q) t.mem w.mem := by
    rw [wm, ← um]; exact hv.out.mono (Nat.le_refl _) (by omega_using [])
  obtain ov' : Outside B (oT q dM) (144 * q) t.mem w.mem := ov.mono (by omega_using []) (by omega_using [hb])
  obtain kt := kv.trans kw
  obtain zc : cVal v = 0 := hv.zero (by omega_using [q1]) (by
    rw [um, show dM + 24 + 24 * (3 * q - 1) = dM + 72 * q by omega_using [q1]]; exact ht.mod.pad)
  obtain hMv : lv t.mem B dM 3 + 2 ^ 171 * lv t.mem B (dM + 24) (9 * q) = N := by
    rw [← lv_split3, Nat.add_comm, lv_append, show dM + 8 * (9 * q) = dM + 72 * q by omega_using [], ht.mod.pad, Nat.mul_zero,
      Nat.add_zero, ht.mod.val]
  obtain ev := hv.val
  rw [zc, Nat.mul_zero, Nat.add_zero, um, show 3 * (3 * q) = 9 * q by omega_using []] at ev
  obtain rest : lv w.mem B (oT q dM + 24 * b + 24 + 72 * q) (9 * q - 3 * (b + 1)) =
      lv t.mem B (oT q dM + 24 * b + 24 + 72 * q) (9 * q - 3 * (b + 1)) :=
    ov.lv (by omega_using []) (by unfold oT; omega_using [hn, fit, hb])
  obtain key : 2 ^ 171 * lv w.mem B (oT q dM + 24 * (b + 1)) (18 * q - 3 * (b + 1)) =
      lv t.mem B (oT q dM + 24 * b) (18 * q - 3 * b) + xVal u * N := by
    rw [sp, sp', lv_split3, show oT q dM + 24 * (b + 1) = oT q dM + 24 * b + 24 by omega_using [], lv_append, lv_append,
      show oT q dM + 24 * b + 24 + 8 * (9 * q) = oT q dM + 24 * b + 24 + 72 * q by omega_using [], rest, wm, ev, ← hMv]
    grind
  refine ⟨⟨cv.of kw (by decide) (by decide), ht.mod.of kt (by decide) ov' (by unfold oT; omega_using []) ht.ctx.scr
    (by omega_using [fit]) q1, by rw [wa0, show oT q dM + 24 * b + 24 = oT q dM + 24 * (b + 1) by omega_using []], ht.out.trans ov', ?_, ?_, Keep.trans' ht.keep (kt.mono (by decide))⟩, ?_⟩
  · obtain ⟨W, hW, eW⟩ := ht.val
    refine ⟨W + 2 ^ (171 * b) * xVal u, ?_, ?_⟩
    · rw [Nat.mul_succ, Nat.pow_add]
      obtain l := Nat.mul_le_mul_left (2 ^ (171 * b)) (xVal_lt mu)
      rw [Nat.mul_succ] at l
      omega_using [l, hW]
    · rw [Nat.mul_succ, Nat.pow_add]
      exact red_step eW key
  · refine (?_ : LimF w.mem B (oT q dM + 24 * (b + 1)) (18 * q - 3 * (b + 1)) fun _ => L57 + (b + 1) * rowMax)
    obtain es : L57 + (b + 1) * rowMax = L57 + b * rowMax + rowMax := by rw [Nat.succ_mul, Nat.add_assoc]
    rw [es, show oT q dM + 24 * (b + 1) = oT q dM + 24 * b + 24 by omega_using [], sp']
    refine LimF.append (by rw [wm]; exact (show 9 * q = 3 * (3 * q) by omega_using []) ▸ hv.lim) ?_
    intro i hi
    rw [ov.word (by omega_using []) (by unfold oT; omega_using [hn, fit, hb, hi]),
      show oT q dM + 24 * b + 24 + 8 * (9 * q) + 8 * i = oT q dM + 24 * b + 8 * (9 * q + i + 3) by omega_using []]
    exact Nat.le_trans (ht.lim _ (by omega_using [hi, hb])) (Nat.le_add_right _ _)
  · rw [wa0, wt3, off_inj (by unfold oT; omega_using [hn, fit, hb]) (by unfold oT; omega_using [hn, fit])]
    omega_using []

/-! ## The carry pass -/

/-- After `i` limbs of a carry pass from `dS` to `dD`, from `s₀`. -/
structure Norm (s₀ s : State) (B : Addr) (dS dD i : Nat) : Prop where
  out : Outside B dD (8 * i) s₀.mem s.mem
  val : lv s.mem B dD i + 2 ^ (57 * i) * (s.gpr .t5).toNat = lv s₀.mem B dS i
  lim : Lim s.mem B dD i L57
  cy : (s.gpr .t5).toNat ≤ 2 ^ 10
  t6 : s.gpr .t6 = m57

/-- The registers a step of the carry pass writes. -/
def normRegs : List Reg := [.s0, .s1, .t5]

theorem norm_arith {x c : BitVec 64} (h : x.toNat + c.toNat < 2 ^ 64) :
    ((x + c) &&& m57).toNat ≤ L57 ∧ ((x + c) >>> 57).toNat ≤ 2 ^ 10 ∧
      ((x + c) &&& m57).toNat + 2 ^ 57 * ((x + c) >>> 57).toNat = x.toNat + c.toNat := by
  obtain e := toNat_add_lt h
  rw [and_m57, srl57, e]
  unfold L57
  omega_using [h]

theorem normStep_ok {s₀ s : State} {B : Addr} {Z dS dD i pS pD k n : Nat} (hs : Scr s B Z) (h : Norm s₀ s B dS dD i)
    (ha0 : s.gpr .a0 = off B pS) (ha1 : s.gpr .a1 = off B pD) (eS : pS + k = dS + 8 * i) (eD : pD + k = dD + 8 * i)
    (hi : i < n) (hk : k < 2048) (hS : dS + 8 * n ≤ Z) (hD : dD + 8 * n ≤ Z) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0)
    (sep : dS = dD ∨ dS + 8 * n ≤ dD ∨ dD + 8 * n ≤ dS) (lS : LimF s₀.mem B dS n fun _ => 2 ^ 64 - 2 ^ 10 - 1) :
    WP isa (.block (normStep k)) s fun t => Norm s₀ t B dS dD (i + 1) ∧ Keep normRegs s t := by
  have hn := hs.nowrap
  obtain l : (word s₀.mem B (dS + 8 * i)).toNat ≤ 2 ^ 64 - 2 ^ 10 - 1 := lS i hi
  obtain cy := h.cy
  obtain rd : word s.mem B (dS + 8 * i) = word s₀.mem B (dS + 8 * i) :=
    h.out.word (by omega_using [sep, hi]) (by omega_using [hn, hS, hi])
  obtain ⟨a1, a2, a3⟩ := norm_arith (x := word s₀.mem B (dS + 8 * i)) (c := s.gpr .t5) (by omega_using [l, cy])
  obtain r : WP isa (.block (normStep k)) s fun t =>
      (t.mem = s.mem.writeW (off B (dD + 8 * i)) ((word s₀.mem B (dS + 8 * i) + s.gpr .t5) &&& m57) ∧
        t.gpr .t5 = (word s₀.mem B (dS + 8 * i) + s.gpr .t5) >>> 57) ∧ Keep normRegs s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold normStep
    brun [ha0, ha1, eS, eD, hk, h.t6, hs.ld (show dS + 8 * i + 8 ≤ Z by omega_using [hS, hi]),
      hs.st (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]),
      hs.al8 (show dS + 8 * i + 8 ≤ Z by omega_using [hS, hi]) (by omega_using [hS8]),
      hs.al8 (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]) (by omega_using [hD8]),
      show s.mem.readW (off B (dS + 8 * i)) 64 = word s₀.mem B (dS + 8 * i) from rd]
  refine WP.mono r fun t ⟨⟨mt, t5⟩, k⟩ => ⟨⟨?_, ?_, ?_, by rw [t5]; exact a2, (k.gpr (by decide)).trans h.t6⟩, k⟩
  · rw [mt]
    exact (h.out.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside _ B _ (by omega_using [hn, hD, hi])).mono (by omega_using []) (by omega_using []))
  · obtain v := h.val
    rw [lv, lv, (show lv t.mem B dD i = lv s.mem B dD i by
      rw [mt]; exact (writeW_outside _ B _ (by omega_using [hn, hD, hi])).lv (by omega_using []) (by omega_using [hn, hD, hi])),
      mt, word_writeW_self, t5, ← v, Nat.mul_succ, Nat.pow_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_assoc, ← Nat.mul_add,
      ← Nat.mul_add, a3, Nat.add_comm (s.gpr .t5).toNat]
  · refine LimF.append (j := i) (k := 1) ?_ ?_
    · rw [mt]
      exact (writeW_outside _ B _ (by omega_using [hn, hD, hi])).lim (by omega_using []) (by omega_using [hn, hD, hi]) h.lim
    · intro c hc
      obtain rfl : c = 0 := by omega_using [hc]
      rw [Nat.mul_zero, Nat.add_zero, mt, word_writeW_self]
      exact a1

theorem norm_ok {s : State} {B : Addr} {Z dS dD c : Nat} (hs : Scr s B Z) (ha0 : s.gpr .a0 = off B dS)
    (ha1 : s.gpr .a1 = off B dD) (h3 : s.gpr .t3 = off B (dS + 24 * c)) (hc : 0 < c) (hS : dS + 24 * c < Z)
    (hD : dD + 24 * c ≤ Z) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0)
    (sep : dS = dD ∨ dS + 24 * c ≤ dD ∨ dD + 24 * c ≤ dS) (lS : LimF s.mem B dS (3 * c) fun _ => 2 ^ 64 - 2 ^ 10 - 1) :
    WP isa norm s fun t => (Outside B dD (24 * c) s.mem t.mem ∧
      (∃ k, lv t.mem B dD (3 * c) + 2 ^ (171 * c) * k = lv s.mem B dS (3 * c)) ∧ Lim t.mem B dD (3 * c) L57) ∧
        Keep (([.t6, .a0, .a1] : List Reg) ++ normRegs) s t := by
  have hn := hs.nowrap
  unfold norm
  obtain r0 : WP isa (.block (mask57 ++ ([.li .t5 0] : List Instr))) s fun t =>
      (t.gpr .t6 = m57 ∧ t.gpr .t5 = 0#64 ∧ t.mem = s.mem) ∧ Keep [.t6, .t5] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (mask57_ok s) fun u ⟨⟨u6, um⟩, ku⟩ => ?_
    obtain r : WP isa (.block [.li .t5 0]) u fun t => (t.gpr .t5 = 0#64 ∧ t.mem = u.mem) ∧ Keep [.t5] u t :=
      WP.keep _ (by brun [exec_li]) (by rfl) (by rfl)
    exact WP.mono r fun t ⟨⟨t5, tm⟩, k⟩ => ⟨⟨(k.gpr (by decide)).trans u6, t5, tm.trans um⟩, (ku.trans k).mono (by decide)⟩
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨t6, t5, m1⟩, k1⟩ => ?_)
  refine WP.mono (ptr_loop (a := .a0) (e := .t3) (n := c) hc (fun b t => Norm s t B dS dD (3 * b) ∧ t.gpr .a0 = off B (dS + 24 * b) ∧
      t.gpr .a1 = off B (dD + 24 * b) ∧ Keep (([.t6, .a0, .a1] : List Reg) ++ normRegs) s t) (fun b hb t ⟨ht, t0, t1, kt⟩ => ?_)
    ⟨⟨by rw [m1]; exact Outside.refl _ _ _ _, by rw [t5, m1]; rfl, fun i hi => absurd hi (by omega_using []), by rw [t5]; decide, t6⟩,
      (k1.gpr (by decide)).trans ha0, (k1.gpr (by decide)).trans ha1, k1.mono (by decide)⟩)
    fun t ⟨ht, _, _, kt⟩ => ⟨⟨ht.out.mono (Nat.le_refl _) (by omega_using []), ⟨(t.gpr .t5).toNat, ?_⟩, ht.lim⟩, kt⟩
  · rw [show (List.range 3).flatMap (fun k => normStep (8 * k)) = normStep 0 ++ (normStep 8 ++ normStep 16) by rfl]
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (normStep_ok (n := 3 * c) (hs.congr kt.2.2) ht t0 t1 (by omega_using []) (by omega_using []) (by omega_using [hb]) (by decide)
      (by omega_using [hS]) (by omega_using [hD]) hS8 hD8 (by omega_using [sep]) lS) fun u ⟨hu, ku⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (normStep_ok (n := 3 * c) (hs.congr (kt.trans ku).2.2) hu ((ku.gpr (by decide)).trans t0)
      ((ku.gpr (by decide)).trans t1) (by omega_using []) (by omega_using []) (by omega_using [hb]) (by decide)
      (by omega_using [hS]) (by omega_using [hD]) hS8 hD8 (by omega_using [sep]) lS) fun v ⟨hv, kv⟩ => ?_
    obtain kuv := ku.trans kv
    rw [WP.block_append_iff]
    refine WP.mono (normStep_ok (n := 3 * c) (hs.congr (kt.trans kuv).2.2) hv ((kuv.gpr (by decide)).trans t0)
      ((kuv.gpr (by decide)).trans t1) (by omega_using []) (by omega_using []) (by omega_using [hb]) (by decide)
      (by omega_using [hS]) (by omega_using [hD]) hS8 hD8 (by omega_using [sep]) lS) fun w ⟨hw, kw⟩ => ?_
    obtain kuw := kuv.trans kw
    obtain fin : WP isa (.block [.addi .a0 .a0 24, .addi .a1 .a1 24]) w fun v =>
        (v.gpr .a0 = off B (dS + 24 * b + 24) ∧ v.gpr .a1 = off B (dD + 24 * b + 24) ∧ v.mem = w.mem) ∧
          Keep [.a0, .a1] w v := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [(kuw.gpr (r := .a0) (by decide)).trans t0, (kuw.gpr (r := .a1) (by decide)).trans t1]
    refine WP.mono fin fun x ⟨⟨x0, x1, xm⟩, kx⟩ => ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · rw [xm]; exact hw.out
    · rw [xm, kx.gpr (by decide)]; exact hw.val
    · rw [xm]; exact hw.lim
    · rw [kx.gpr (by decide)]; exact hw.cy
    · rw [kx.gpr (by decide)]; exact hw.t6
    · rw [x0, Nat.mul_succ, Nat.add_assoc]
    · rw [x1, Nat.mul_succ, Nat.add_assoc]
    · exact Keep.trans' kt ((kuw.trans kx).mono (by decide))
    · rw [x0, kx.gpr (by decide), kuw.gpr (by decide), kt.gpr (by decide), h3,
        off_inj (by omega_using [hn, hS, hb]) (by omega_using [hn, hS])]
      omega_using []
  · rw [← ht.val, show 57 * (3 * c) = 171 * c by omega_using []]

/-! ## Zeroing `T` -/

theorem lv_zero {m : Mem} {B : Addr} {d k : Nat} (h : Lim m B d k 0) : lv m B d k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lv, ih fun i hi => h i (by omega_using [hi]), Nat.eq_zero_of_le_zero (h k (Nat.lt_succ_self k))]
    rfl

theorem zeroT57_ok {s : State} {B : Addr} {Z q dM : Nat} (h : In s B Z q dM) :
    WP isa zeroT57 s fun t => (Outside B (oT q dM) (144 * q) s.mem t.mem ∧ Lim t.mem B (oT q dM) (18 * q) 0) ∧
      Keep [.t2, .t3, .t4, .s0] s t := by
  obtain fit := h.fit
  obtain dM8 := h.dM8
  obtain q6 := h.q6
  have hn := h.scr.nowrap
  unfold zeroT57
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  obtain r : WP isa (.block [.shift .sll .d .t2 .t2 1, .add .t4 .s5 .t2, .addi .t3 .s5 0, .li .s0 0]) s₁ fun t =>
      (t.gpr .t4 = off B (oT q dM + 144 * q) ∧ t.gpr .t3 = off B (oT q dM) ∧ t.gpr .s0 = 0#64 ∧ t.mem = s₁.mem) ∧
        Keep [.t2, .t3, .t4, .s0] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    obtain e : BitVec.ofNat 64 (72 * q) <<< 1 = BitVec.ofNat 64 (144 * q) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using []
    brun [x2, (k1.gpr (r := .s5) (by decide)).trans h.s5, e, exec_li, BitVec.add_zero]
  refine WP.mono r fun s₂ ⟨⟨t4, t3, s0, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (ptr_loop (a := .t3) (e := .t4) (n := 6 * q) (by have := h.q1; omega_using [this]) (fun b t => t.gpr .t3 = off B (oT q dM + 24 * b) ∧
      Outside B (oT q dM) (24 * b) s.mem t.mem ∧ Lim t.mem B (oT q dM) (3 * b) 0 ∧ t.gpr .s0 = 0#64 ∧
      t.gpr .t4 = off B (oT q dM + 144 * q) ∧
      Keep [.t2, .t3, .t4, .s0] s t) (fun b hb t ⟨h3, ho, hl, h0, h4, kt⟩ => ?_)
    ⟨t3, by rw [m2, m1]; exact Outside.refl _ _ _ _, fun i hi => absurd hi (by omega_using []), s0, t4, k12.mono (by decide)⟩)
    fun t ⟨_, ho, hl, _, _, kt⟩ => ⟨⟨ho.mono (Nat.le_refl _) (by omega_using []), (show 18 * q = 3 * (6 * q) by omega_using []) ▸ hl⟩, kt⟩
  obtain hs := h.scr.congr kt.2.2
  obtain b1 : oT q dM + 24 * b + 24 ≤ Z := by unfold oT; omega_using [fit, hb]
  obtain b8 : (oT q dM + 24 * b) % 8 = 0 := by unfold oT; omega_using [dM8]
  obtain r : WP isa (.block [.store .d .s0 .t3 0, .store .d .s0 .t3 8, .store .d .s0 .t3 16, .addi .t3 .t3 24]) t fun u =>
      (u.mem = ((t.mem.writeW (off B (oT q dM + 24 * b)) 0#64).writeW (off B (oT q dM + 24 * b + 8)) 0#64).writeW
        (off B (oT q dM + 24 * b + 16)) 0#64 ∧ u.gpr .t3 = off B (oT q dM + 24 * b + 24)) ∧ Keep [.t3] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h3, h0, hs.st (show oT q dM + 24 * b + 8 ≤ Z by omega_using [b1]),
      hs.st (show oT q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]),
      hs.st (show oT q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]),
      hs.al8 (show oT q dM + 24 * b + 8 ≤ Z by omega_using [b1]) b8,
      hs.al8 (show oT q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8]),
      hs.al8 (show oT q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8])]
  refine WP.mono r fun u ⟨⟨um, u3⟩, ku⟩ => ?_
  obtain ou : Outside B (oT q dM + 24 * b) 24 t.mem u.mem := by
    rw [um]
    exact (((writeW_outside _ B _ (by omega_using [hn, b1])).mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside _ B _ (by omega_using [hn, b1])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ B _ (by omega_using [hn, b1])).mono (by omega_using []) (by omega_using []))
  refine ⟨⟨by rw [u3, Nat.mul_succ, Nat.add_assoc], (ho.mono (Nat.le_refl _) (by omega_using [])).trans
    (ou.mono (by omega_using []) (by omega_using [])), ?_, (ku.gpr (by decide)).trans h0, (ku.gpr (by decide)).trans h4,
    Keep.trans' kt (ku.mono (by decide))⟩, ?_⟩
  · refine LimF.append (j := 3 * b) (k := 3) (ou.lim (by omega_using []) (by omega_using [hn, b1]) hl) ?_
    rw [show oT q dM + 8 * (3 * b) = oT q dM + 24 * b by omega_using []]
    intro i hi
    rw [um]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
    · rw [show oT q dM + 24 * b + 8 * 0 = oT q dM + 24 * b by omega_using [], wd_ne _ B _ (by omega_using []) (by omega_using [hn, b1]) (by omega_using [hn, b1]),
        wd_ne _ B _ (by omega_using []) (by omega_using [hn, b1]) (by omega_using [hn, b1]), word_writeW_self]
      exact Nat.le_refl 0
    · rw [Nat.mul_one, wd_ne _ B _ (by omega_using []) (by omega_using [hn, b1]) (by omega_using [hn, b1]), word_writeW_self]
      exact Nat.le_refl 0
    · rw [word_writeW_self]
      exact Nat.le_refl 0
  · rw [u3, ku.gpr (by decide), h4, off_inj (by unfold oT; omega_using [hn, fit, hb]) (by unfold oT; omega_using [hn, fit])]
    omega_using []

/-! ## The whole reduction -/

/-- The number `a` in `A`. -/
structure AIn (m : Mem) (B : Addr) (q dM a : Nat) : Prop where
  val : lv m B (oA q dM) (9 * q) = a
  lim : Lim m B (oA q dM) (9 * q) L57
  pad : lv m B (oA q dM + 72 * q) 3 = 0

/-- What the reduction writes: `A` and `T`. -/
abbrev OutAT (B : Addr) (q dM : Nat) (m m' : Mem) : Prop := Outside B (oA q dM) (216 * q + 24) m m'

theorem outT {B : Addr} {q dM : Nat} {m m' : Mem} (h : Outside B (oT q dM) (144 * q) m m') : OutAT B q dM m m' :=
  Outside.mono h (by unfold oA oT; omega_using []) (by unfold oA oT; omega_using [])

theorem reduce57_ok {s : State} {B : Addr} {Z q dM N V : Nat} (h : In s B Z q dM) (hm : ModIn s B q dM N)
    (lT : Lim s.mem B (oT q dM) (18 * q) L57) (eV : lv s.mem B (oT q dM) (18 * q) = V)
    (hV : V + 2 ^ (513 * q) * N ≤ 2 ^ (513 * q) * 2 ^ (513 * q)) (hN : 0 < N)
    (pad : lv s.mem B (oA q dM + 72 * q) 3 = 0) :
    WP isa reduce57 s fun t => (In t B Z q dM ∧ ModIn t B q dM N ∧ OutAT B q dM s.mem t.mem ∧
      ∃ a W, AIn t.mem B q dM a ∧ W < 2 ^ (513 * q) ∧ 2 ^ (513 * q) * a = V + W * N) ∧ Keep opRegs s t := by
  obtain q1 := h.q1
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  unfold reduce57
  refine WP.seq (WP.mono (redRows_ok h hm lT) fun s₁ hr => ?_)
  obtain ⟨W, hW, eW⟩ := hr.val
  rw [eV, show 171 * (3 * q) = 513 * q by omega_using [], show 18 * q - 3 * (3 * q) = 9 * q by omega_using [],
    show oT q dM + 24 * (3 * q) = oT q dM + 72 * q by omega_using []] at eW
  rw [show 171 * (3 * q) = 513 * q by omega_using []] at hW
  obtain rl := hr.lim
  rw [show 18 * q - 3 * (3 * q) = 9 * q by omega_using [], show oT q dM + 24 * (3 * q) = oT q dM + 72 * q by omega_using []] at rl
  obtain X : lv s₁.mem B (oT q dM + 72 * q) (9 * q) < 2 ^ (513 * q) := by
    obtain l := (Nat.mul_lt_mul_right hN).mpr hW
    exact Nat.lt_of_mul_lt_mul_left (a := 2 ^ (513 * q)) (by rw [eW]; omega_using [l, hV])
  obtain r : WP isa (.block (limbs ++ ([.add .a0 .s5 .t2, .addi .a1 .a7 0, .add .t3 .a0 .t2] : List Instr))) s₁ fun t =>
      (t.gpr .a0 = off B (oT q dM + 72 * q) ∧ t.gpr .a1 = off B (oA q dM) ∧
        t.gpr .t3 = off B (oT q dM + 72 * q + 72 * q) ∧ t.mem = s₁.mem) ∧ Keep [.t2, .a0, .a1, .t3] s₁ t := by
    rw [WP.block_append_iff]
    refine WP.mono (limbs_ok hr.ctx) fun u ⟨⟨x2, um⟩, ku⟩ => ?_
    obtain r : WP isa (.block [.add .a0 .s5 .t2, .addi .a1 .a7 0, .add .t3 .a0 .t2]) u fun t =>
      (t.gpr .a0 = off B (oT q dM + 72 * q) ∧ t.gpr .a1 = off B (oA q dM) ∧
        t.gpr .t3 = off B (oT q dM + 72 * q + 72 * q) ∧ t.mem = u.mem) ∧ Keep [.a0, .a1, .t3] u t := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [x2, (ku.gpr (r := .s5) (by decide)).trans hr.ctx.s5, (ku.gpr (r := .a7) (by decide)).trans hr.ctx.a7, BitVec.add_zero]
    exact WP.mono r fun t ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c, d.trans um⟩, (ku.trans k).mono (by decide)⟩
  refine WP.seq (WP.mono r fun s₂ ⟨⟨a0, a1, t3, m2⟩, k2⟩ => ?_)
  obtain K2 := hr.keep.trans k2
  refine WP.mono (norm_ok (c := 3 * q) (dS := oT q dM + 72 * q) (dD := oA q dM) (h.scr.congr K2.2.2) a0 a1
    (by rw [t3, show 24 * (3 * q) = 72 * q by omega_using []]) (by omega_using [q1]) (by unfold oT; omega_using [fit])
    (by unfold oA; omega_using [fit]) (by unfold oT; omega_using [dM8]) (by unfold oA; omega_using [dM8])
    (by unfold oA oT; omega_using []) (by
      rw [m2, show 3 * (3 * q) = 9 * q by omega_using []]
      intro i hi
      refine Nat.le_trans (rl i hi) ?_
      obtain b : 3 * q * rowMax ≤ 18 * rowMax := Nat.mul_le_mul_right _ (by omega_using [q6])
      obtain hL : L57 = 2 ^ 57 - 1 := rfl
      obtain hR : rowMax = 6 * L57 + 2 ^ 10 := rfl
      show L57 + 3 * q * rowMax ≤ 2 ^ 64 - 2 ^ 10 - 1
      omega_using [b, hL, hR])) fun t ⟨⟨ot, ⟨k, et⟩, lt⟩, kt⟩ => ?_
  rw [m2] at ot et
  rw [show 3 * (3 * q) = 9 * q by omega_using [], show 171 * (3 * q) = 513 * q by omega_using []] at et
  rw [show 3 * (3 * q) = 9 * q by omega_using []] at lt
  rw [show 24 * (3 * q) = 72 * q by omega_using []] at ot
  obtain hk : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · obtain l := Nat.le_mul_of_pos_right (2 ^ (513 * q)) h
      omega_using [l, et, X]
  subst hk
  rw [Nat.mul_zero, Nat.add_zero] at et
  obtain KT := K2.trans kt
  refine ⟨⟨h.of (KT.mono (rs' := opRegs) (by decide)) (by decide) (by decide), ?_, ?_, _, W, ⟨rfl, lt, ?_⟩, hW, by rw [et]; exact eW⟩, KT.mono (by decide)⟩
  · exact hr.mod.of (k2.trans kt) (by decide) ot (by unfold oA; omega_using []) (h.scr.congr hr.keep.2.2)
      (by omega_using [fit]) q1
  · exact (outT hr.out).trans (ot.mono (Nat.le_refl _) (by omega_using []))
  · rw [ot.lv (by omega_using []) (by unfold oA; omega_using [hn, fit]),
      hr.out.lv (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit])]
    exact pad

/-! ## The product -/

theorem lv_seg {m m' : Mem} {B : Addr} {d j k r δ : Nat} (out : Outside B (d + 8 * j) (8 * k) m m')
    (e : lv m' B (d + 8 * j) k = lv m B (d + 8 * j) k + δ) (hd : d + 8 * (j + k + r) ≤ 2 ^ 64) :
    lv m' B d (j + k + r) = lv m B d (j + k + r) + 2 ^ (57 * j) * δ := by
  rw [lv_append, lv_append m', lv_append m, lv_append m, e,
    out.lv (d := d) (by omega_using []) (by omega_using [hd]),
    out.lv (d := d + 8 * (j + k)) (by omega_using []) (by omega_using [hd]), Nat.mul_add]
  omega_using []

theorem lim_seg {m m' : Mem} {B : Addr} {d j k r : Nat} {f g : Nat → Nat} (out : Outside B (d + 8 * j) (8 * k) m m')
    (h : LimF m B d (j + k + r) f) (h' : LimF m' B (d + 8 * j) k fun i => g (j + i)) (hfg : ∀ i, f i ≤ g i)
    (hd : d + 8 * (j + k + r) ≤ 2 ^ 64) : LimF m' B d (j + k + r) g := by
  refine LimF.append (LimF.append ?_ h') ?_
  · intro i hi
    rw [out.word (by omega_using [hi]) (by omega_using [hi, hd])]
    exact Nat.le_trans (h i (by omega_using [hi])) (hfg i)
  · intro i hi
    rw [out.word (by omega_using []) (by omega_using [hi, hd]), show d + 8 * (j + k) + 8 * i = d + 8 * (j + k + i) by omega_using []]
    exact Nat.le_trans (h (j + k + i) (by omega_using [hi])) (hfg _)

theorem zeros (s : State) : WP isa (.block [.li .t5 0, .li .t6 0, .li .s7 0, .addi .a1 .a7 0]) s fun t =>
    (t.gpr .t5 = 0#64 ∧ t.gpr .t6 = 0#64 ∧ t.gpr .s7 = 0#64 ∧ t.gpr .a1 = s.gpr .a7 ∧ t.mem = s.mem) ∧
      Keep [.t5, .t6, .s7, .a1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [exec_li, BitVec.add_zero]

theorem rectX_ok (s : State) : WP isa (.block rectX) s fun t => (t.gpr .t2 = s.gpr .s2 <<< 7 ∧ t.gpr .t3 = s.gpr .s3 <<< 7 ∧
    t.gpr .t4 = s.gpr .s4 <<< 7 ∧ t.mem = s.mem) ∧ Keep [.t2, .t3, .t4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold rectX
  brun

theorem shl1 (n : Nat) (h : n < 2 ^ 63) : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using [h]

def mulHeadRegs : List Reg := [.t2, .a2, .s2, .s3, .s4, .t3, .t4, .t5, .t6, .s7, .a1]

theorem mulHead_ok {s : State} {B : Addr} {Z q dM b : Nat} (h : In s B Z q dM) (ha0 : s.gpr .a0 = off B (oT q dM + 24 * b))
    (hb : b < 3 * q) (lE : Lim s.mem B (oE q dM) (9 * q) L57) :
    WP isa (.block mulHead) s fun t =>
      (Mult t ∧ t.gpr .a1 = off B (oA q dM) ∧ t.gpr .s7 = 0#64 ∧ t.gpr .t5 = 0#64 ∧ t.gpr .t6 = 0#64 ∧
        xVal t = lv s.mem B (oE q dM + 24 * b) 3 ∧ t.mem = s.mem) ∧ Keep mulHeadRegs s t := by
  obtain fit := h.fit
  obtain dM8 := h.dM8
  obtain q6 := h.q6
  unfold mulHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  obtain hs := h.scr.congr k1.2.2
  obtain b1 : oE q dM + 24 * b + 24 ≤ Z := by unfold oE; omega_using [fit, hb]
  obtain b8 : (oE q dM + 24 * b) % 8 = 0 := by unfold oE; omega_using [dM8]
  obtain r : WP isa (.block [.shift .sll .d .t2 .t2 1, .add .a2 .a0 .t2, .load .d .s2 .a2 0, .load .d .s3 .a2 8,
      .load .d .s4 .a2 16]) s₁ fun t => (t.gpr .s2 = word s.mem B (oE q dM + 24 * b) ∧
        t.gpr .s3 = word s.mem B (oE q dM + 24 * b + 8) ∧ t.gpr .s4 = word s.mem B (oE q dM + 24 * b + 16) ∧ t.mem = s₁.mem) ∧
      Keep [.t2, .a2, .s2, .s3, .s4] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [x2, shl1 (72 * q) (by omega_using [q6]), (k1.gpr (r := .a0) (by decide)).trans ha0,
      show oT q dM + 24 * b + 2 * (72 * q) = oE q dM + 24 * b by unfold oT oE; omega_using [], m1,
      hs.ld (show oE q dM + 24 * b + 8 ≤ Z by omega_using [b1]), hs.ld (show oE q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]),
      hs.ld (show oE q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]), hs.al8 (show oE q dM + 24 * b + 8 ≤ Z by omega_using [b1]) b8,
      hs.al8 (show oE q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8]),
      hs.al8 (show oE q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8])]
  refine WP.mono r fun s₂ ⟨⟨x0, x1, x2', m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rectX_ok s₂) fun s₃ ⟨⟨p0, p1, p2, m3⟩, k3⟩ => ?_
  refine WP.mono (zeros s₃) fun t ⟨⟨t5, t6, t7, a1, m4⟩, k4⟩ => ?_
  obtain K4 := ((k1.trans k2).trans k3).trans k4
  obtain g : ∀ r ∈ [Reg.s2, .s3, .s4], t.gpr r = s₂.gpr r := fun r hr => (k3.trans k4).gpr (by revert r hr; decide)
  obtain l0 := lE (3 * b) (by omega_using [hb])
  obtain l1 := lE (3 * b + 1) (by omega_using [hb])
  obtain l2 := lE (3 * b + 2) (by omega_using [hb])
  rw [show oE q dM + 8 * (3 * b) = oE q dM + 24 * b by omega_using []] at l0
  rw [show oE q dM + 8 * (3 * b + 1) = oE q dM + 24 * b + 8 by omega_using []] at l1
  rw [show oE q dM + 8 * (3 * b + 2) = oE q dM + 24 * b + 16 by omega_using []] at l2
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, t7, t5, t6, ?_, by rw [m4, m3, m2, m1]⟩, K4.mono (by decide)⟩
  · rw [k4.gpr (by decide), p0, g .s2 (by decide)]
  · rw [k4.gpr (by decide), p1, g .s3 (by decide)]
  · rw [k4.gpr (by decide), p2, g .s4 (by decide)]
  · rw [g .s2 (by decide), x0]; exact l0
  · rw [g .s3 (by decide), x1]; exact l1
  · rw [g .s4 (by decide), x2']; exact l2
  · rw [a1, k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), h.a7]
  · unfold xVal
    rw [g .s2 (by decide), g .s3 (by decide), g .s4 (by decide), x0, x1, x2', lv_three]

/-- After `b` blocks of the product `T = A E`, from `s₀`. -/
structure MulI (s₀ s : State) (B : Addr) (Z q dM b : Nat) : Prop where
  ctx : In s B Z q dM
  a0 : s.gpr .a0 = off B (oT q dM + 24 * b)
  out : Outside B (oT q dM) (144 * q) s₀.mem s.mem
  val : lv s.mem B (oT q dM) (18 * q) = lv s₀.mem B (oA q dM) (9 * q) * lv s₀.mem B (oE q dM) (3 * b)
  lim : Lim s.mem B (oT q dM) (18 * q) (b * rowMax)
  keep : Keep opRegs s₀ s

theorem cVal_zero {s : State} (h7 : s.gpr .s7 = 0#64) (h5 : s.gpr .t5 = 0#64) (h6 : s.gpr .t6 = 0#64) : cVal s = 0 := by
  unfold cVal
  rw [h7, h5, h6]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]

theorem AIn.pads {m : Mem} {B : Addr} {q dM a : Nat} (h : AIn m B q dM a) : lv m B (oA q dM) (9 * q + 3) = a := by
  rw [lv_append, show oA q dM + 8 * (9 * q) = oA q dM + 72 * q by omega_using [], h.pad, h.val, Nat.mul_zero, Nat.add_zero]

theorem pad_lim {m : Mem} {B : Addr} {d k : Nat} (h : Lim m B d k L57) (p : lv m B (d + 8 * k) 3 = 0) : Lim m B d (k + 3) L57 := by
  refine LimF.append h fun i hi => ?_
  obtain ⟨z0, z1, z2⟩ := lv_three_zero p
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
  · rw [Nat.mul_zero, Nat.add_zero, z0]; exact Nat.zero_le _
  · rw [Nat.mul_one, z1]; exact Nat.zero_le _
  · rw [z2]; exact Nat.zero_le _

theorem mulRows_ok {s : State} {B : Addr} {Z q dM a : Nat} (h : In s B Z q dM) (hA : AIn s.mem B q dM a)
    (lE : Lim s.mem B (oE q dM) (9 * q) L57) (lT : Lim s.mem B (oT q dM) (18 * q) 0) :
    WP isa mulRows s fun t => MulI s t B Z q dM (3 * q) := by
  obtain q1 := h.q1
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  obtain hR : rowMax = 6 * L57 + 2 ^ 10 := rfl
  unfold mulRows
  obtain r0 : WP isa (.block [.addi .a0 .s5 0]) s fun t => (t.gpr .a0 = off B (oT q dM) ∧ t.mem = s.mem) ∧ Keep [.a0] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s5, BitVec.add_zero]
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  refine ptr_loop (n := 3 * q) (by omega_using [q1]) (fun b t => MulI s t B Z q dM b) (fun b hb t ht => ?_)
    ⟨h.of k1 (by decide) (by decide), a0, by rw [m1]; exact Outside.refl _ _ _ _, by
      rw [m1, lv_zero lT]; rfl, by rw [m1, Nat.zero_mul]; exact lT, k1.mono (by decide)⟩
  obtain hbm : b * rowMax ≤ 17 * rowMax := Nat.mul_le_mul_right _ (by omega_using [hb, q6])
  obtain sp : 18 * q = 3 * b + (9 * q + 3) + (9 * q - 3 * (b + 1)) := by omega_using [hb]
  obtain ht18 := ht.lim
  refine WP.seq (WP.mono (mulHead_ok ht.ctx ht.a0 hb (ht.out.lim (by unfold oE oT; omega_using []) (by unfold oE; omega_using [hn, fit]) lE))
    fun u ⟨⟨mu, ua1, u7, u5, u6, ux, um⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (rect_ok (e := .s5) (.inr rfl) (k := 3 * q + 1) (f := fun _ => b * rowMax) (dT := oT q dM + 24 * b)
    (dY := oA q dM) (ht.ctx.scr.congr ku.2.2) ((ku.gpr (by decide)).trans ht.a0) ua1
    (by rw [ku.gpr (by decide), ht.ctx.s5, show oT q dM = oA q dM + 24 * (3 * q + 1) by unfold oA oT; omega_using []])
    (by omega_using []) (by unfold oT; omega_using [fit, hb]) (by unfold oA; omega_using [fit, q1]) (by unfold oT; omega_using [dM8])
    (by unfold oA; omega_using [dM8]) (by unfold oA oT; omega_using []) mu (by rw [u5]; decide) (by rw [u6]; decide) ?_ ?_
    (by rw [u7]; decide) (fun i _ => by omega_using [hbm, hL, hR]))
    fun v hv => ?_)
  · rw [um, show 3 * (3 * q + 1) = 9 * q + 3 by omega_using []]
    exact ht.out.lim (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit, q1])
      (pad_lim hA.lim (by rw [show oA q dM + 8 * (9 * q) = oA q dM + 72 * q by omega_using []]; exact hA.pad))
  · intro i hi
    rw [um, show oT q dM + 24 * b + 8 * i = oT q dM + 8 * (3 * b + i) by omega_using []]
    exact ht18 (3 * b + i) (by omega_using [hi, hb])
  obtain kv := ku.trans hv.keep
  obtain cv := ht.ctx.of kv (by decide) (by decide)
  refine WP.mono (rowNext_ok (d := oT q dM + 24 * b + 24) cv (by rw [hv.a0, show oT q dM + 24 * b + 24 * (3 * q + 1) =
    oT q dM + 24 * b + 24 + 72 * q by omega_using []])) fun w ⟨⟨wa0, wt3, wm⟩, kw⟩ => ?_
  obtain ov : Outside B (oT q dM + 8 * (3 * b)) (8 * (9 * q + 3)) t.mem w.mem := by
    rw [wm, ← um]; exact hv.out.mono (by omega_using []) (by omega_using [])
  obtain ov' : Outside B (oT q dM) (144 * q) t.mem w.mem := ov.mono (by omega_using []) (by omega_using [hb])
  obtain kt := kv.trans kw
  obtain eA : lv t.mem B (oA q dM) (9 * q + 3) = a := by
    rw [ht.out.lv (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit, q1])]; exact hA.pads
  obtain zc : cVal v = 0 := hv.zero (by omega_using []) (by
    rw [um, show oA q dM + 24 * (3 * q + 1 - 1) = oA q dM + 72 * q by omega_using [],
      ht.out.lv (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit, q1])]
    exact hA.pad)
  obtain ev := hv.val
  rw [zc, Nat.mul_zero, Nat.add_zero, um, show 3 * (3 * q + 1) = 9 * q + 3 by omega_using [], cVal_zero u7 u5 u6, Nat.add_zero, eA, ux,
    show oT q dM + 24 * b = oT q dM + 8 * (3 * b) by omega_using [], ← wm,
    ht.out.lv (d := oE q dM + 24 * b) (by unfold oE oT; omega_using []) (by unfold oE; omega_using [hn, fit, hb])] at ev
  obtain bd : oT q dM + 8 * (3 * b + (9 * q + 3) + (9 * q - 3 * (b + 1))) ≤ 2 ^ 64 := by
    rw [← sp]; unfold oT; omega_using [hn, fit]
  refine ⟨⟨cv.of kw (by decide) (by decide), by rw [wa0, show oT q dM + 24 * b + 24 = oT q dM + 24 * (b + 1) by omega_using []],
    ht.out.trans ov', ?_, ?_, Keep.trans' ht.keep (kt.mono (by decide))⟩, ?_⟩
  · rw [sp, lv_seg ov ev bd, ← sp, ht.val, hA.val, show 3 * (b + 1) = 3 * b + 3 from rfl, lv_append,
      show oE q dM + 8 * (3 * b) = oE q dM + 24 * b by omega_using []]
    grind
  · rw [sp] at ht18 ⊢
    refine lim_seg ov ht18 ?_ (fun _ => Nat.mul_le_mul_right _ (Nat.le_succ b)) bd
    obtain l := hv.lim
    rw [← wm, show 3 * (3 * q + 1) = 9 * q + 3 by omega_using [], show oT q dM + 24 * b = oT q dM + 8 * (3 * b) by omega_using [],
      ← Nat.succ_mul] at l
    exact l
  · rw [wa0, wt3, off_inj (by unfold oT; omega_using [hn, fit, hb]) (by unfold oT; omega_using [hn, fit])]
    omega_using []

/-! ## The square: the cross products -/

/-- The extra of column `c` in block `b`'s head. -/
def sqE (b c : Nat) : Nat :=
  (if c = 6 * b + 1 then 1 else 0) + (if c = 6 * b + 2 then 2 else 0) + (if c = 6 * b + 4 then 1 else 0)

/-- How many limbs the first `b` blocks of rows add at most to column `c` of a square of `n` limbs. -/
def sqB (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | b + 1, c => sqB n b c + (sqE b c + if 6 * b + 3 ≤ c ∧ c < n + 3 * b + 3 then 6 else 0)

theorem sqB_mono (n c b k : Nat) : sqB n b c ≤ sqB n (b + k) c := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem sqB_le' : ∀ q < 7, ∀ c < 108, sqB (9 * q) (3 * q) c ≤ 60 := by decide +kernel

theorem sqB_le {q b c : Nat} (hq : q ≤ 6) (hb : b ≤ 3 * q) (hc : c < 18 * q) : sqB (9 * q) b c ≤ 60 := by
  obtain ⟨k, e⟩ := Nat.exists_eq_add_of_le hb
  refine Nat.le_trans (sqB_mono (9 * q) c b k) ?_
  rw [← e]
  exact sqB_le' q (by omega_using [hq]) c (by omega_using [hq, hc])

/-- A bound of column `c` after `b` blocks. -/
abbrev sqF (n b c : Nat) : Nat := sqB n b c * L57 + b * 2 ^ 10

/-- The squares of the `k` words at `d`. -/
def dg (m : Mem) (B : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => dg m B d k + 2 ^ (114 * k) * ((word m B (d + 8 * k)).toNat * (word m B (d + 8 * k)).toNat)

theorem dg_congr {m m' : Mem} {B : Addr} {d k : Nat} (h : ∀ i < k, word m' B (d + 8 * i) = word m B (d + 8 * i)) :
    dg m' B d k = dg m B d k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dg, dg, ih fun i hi => h i (by omega_using [hi]), h k (Nat.lt_succ_self k)]

theorem dg_three (m : Mem) (B : Addr) (d k : Nat) : dg m B d (k + 3) = dg m B d k + 2 ^ (114 * k) *
    ((word m B (d + 8 * k)).toNat * (word m B (d + 8 * k)).toNat + 2 ^ 114 * ((word m B (d + 8 * k + 8)).toNat *
      (word m B (d + 8 * k + 8)).toNat) + 2 ^ 228 * ((word m B (d + 8 * k + 16)).toNat * (word m B (d + 8 * k + 16)).toNat)) := by
  rw [dg, dg, dg, show d + 8 * (k + 1) = d + 8 * k + 8 by omega_using [], show d + 8 * (k + 2) = d + 8 * k + 16 by omega_using [],
    show 114 * (k + 1) = 114 * k + 114 by omega_using [], show 114 * (k + 2) = 114 * k + 228 by omega_using [],
    Nat.pow_add, Nat.pow_add]
  grind

theorem lv_write {m : Mem} {B : Addr} {d j r δ : Nat} {v : BitVec 64} (e : v.toNat = (word m B (d + 8 * j)).toNat + δ)
    (hd : d + 8 * (j + 1 + r) ≤ 2 ^ 64) :
    lv (m.writeW (off B (d + 8 * j)) v) B d (j + 1 + r) = lv m B d (j + 1 + r) + 2 ^ (57 * j) * δ :=
  lv_seg (k := 1) (writeW_outside m B v (by omega_using [hd])) (by rw [lv_one, lv_one, word_writeW_self, e]) hd

theorem lim_write {m : Mem} {B : Addr} {d j n : Nat} {v : BitVec 64} {f g : Nat → Nat} (h : LimF m B d n f) (hv : v.toNat ≤ g j)
    (hfg : ∀ i < n, i ≠ j → f i ≤ g i) (hj : d + 8 * j + 8 ≤ 2 ^ 64) (hd : d + 8 * n ≤ 2 ^ 64) :
    LimF (m.writeW (off B (d + 8 * j)) v) B d n g := fun i hi => by
  by_cases e : i = j
  · subst e; rw [word_writeW_self]; exact hv
  · rw [wd_ne _ B _ (by omega_using [e]) hj (by omega_using [hi, hd])]
    exact Nat.le_trans (h i hi) (hfg i hi e)

def sqrHeadRegs : List Reg := [.a2, .a0, .s2, .s3, .s4, .a1, .t2, .t3, .t4, .s0, .s1, .t0, .a3, .a4, .a5, .t5, .t6, .s7]

/-- What the head of a block of the square leaves: the three limbs `x`, the words it changes at `p`, `T`'s column `6 b`. -/
structure SqrHead (s t : State) (B : Addr) (q dM b : Nat) : Prop where
  mult : Mult t
  a0 : t.gpr .a0 = off B (oT q dM + 48 * b + 24)
  a1 : t.gpr .a1 = off B (oA q dM + 24 * b + 24)
  t5 : t.gpr .t5 = 0#64
  t6 : t.gpr .t6 = 0#64
  x0 : t.gpr .s2 = word s.mem B (oA q dM + 24 * b)
  x1 : t.gpr .s3 = word s.mem B (oA q dM + 24 * b + 8)
  x2 : t.gpr .s4 = word s.mem B (oA q dM + 24 * b + 16)
  h : (t.gpr .s7).toNat = hi57 (t.gpr .s2) (t.gpr .s4) + lo57 (t.gpr .s3) (t.gpr .s4)
  mem : ∃ v₁ v₂ v₄ : BitVec 64, t.mem = ((s.mem.writeW (off B (oT q dM + 48 * b + 8)) v₁).writeW
      (off B (oT q dM + 48 * b + 16)) v₂).writeW (off B (oT q dM + 48 * b + 32)) v₄ ∧
    v₁.toNat = (word s.mem B (oT q dM + 48 * b + 8)).toNat + lo57 (t.gpr .s2) (t.gpr .s3) ∧
    v₂.toNat = (word s.mem B (oT q dM + 48 * b + 16)).toNat + (hi57 (t.gpr .s2) (t.gpr .s3) + lo57 (t.gpr .s2) (t.gpr .s4)) ∧
    v₄.toNat = (word s.mem B (oT q dM + 48 * b + 32)).toNat + hi57 (t.gpr .s3) (t.gpr .s4)

theorem sqrHead_ok {s : State} {B : Addr} {Z q dM b g : Nat} (h : In s B Z q dM) (h4 : s.gpr .t4 = BitVec.ofNat 64 (24 * b))
    (hb : b < 3 * q) (lA : Lim s.mem B (oA q dM) (9 * q) L57) (lT : Lim s.mem B (oT q dM) (18 * q) g) (hg : g + 2 * L57 < 2 ^ 64) :
    WP isa (.block sqrHead) s fun t => SqrHead s t B q dM b ∧ Keep sqrHeadRegs s t := by
  obtain fit := h.fit
  obtain dM8 := h.dM8
  obtain q6 := h.q6
  have hn := h.scr.nowrap
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  obtain l0 := lA (3 * b) (by omega_using [hb])
  obtain l1 := lA (3 * b + 1) (by omega_using [hb])
  obtain l2 := lA (3 * b + 2) (by omega_using [hb])
  rw [show oA q dM + 8 * (3 * b) = oA q dM + 24 * b by omega_using []] at l0
  rw [show oA q dM + 8 * (3 * b + 1) = oA q dM + 24 * b + 8 by omega_using []] at l1
  rw [show oA q dM + 8 * (3 * b + 2) = oA q dM + 24 * b + 16 by omega_using []] at l2
  obtain g1 : (word s.mem B (oT q dM + 8 * (6 * b + 1))).toNat ≤ g := lT (6 * b + 1) (by omega_using [hb])
  obtain g2 : (word s.mem B (oT q dM + 8 * (6 * b + 2))).toNat ≤ g := lT (6 * b + 2) (by omega_using [hb])
  obtain g4 : (word s.mem B (oT q dM + 8 * (6 * b + 4))).toNat ≤ g := lT (6 * b + 4) (by omega_using [hb])
  rw [show oT q dM + 8 * (6 * b + 1) = oT q dM + 48 * b + 8 by omega_using []] at g1
  rw [show oT q dM + 8 * (6 * b + 2) = oT q dM + 48 * b + 16 by omega_using []] at g2
  rw [show oT q dM + 8 * (6 * b + 4) = oT q dM + 48 * b + 32 by omega_using []] at g4
  obtain c1 : oA q dM + 24 * b + 24 ≤ Z := by unfold oA; omega_using [fit, hb]
  obtain c8 : (oA q dM + 24 * b) % 8 = 0 := by unfold oA; omega_using [dM8]
  obtain e1 : oT q dM + 48 * b + 40 ≤ Z := by unfold oT; omega_using [fit, hb]
  obtain e8 : (oT q dM + 48 * b) % 8 = 0 := by unfold oT; omega_using [dM8]
  unfold sqrHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  obtain r : WP isa (.block [.add .a2 .a7 .t4, .add .a0 .s5 .t4, .add .a0 .a0 .t4, .load .d .s2 .a2 0, .load .d .s3 .a2 8,
      .load .d .s4 .a2 16, .addi .a1 .a2 24]) s fun t => (t.gpr .a0 = off B (oT q dM + 48 * b) ∧
      t.gpr .a1 = off B (oA q dM + 24 * b + 24) ∧ t.gpr .s2 = word s.mem B (oA q dM + 24 * b) ∧
        t.gpr .s3 = word s.mem B (oA q dM + 24 * b + 8) ∧ t.gpr .s4 = word s.mem B (oA q dM + 24 * b + 16) ∧ t.mem = s.mem) ∧
      Keep [.a2, .a0, .s2, .s3, .s4, .a1] s t := by
    obtain hs := h.scr
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.a7, h.s5, h4, show oT q dM + 24 * b + 24 * b = oT q dM + 48 * b by omega_using [],
      hs.ld (show oA q dM + 24 * b + 8 ≤ Z by omega_using [c1]), hs.ld (show oA q dM + 24 * b + 8 + 8 ≤ Z by omega_using [c1]),
      hs.ld (show oA q dM + 24 * b + 16 + 8 ≤ Z by omega_using [c1]), hs.al8 (show oA q dM + 24 * b + 8 ≤ Z by omega_using [c1]) c8,
      hs.al8 (show oA q dM + 24 * b + 8 + 8 ≤ Z by omega_using [c1]) (by omega_using [c8]),
      hs.al8 (show oA q dM + 24 * b + 16 + 8 ≤ Z by omega_using [c1]) (by omega_using [c8])]
  refine WP.mono r fun s₁ ⟨⟨a0, a1, x0, x1, x2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rectX_ok s₁) fun s₂ ⟨⟨p0, p1, p2, m2⟩, k2⟩ => ?_
  obtain b0 : (s₁.gpr .s2).toNat ≤ L57 := by rw [x0]; exact l0
  obtain b1 : (s₁.gpr .s3).toNat ≤ L57 := by rw [x1]; exact l1
  obtain b2 : (s₁.gpr .s4).toNat ≤ L57 := by rw [x2]; exact l2
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .s0) (rh := .s1) (x := .s2) (xp := .t2) (y := .s3) (tmp := .t0) s₂ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [p0, k2.gpr (by decide)]) (by rw [k2.gpr (by decide)]; exact b0) (by rfl))
    fun s₃ ⟨⟨lo01, hi01, m3⟩, k3⟩ => ?_
  rw [k2.gpr (r := .s2) (by decide), k2.gpr (r := .s3) (by decide)] at lo01 hi01
  obtain k23 := k2.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .a2) (rh := .a3) (x := .s2) (xp := .t2) (y := .s4) (tmp := .t0) s₃ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [k3.gpr (by decide), p0, k23.gpr (by decide)]) (by rw [k23.gpr (by decide)]; exact b0) (by rfl))
    fun s₄ ⟨⟨lo02, hi02, m4⟩, k4⟩ => ?_
  rw [k23.gpr (r := .s2) (by decide), k23.gpr (r := .s4) (by decide)] at lo02 hi02
  obtain k24 := k23.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .a4) (rh := .a5) (x := .s3) (xp := .t3) (y := .s4) (tmp := .t0) s₄ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [k4.gpr (by decide), k3.gpr (by decide), p1, k24.gpr (by decide)])
    (by rw [k24.gpr (by decide)]; exact b1) (by rfl))
    fun s₅ ⟨⟨lo12, hi12, m5⟩, k5⟩ => ?_
  rw [k24.gpr (r := .s3) (by decide), k24.gpr (r := .s4) (by decide)] at lo12 hi12
  obtain k25 := k24.trans k5
  obtain K5 := k1.trans k25
  obtain M5 : s₅.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  obtain r6 : WP isa (.block [.load .d .t0 .a0 8, .load .d .t5 .a0 16, .load .d .t6 .a0 32, .add .t0 .t0 .s0, .add .t5 .t5 .s1,
    .add .t5 .t5 .a2, .add .s7 .a3 .a4, .add .t6 .t6 .a5, .store .d .t0 .a0 8, .store .d .t5 .a0 16,
    .store .d .t6 .a0 32, .li .t5 0, .li .t6 0, .addi .a0 .a0 24]) s₅ fun t =>
      (t.gpr .a0 = off B (oT q dM + 48 * b + 24) ∧ t.gpr .t5 = 0#64 ∧ t.gpr .t6 = 0#64 ∧
        t.gpr .s7 = s₅.gpr .a3 + s₅.gpr .a4 ∧
        t.mem = ((s.mem.writeW (off B (oT q dM + 48 * b + 8)) (word s.mem B (oT q dM + 48 * b + 8) + s₅.gpr .s0)).writeW
          (off B (oT q dM + 48 * b + 16)) (word s.mem B (oT q dM + 48 * b + 16) + s₅.gpr .s1 + s₅.gpr .a2)).writeW
          (off B (oT q dM + 48 * b + 32)) (word s.mem B (oT q dM + 48 * b + 32) + s₅.gpr .a5)) ∧
      Keep [.t0, .t5, .t6, .s7, .a0] s₅ t := by
    obtain hs := h.scr.congr K5.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(k25.gpr (r := .a0) (by decide)).trans a0, M5, exec_li,
      hs.ld (show oT q dM + 48 * b + 8 + 8 ≤ Z by omega_using [e1]), hs.ld (show oT q dM + 48 * b + 16 + 8 ≤ Z by omega_using [e1]),
      hs.ld (show oT q dM + 48 * b + 32 + 8 ≤ Z by omega_using [e1]),
      hs.st (show oT q dM + 48 * b + 8 + 8 ≤ Z by omega_using [e1]), hs.st (show oT q dM + 48 * b + 16 + 8 ≤ Z by omega_using [e1]),
      hs.st (show oT q dM + 48 * b + 32 + 8 ≤ Z by omega_using [e1]),
      hs.al8 (show oT q dM + 48 * b + 8 + 8 ≤ Z by omega_using [e1]) (by omega_using [e8]),
      hs.al8 (show oT q dM + 48 * b + 16 + 8 ≤ Z by omega_using [e1]) (by omega_using [e8]),
      hs.al8 (show oT q dM + 48 * b + 32 + 8 ≤ Z by omega_using [e1]) (by omega_using [e8])]
  refine WP.mono r6 fun t ⟨⟨ta0, t5, t6, t7, tm⟩, k6⟩ => ?_
  obtain K6 := k25.trans k6
  obtain gs2 : t.gpr .s2 = s₁.gpr .s2 := K6.gpr (by decide)
  obtain gs3 : t.gpr .s3 = s₁.gpr .s3 := K6.gpr (by decide)
  obtain gs4 : t.gpr .s4 = s₁.gpr .s4 := K6.gpr (by decide)
  obtain u1 := lo57_le (s₁.gpr .s2) (s₁.gpr .s3)
  obtain u2 := lo57_le (s₁.gpr .s2) (s₁.gpr .s4)
  obtain u3 := lo57_le (s₁.gpr .s3) (s₁.gpr .s4)
  obtain w1 := hi57_le b0 b1
  obtain w2 := hi57_le b0 b2
  obtain w3 := hi57_le b1 b2
  rw [← gs2, ← gs3] at lo01 hi01 u1 w1
  rw [← gs2, ← gs4] at lo02 hi02 u2 w2
  rw [← gs3, ← gs4] at lo12 hi12 u3 w3
  obtain A2 : s₅.gpr .a2 = s₄.gpr .a2 := k5.gpr (by decide)
  obtain A3 : s₅.gpr .a3 = s₄.gpr .a3 := k5.gpr (by decide)
  obtain S0 : s₅.gpr .s0 = s₃.gpr .s0 := by rw [k5.gpr (by decide), k4.gpr (by decide)]
  obtain S1 : s₅.gpr .s1 = s₃.gpr .s1 := by rw [k5.gpr (by decide), k4.gpr (by decide)]
  rw [A2, S0, S1] at tm
  rw [A3] at t7
  obtain n1 : (word s.mem B (oT q dM + 48 * b + 16) + s₃.gpr .s1).toNat =
      (word s.mem B (oT q dM + 48 * b + 16)).toNat + hi57 (t.gpr .s2) (t.gpr .s3) := by
    rw [toNat_add_lt (by rw [hi01]; omega_using [g2, w1, hg, hL]), hi01]
  refine ⟨⟨⟨?_, ?_, ?_, by rw [gs2]; exact b0, by rw [gs3]; exact b1, by rw [gs4]; exact b2⟩, ta0,
    by rw [K6.gpr (by decide)]; exact a1, t5, t6, by rw [gs2, x0], by rw [gs3, x1], by rw [gs4, x2], ?_, _, _, _, tm, ?_, ?_, ?_⟩,
    (k1.trans K6).mono (by decide)⟩
  · rw [gs2, k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), p0]
  · rw [gs3, k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), p1]
  · rw [gs4, k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), p2]
  · rw [t7, toNat_add_lt (by rw [hi02, lo12]; omega_using [w2, u3, hL]), hi02, lo12]
  · rw [toNat_add_lt (by rw [lo01]; omega_using [g1, u1, hg, hL]), lo01]
  · rw [toNat_add_lt (by rw [n1, lo02]; omega_using [g2, w1, u2, hg, hL]), n1, lo02, Nat.add_assoc]
  · rw [toNat_add_lt (by rw [hi12]; omega_using [g4, w3, hg, hL]), hi12]

theorem lv_write' {m : Mem} {B : Addr} {d j n δ : Nat} {v : BitVec 64} (e : v.toNat = (word m B (d + 8 * j)).toNat + δ)
    (hj : j < n) (hd : d + 8 * n ≤ 2 ^ 64) :
    lv (m.writeW (off B (d + 8 * j)) v) B d n = lv m B d n + 2 ^ (57 * j) * δ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show j + 1 ≤ n from hj)
  exact lv_write e hd

theorem sqr_head_val {m m' : Mem} {B : Addr} {d j n : Nat} {v₁ v₂ v₄ : BitVec 64} {δ₁ δ₂ δ₄ : Nat}
    (hm : m' = ((m.writeW (off B (d + 8 * j + 8)) v₁).writeW (off B (d + 8 * j + 16)) v₂).writeW (off B (d + 8 * j + 32)) v₄)
    (e₁ : v₁.toNat = (word m B (d + 8 * j + 8)).toNat + δ₁) (e₂ : v₂.toNat = (word m B (d + 8 * j + 16)).toNat + δ₂)
    (e₄ : v₄.toNat = (word m B (d + 8 * j + 32)).toNat + δ₄) (hj : j + 5 ≤ n) (hd : d + 8 * n ≤ 2 ^ 64) :
    lv m' B d n = lv m B d n + 2 ^ (57 * j) * (2 ^ 57 * δ₁ + 2 ^ 114 * δ₂ + 2 ^ 228 * δ₄) := by
  rw [show d + 8 * j + 8 = d + 8 * (j + 1) by omega_using []] at hm e₁
  rw [show d + 8 * j + 16 = d + 8 * (j + 2) by omega_using []] at hm e₂
  rw [show d + 8 * j + 32 = d + 8 * (j + 4) by omega_using []] at hm e₄
  rw [hm, lv_write' (δ := δ₄) (by
      rw [wd_ne _ B _ (by omega_using []) (by omega_using [hj, hd]) (by omega_using [hj, hd]),
        wd_ne _ B _ (by omega_using []) (by omega_using [hj, hd]) (by omega_using [hj, hd]), e₄]) (by omega_using [hj]) hd,
    lv_write' (δ := δ₂) (by
      rw [wd_ne _ B _ (by omega_using []) (by omega_using [hj, hd]) (by omega_using [hj, hd]), e₂]) (by omega_using [hj]) hd,
    lv_write' e₁ (by omega_using [hj]) hd, show 57 * (j + 1) = 57 * j + 57 by omega_using [],
    show 57 * (j + 2) = 57 * j + 114 by omega_using [], show 57 * (j + 4) = 57 * j + 228 by omega_using [], Nat.pow_add,
    Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_add, Nat.mul_add]
  omega_using []

theorem sqr_step {V V₁ V₂ D S S' P x₀ x₁ x₂ a : Nat}
    (e : 2 * V + D + P * (S * S) = a * a) (eS : S = x₀ + 2 ^ 57 * x₁ + 2 ^ 114 * x₂ + 2 ^ 171 * S')
    (e₁ : V₁ = V + P * (2 ^ 57 * (x₀ * x₁ % 2 ^ 57) + 2 ^ 114 * (x₀ * x₁ / 2 ^ 57 + x₀ * x₂ % 2 ^ 57) + 2 ^ 228 * (x₁ * x₂ / 2 ^ 57)))
    (e₂ : V₂ = V₁ + P * 2 ^ 171 * (x₀ * x₂ / 2 ^ 57 + x₁ * x₂ % 2 ^ 57 + (x₀ + 2 ^ 57 * x₁ + 2 ^ 114 * x₂) * S')) :
    2 * V₂ + (D + P * (x₀ * x₀ + 2 ^ 114 * (x₁ * x₁) + 2 ^ 228 * (x₂ * x₂))) + P * 2 ^ 342 * (S' * S') = a * a := by
  obtain d₁ := Nat.div_add_mod (x₀ * x₁) (2 ^ 57)
  obtain d₂ := Nat.div_add_mod (x₀ * x₂) (2 ^ 57)
  obtain d₃ := Nat.div_add_mod (x₁ * x₂) (2 ^ 57)
  obtain e₃ : V₂ = V + P * (2 ^ 57 * (x₀ * x₁) + 2 ^ 114 * (x₀ * x₂) + 2 ^ 171 * (x₁ * x₂) +
      2 ^ 171 * ((x₀ + 2 ^ 57 * x₁ + 2 ^ 114 * x₂) * S')) := by
    rw [e₂, e₁, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add]
    refine congrArg (V + P * ·) ?_
    omega_using [d₁, d₂, d₃]
  rw [← e, e₃, eS]
  clear e₁ e₂ e₃ d₁ d₂ d₃ e eS
  grind

/-- After `b` blocks of the cross products of `A`, from `s₀`. -/
structure SqrI (s₀ s : State) (B : Addr) (Z q dM a b : Nat) : Prop where
  ctx : In s B Z q dM
  t4 : s.gpr .t4 = BitVec.ofNat 64 (24 * b)
  out : Outside B (oT q dM) (144 * q) s₀.mem s.mem
  val : 2 * lv s.mem B (oT q dM) (18 * q) + dg s₀.mem B (oA q dM) (3 * b) +
    2 ^ (342 * b) * (lv s₀.mem B (oA q dM + 24 * b) (9 * q - 3 * b) * lv s₀.mem B (oA q dM + 24 * b) (9 * q - 3 * b)) = a * a
  lim : LimF s.mem B (oT q dM) (18 * q) (sqF (9 * q) b)
  keep : Keep opRegs s₀ s

theorem sqrNext_ok {s : State} {B : Addr} {Z q dM b : Nat} (h : In s B Z q dM) (ha0 : s.gpr .a0 = off B (oT q dM + 72 * q + 24 * b)) :
    WP isa (.block sqrNext) s fun t => (t.gpr .t2 = BitVec.ofNat 64 (72 * q) ∧ t.gpr .t4 = BitVec.ofNat 64 (24 * b) ∧ t.mem = s.mem) ∧
      Keep [.t2, .t4] s t := by
  unfold sqrNext
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun u ⟨⟨x2, um⟩, ku⟩ => ?_
  obtain r : WP isa (.block [.sub .t4 .a0 .s5, .sub .t4 .t4 .t2]) u fun t => (t.gpr .t4 = BitVec.ofNat 64 (24 * b) ∧ t.mem = u.mem) ∧
      Keep [.t4] u t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [x2, (ku.gpr (r := .a0) (by decide)).trans ha0, (ku.gpr (r := .s5) (by decide)).trans h.s5,
      sub_off B (show oT q dM ≤ oT q dM + 72 * q + 24 * b by omega_using [])]
    rw [show oT q dM + 72 * q + 24 * b - oT q dM = 24 * b + 72 * q by omega_using [], BitVec.ofNat_add, BitVec.add_sub_cancel]
  exact WP.mono r fun t ⟨⟨t4, tm⟩, k⟩ => ⟨⟨(k.gpr (by decide)).trans x2, t4, tm.trans um⟩, (ku.trans k).mono (by decide)⟩

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  obtain e := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e

/-- The bounds after the head of block `b`. -/
abbrev sqG (n b c : Nat) : Nat := (sqB n b c + sqE b c) * L57 + b * 2 ^ 10

theorem sqG_e (n b c e : Nat) (h : sqE b c = e) : sqG n b c = sqF n b c + e * L57 := by
  unfold sqG sqF
  rw [h, Nat.add_mul]
  omega_using []

theorem sqG_le (n b c : Nat) : sqF n b c ≤ sqG n b c := by
  rw [sqG_e n b c _ rfl]
  exact Nat.le_add_right _ _

theorem sqG_F (n b c : Nat) : sqG n b c ≤ sqF n (b + 1) c := by
  unfold sqG sqF
  rw [sqB, ← Nat.add_assoc (sqB n b c)]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem sqG_in {n b c : Nat} (h : 6 * b + 3 ≤ c ∧ c < n + 3 * b + 3) : sqG n b c + rowMax = sqF n (b + 1) c := by
  unfold sqG sqF
  rw [sqB, ite_eq_left h, ← Nat.add_assoc (sqB n b c), Nat.add_mul (sqB n b c + sqE b c) 6, Nat.add_mul b 1]
  unfold rowMax
  omega_using []

theorem sqE_1 (b : Nat) : sqE b (6 * b + 1) = 1 := by
  unfold sqE
  rw [ite_eq_left rfl, ite_eq_right (by omega_using []), ite_eq_right (by omega_using [])]

theorem sqE_2 (b : Nat) : sqE b (6 * b + 2) = 2 := by
  unfold sqE
  rw [ite_eq_right (by omega_using []), ite_eq_left rfl, ite_eq_right (by omega_using [])]

theorem sqE_4 (b : Nat) : sqE b (6 * b + 4) = 1 := by
  unfold sqE
  rw [ite_eq_right (by omega_using []), ite_eq_right (by omega_using []), ite_eq_left rfl]

theorem sqF_le {q b c : Nat} (hq : q ≤ 6) (hb : b ≤ 3 * q) (hc : c < 18 * q) : sqF (9 * q) b c ≤ 60 * L57 + 18 * 2 ^ 10 :=
  Nat.add_le_add (Nat.mul_le_mul_right _ (sqB_le hq hb hc)) (Nat.mul_le_mul_right _ (by omega_using [hq, hb]))

theorem sqrRows_ok {s : State} {B : Addr} {Z q dM a : Nat} (h : In s B Z q dM) (hA : AIn s.mem B q dM a)
    (lT : Lim s.mem B (oT q dM) (18 * q) 0) :
    WP isa sqrRows s fun t => SqrI s t B Z q dM a (3 * q) := by
  obtain q1 := h.q1
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  unfold sqrRows
  obtain r0 : WP isa (.block [.li .t4 0]) s fun t => (t.gpr .t4 = 0#64 ∧ t.mem = s.mem) ∧ Keep [.t4] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li]
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨t4, m1⟩, k1⟩ => ?_)
  refine ptr_loop (n := 3 * q) (by omega_using [q1]) (fun b t => SqrI s t B Z q dM a b) (fun b hb t ht => ?_)
    ⟨h.of k1 (by decide) (by decide), t4, by rw [m1]; exact Outside.refl _ _ _ _, by
      rw [m1, lv_zero lT]
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.pow_zero, Nat.one_mul, dg, Nat.zero_add, hA.val],
      by
        rw [m1]
        exact fun i hi => Nat.le_trans (lT i hi) (Nat.zero_le _), k1.mono (by decide)⟩
  obtain tA : ∀ {d k : Nat}, d + 8 * k ≤ oT q dM → lv t.mem B d k = lv s.mem B d k := fun {d k} hd =>
    ht.out.lv (by omega_using [hd]) (by unfold oT at hd; omega_using [hn, fit, hd])
  obtain tw : ∀ {d : Nat}, d + 8 ≤ oT q dM → word t.mem B d = word s.mem B d := fun {d} hd =>
    ht.out.word (by omega_using [hd]) (by unfold oT at hd; omega_using [hn, fit, hd])
  obtain bT : oT q dM + 8 * (18 * q) ≤ 2 ^ 64 := by unfold oT; omega_using [hn, fit]
  refine WP.seq (WP.mono (sqrHead_ok (g := 60 * L57 + 18 * 2 ^ 10) ht.ctx ht.t4 hb
    (ht.out.lim (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit]) hA.lim)
    (fun i hi => Nat.le_trans (ht.lim i hi) (sqF_le q6 (by omega_using [hb]) hi)) (by omega_using [hL])) fun u ⟨hu, ku⟩ => ?_)
  obtain ⟨v₁, v₂, v₄, um, e₁, e₂, e₄⟩ := hu.mem
  rw [show oT q dM + 48 * b = oT q dM + 8 * (6 * b) by omega_using []] at um e₁ e₂ e₄
  obtain hV₁ := sqr_head_val um e₁ e₂ e₄ (show 6 * b + 5 ≤ 18 * q by omega_using [hb]) bT
  rw [show 57 * (6 * b) = 342 * b by omega_using []] at hV₁
  -- The head writes only `T`.
  obtain ou : Outside B (oT q dM) (144 * q) t.mem u.mem := by
    rw [um]
    exact (((writeW_outside _ B _ (by omega_using [bT, hb])).mono (by omega_using []) (by omega_using [hb])).trans
      ((writeW_outside _ B _ (by omega_using [bT, hb])).mono (by omega_using []) (by omega_using [hb]))).trans
      ((writeW_outside _ B _ (by omega_using [bT, hb])).mono (by omega_using []) (by omega_using [hb]))
  obtain l01 := lo57_le (u.gpr .s2) (u.gpr .s3)
  obtain h01 := hi57_le hu.mult.x0 hu.mult.x1
  obtain l02 := lo57_le (u.gpr .s2) (u.gpr .s4)
  obtain h12 := hi57_le hu.mult.x1 hu.mult.x2
  obtain h02 := hi57_le hu.mult.x0 hu.mult.x2
  obtain l12 := lo57_le (u.gpr .s3) (u.gpr .s4)
  obtain limG : LimF u.mem B (oT q dM) (18 * q) (sqG (9 * q) b) := by
    rw [show oT q dM + 8 * (6 * b) + 8 = oT q dM + 8 * (6 * b + 1) by omega_using []] at um e₁
    rw [show oT q dM + 8 * (6 * b) + 16 = oT q dM + 8 * (6 * b + 2) by omega_using []] at um e₂
    rw [show oT q dM + 8 * (6 * b) + 32 = oT q dM + 8 * (6 * b + 4) by omega_using []] at um e₄
    obtain f1 := ht.lim (6 * b + 1) (by omega_using [hb])
    obtain f2 := ht.lim (6 * b + 2) (by omega_using [hb])
    obtain f4 := ht.lim (6 * b + 4) (by omega_using [hb])
    rw [um]
    refine lim_write (f := sqG (9 * q) b) (lim_write (f := sqG (9 * q) b) (lim_write ht.lim ?_ (fun i _ _ => sqG_le _ _ _)
      (by omega_using [bT, hb]) bT) ?_ (fun i _ _ => Nat.le_refl _) (by omega_using [bT, hb]) bT) ?_ (fun i _ _ => Nat.le_refl _)
      (by omega_using [bT, hb]) bT
    · rw [e₁, sqG_e _ _ _ _ (sqE_1 b), Nat.one_mul]; exact Nat.add_le_add f1 l01
    · rw [e₂, sqG_e _ _ _ _ (sqE_2 b), Nat.two_mul]; exact Nat.add_le_add f2 (Nat.add_le_add h01 l02)
    · rw [e₄, sqG_e _ _ _ _ (sqE_4 b), Nat.one_mul]; exact Nat.add_le_add f4 h12
  refine WP.seq (WP.mono (rect_ok (e := .s5) (.inr rfl) (k := 3 * q - b) (f := fun i => sqG (9 * q) b (6 * b + 3 + i))
    (dT := oT q dM + 48 * b + 24) (dY := oA q dM + 24 * b + 24) (ht.ctx.scr.congr ku.2.2) hu.a0 hu.a1
    (by rw [ku.gpr (by decide), ht.ctx.s5, show oT q dM = oA q dM + 24 * b + 24 + 24 * (3 * q - b) by unfold oA oT; omega_using [hb]])
    (by omega_using [hb]) (by unfold oT; omega_using [fit, hb]) (by unfold oA; omega_using [fit, hb]) (by unfold oT; omega_using [dM8])
    (by unfold oA; omega_using [dM8]) (by unfold oA oT; omega_using [hb]) hu.mult (by rw [hu.t5]; decide) (by rw [hu.t6]; decide) ?_ ?_
    (by rw [hu.h]; omega_using [h02, l12]) (fun i hi => ?_))
    fun v hv => ?_)
  · refine fun i hi => ?_
    obtain p := pad_lim hA.lim (by rw [show oA q dM + 8 * (9 * q) = oA q dM + 72 * q by omega_using []]; exact hA.pad) (3 * b + 3 + i)
      (by omega_using [hi, hb])
    rw [ou.word (by unfold oA oT; omega_using [hi, hb]) (by unfold oA; omega_using [hn, fit, hi, hb]),
      tw (by unfold oA oT; omega_using [hi, hb]), show oA q dM + 24 * b + 24 + 8 * i = oA q dM + 8 * (3 * b + 3 + i) by omega_using []]
    exact p
  · intro i hi
    rw [show oT q dM + 48 * b + 24 + 8 * i = oT q dM + 8 * (6 * b + 3 + i) by omega_using []]
    exact limG _ (by omega_using [hi, hb])
  · obtain c : sqG (9 * q) b (6 * b + 3 + i) + rowMax ≤ 60 * L57 + 18 * 2 ^ 10 := by
      rw [sqG_in ⟨by omega_using [], by omega_using [hi, hb]⟩]
      exact sqF_le q6 (by omega_using [hb]) (by omega_using [hi, hb])
    rw [Nat.add_assoc]
    exact Nat.lt_of_le_of_lt c (by omega_using [hL])
  obtain kv := ku.trans hv.keep
  obtain cv := ht.ctx.of kv (by decide) (by decide)
  refine WP.mono (sqrNext_ok (b := b + 1) cv (by
    rw [hv.a0, show oT q dM + 48 * b + 24 + 24 * (3 * q - b) = oT q dM + 72 * q + 24 * (b + 1) by omega_using [hb]]))
    fun w ⟨⟨w2, w4, wm⟩, kw⟩ => ?_
  obtain ov : Outside B (oT q dM + 8 * (6 * b + 3)) (8 * (9 * q - 3 * b)) u.mem w.mem := by
    rw [wm]; exact hv.out.mono (by omega_using []) (by omega_using [hb])
  obtain ov' : Outside B (oT q dM) (144 * q) u.mem w.mem := ov.mono (by omega_using []) (by omega_using [hb])
  obtain kt := kv.trans kw
  -- The limbs of `A`.
  obtain uA : ∀ {d k : Nat}, d + 8 * k ≤ oT q dM → lv u.mem B d k = lv s.mem B d k := fun {d k} hd => by
    rw [ou.lv (by omega_using [hd]) (by unfold oT at hd; omega_using [hn, fit, hd]), tA hd]
  obtain x0 : u.gpr .s2 = word s.mem B (oA q dM + 24 * b) := by rw [hu.x0, tw (by unfold oA oT; omega_using [hb])]
  obtain x1 : u.gpr .s3 = word s.mem B (oA q dM + 24 * b + 8) := by rw [hu.x1, tw (by unfold oA oT; omega_using [hb])]
  obtain x2 : u.gpr .s4 = word s.mem B (oA q dM + 24 * b + 16) := by rw [hu.x2, tw (by unfold oA oT; omega_using [hb])]
  obtain zc : cVal v = 0 := hv.zero (by omega_using [hb]) (by
    rw [show oA q dM + 24 * b + 24 + 24 * (3 * q - b - 1) = oA q dM + 72 * q by omega_using [hb], uA (by unfold oA oT; omega_using [])]
    exact hA.pad)
  obtain eY : lv u.mem B (oA q dM + 24 * b + 24) (3 * (3 * q - b)) = lv s.mem B (oA q dM + 24 * (b + 1)) (9 * q - 3 * (b + 1)) := by
    rw [uA (by unfold oA oT; omega_using [hb]), show 3 * (3 * q - b) = 9 * q - 3 * (b + 1) + 3 by omega_using [hb], lv_append,
      show oA q dM + 24 * b + 24 + 8 * (9 * q - 3 * (b + 1)) = oA q dM + 72 * q by omega_using [hb], hA.pad, Nat.mul_zero,
      Nat.add_zero, show oA q dM + 24 * b + 24 = oA q dM + 24 * (b + 1) by omega_using []]
  obtain ev := hv.val
  obtain c0 : cVal u = (u.gpr .s7).toNat := by
    unfold cVal
    rw [hu.t5, hu.t6]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  rw [zc, Nat.mul_zero, Nat.add_zero, eY, c0, hu.h, show 3 * (3 * q - b) = 9 * q - 3 * b by omega_using [hb],
    show oT q dM + 48 * b + 24 = oT q dM + 8 * (6 * b + 3) by omega_using [], ← wm,
    Nat.add_assoc (lv u.mem B (oT q dM + 8 * (6 * b + 3)) _)] at ev
  obtain spl : 18 * q = 6 * b + 3 + (9 * q - 3 * b) + (9 * q - 3 * (b + 1)) := by omega_using [hb]
  obtain bd : oT q dM + 8 * (6 * b + 3 + (9 * q - 3 * b) + (9 * q - 3 * (b + 1))) ≤ 2 ^ 64 := by rw [← spl]; exact bT
  obtain hV₂ := lv_seg ov ev bd
  rw [← spl, show 57 * (6 * b + 3) = 342 * b + 171 by omega_using [], Nat.pow_add] at hV₂
  obtain eS : lv s.mem B (oA q dM + 24 * b) (9 * q - 3 * b) = (u.gpr .s2).toNat + 2 ^ 57 * (u.gpr .s3).toNat + 2 ^ 114 * (u.gpr .s4).toNat +
      2 ^ 171 * lv s.mem B (oA q dM + 24 * (b + 1)) (9 * q - 3 * (b + 1)) := by
    rw [show 9 * q - 3 * b = 3 + (9 * q - 3 * (b + 1)) by omega_using [hb], lv_split3, lv_three, x0, x1, x2,
      show oA q dM + 24 * b + 24 = oA q dM + 24 * (b + 1) by omega_using []]
  refine ⟨⟨cv.of kw (by decide) (by decide), w4, (ht.out.trans ou).trans ov', ?_, ?_, Keep.trans' ht.keep (kt.mono (by decide))⟩, ?_⟩
  · rw [show 3 * (b + 1) = 3 * b + 3 from rfl, dg_three, show oA q dM + 8 * (3 * b) = oA q dM + 24 * b by omega_using [],
      ← x0, ← x1, ← x2, show 114 * (3 * b) = 342 * b by omega_using [], show 342 * (b + 1) = 342 * b + 342 by omega_using [], Nat.pow_add]
    exact sqr_step ht.val eS hV₁ hV₂
  · rw [spl] at limG ⊢
    refine lim_seg ov limG ?_ (fun c => sqG_F _ _ _) bd
    obtain l := hv.lim
    rw [← wm, show 3 * (3 * q - b) = 9 * q - 3 * b by omega_using [hb], show oT q dM + 48 * b + 24 = oT q dM + 8 * (6 * b + 3) by omega_using []] at l
    intro i hi
    exact Nat.le_trans (l i hi) (Nat.le_of_eq (sqG_in (n := 9 * q) (b := b) (c := 6 * b + 3 + i)
      ⟨by omega_using [], by omega_using [hi, hb]⟩))
  · rw [w4, w2, ofNat_inj (by omega_using [hb, q6]) (by omega_using [q6])]
    omega_using []

/-! ## The square: doubling and the squares of the limbs -/

/-- After `i` limbs of `diag57` from `s₀`. -/
structure Diag (s₀ s : State) (B : Addr) (dA dT i : Nat) : Prop where
  a0 : s.gpr .a0 = off B (dT + 16 * i)
  a1 : s.gpr .a1 = off B (dA + 8 * i)
  out : Outside B dT (16 * i) s₀.mem s.mem
  val : lv s.mem B dT (2 * i) + 2 ^ (114 * i) * (s.gpr .t5).toNat = 2 * lv s₀.mem B dT (2 * i) + dg s₀.mem B dA i
  lim : Lim s.mem B dT (2 * i) L57
  cy : (s.gpr .t5).toNat ≤ 2 ^ 10
  t6 : s.gpr .t6 = m57

def diagRegs : List Reg := [.s2, .t2, .s0, .s1, .a2, .a3, .a4, .t5, .a5, .a0, .a1]

theorem diag_arith {T₀ T₁ l h c g : Nat} (h₀ : T₀ ≤ g) (h₁ : T₁ ≤ g) (hl : l ≤ L57) (hh : h ≤ L57) (hc : c ≤ 2 ^ 10)
    (hg : 2 * g + L57 + 2 ^ 11 < 2 ^ 64) :
    2 * T₀ + c + l < 2 ^ 64 ∧ 2 * T₁ + h + (2 * T₀ + c + l) / 2 ^ 57 < 2 ^ 64 ∧
      (2 * T₁ + h + (2 * T₀ + c + l) / 2 ^ 57) / 2 ^ 57 ≤ 2 ^ 10 ∧
      (2 * T₀ + c + l) % 2 ^ 57 + 2 ^ 57 * ((2 * T₁ + h + (2 * T₀ + c + l) / 2 ^ 57) % 2 ^ 57) +
        2 ^ 114 * ((2 * T₁ + h + (2 * T₀ + c + l) / 2 ^ 57) / 2 ^ 57) = 2 * (T₀ + 2 ^ 57 * T₁) + (l + 2 ^ 57 * h) + c := by
  unfold L57 at *
  omega_using [h₀, h₁, hl, hh, hc, hg]

theorem diagStep_ok {s₀ s : State} {B : Addr} {Z dA dT i n g : Nat} (hs : Scr s B Z) (h : Diag s₀ s B dA dT i) (hi : i < n)
    (hA : dA + 8 * n ≤ dT) (hT : dT + 16 * n ≤ Z) (hA8 : dA % 8 = 0) (hT8 : dT % 8 = 0)
    (lA : Lim s₀.mem B dA n L57) (lT : Lim s₀.mem B dT (2 * n) g) (hg : 2 * g + L57 + 2 ^ 11 < 2 ^ 64) :
    WP isa (.block (diagStep57 ++ ([.addi .a0 .a0 16, .addi .a1 .a1 8] : List Instr))) s fun t =>
      Diag s₀ t B dA dT (i + 1) ∧ Keep diagRegs s t := by
  have hn := hs.nowrap
  obtain x : (word s₀.mem B (dA + 8 * i)).toNat ≤ L57 := lA i hi
  obtain T₀ : (word s₀.mem B (dT + 8 * (2 * i))).toNat ≤ g := lT (2 * i) (by omega_using [hi])
  obtain T₁ : (word s₀.mem B (dT + 8 * (2 * i + 1))).toNat ≤ g := lT (2 * i + 1) (by omega_using [hi])
  rw [show dT + 8 * (2 * i) = dT + 16 * i by omega_using []] at T₀
  rw [show dT + 8 * (2 * i + 1) = dT + 16 * i + 8 by omega_using []] at T₁
  obtain rx : word s.mem B (dA + 8 * i) = word s₀.mem B (dA + 8 * i) := h.out.word (by omega_using [hA, hi]) (by omega_using [hn, hA, hT, hi])
  obtain r₀ : word s.mem B (dT + 16 * i) = word s₀.mem B (dT + 16 * i) := h.out.word (by omega_using []) (by omega_using [hn, hT, hi])
  obtain r₁ : word s.mem B (dT + 16 * i + 8) = word s₀.mem B (dT + 16 * i + 8) := h.out.word (by omega_using []) (by omega_using [hn, hT, hi])
  obtain val := h.val
  generalize eX : word s₀.mem B (dA + 8 * i) = X at x rx
  generalize e₀ : word s₀.mem B (dT + 16 * i) = X₀ at T₀ r₀
  generalize e₁ : word s₀.mem B (dT + 16 * i + 8) = X₁ at T₁ r₁
  unfold diagStep57
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  obtain q1 : WP isa (.block [.load .d .s2 .a1 0]) s fun t => (t.gpr .s2 = X ∧ t.mem = s.mem) ∧ Keep [.s2] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.a1, hs.ld (show dA + 8 * i + 8 ≤ Z by omega_using [hA, hT, hi]),
      hs.al8 (show dA + 8 * i + 8 ≤ Z by omega_using [hA, hT, hi]) (by omega_using [hA8])]
    exact rx
  refine WP.mono q1 fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  obtain q2 : WP isa (.block [.shift .sll .d .t2 .s2 7]) s₁ fun t => (t.gpr .t2 = X <<< 7 ∧ t.mem = s₁.mem) ∧ Keep [.t2] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [x2]
  refine WP.mono q2 fun s₂ ⟨⟨x2', m2⟩, k2⟩ => ?_
  obtain y2 : s₂.gpr .s2 = X := (k2.gpr (by decide)).trans x2
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .s0) (rh := .s1) (x := .s2) (xp := .t2) (y := .s2) (tmp := .a2) s₂ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [x2', y2]) (by rw [y2]; exact x) (by rfl)) fun s₃ ⟨⟨lo, hi', m3⟩, k3⟩ => ?_
  rw [y2] at lo hi'
  obtain K3 := (k1.trans k2).trans k3
  obtain M3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  obtain bl := lo57_le X X
  obtain bh := hi57_le x x
  obtain ⟨o1, o2, o3, o4⟩ := diag_arith T₀ T₁ bl bh h.cy hg
  generalize hv1 : 2 * X₀.toNat + (s.gpr .t5).toNat + lo57 X X = v1 at o1 o2 o3 o4
  generalize hv2 : 2 * X₁.toNat + hi57 X X + v1 / 2 ^ 57 = v2 at o2 o3 o4
  obtain dd : ∀ y : BitVec 64, 2 * y.toNat < 2 ^ 64 → (y <<< 1).toNat = 2 * y.toNat := fun y hy => by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using [hy])]; omega_using []
  obtain r : WP isa (.block [.load .d .a3 .a0 0, .load .d .a4 .a0 8, .shift .sll .d .a3 .a3 1, .shift .sll .d .a4 .a4 1,
      .add .a3 .a3 .t5, .add .a3 .a3 .s0, .logic .and .a5 .a3 .t6, .shift .srl .d .t5 .a3 57,
      .store .d .a5 .a0 0, .add .a4 .a4 .s1, .add .a4 .a4 .t5, .logic .and .a5 .a4 .t6,
      .shift .srl .d .t5 .a4 57, .store .d .a5 .a0 8, .addi .a0 .a0 16, .addi .a1 .a1 8]) s₃ fun t =>
      (t.mem = (s.mem.writeW (off B (dT + 16 * i)) ((X₀ <<< 1 + s.gpr .t5 + s₃.gpr .s0) &&& m57)).writeW (off B (dT + 16 * i + 8))
          ((X₁ <<< 1 + s₃.gpr .s1 + (X₀ <<< 1 + s.gpr .t5 + s₃.gpr .s0) >>> 57) &&& m57) ∧
        t.gpr .t5 = (X₁ <<< 1 + s₃.gpr .s1 + (X₀ <<< 1 + s.gpr .t5 + s₃.gpr .s0) >>> 57) >>> 57 ∧
        t.gpr .a0 = off B (dT + 16 * i + 16) ∧ t.gpr .a1 = off B (dA + 8 * i + 8)) ∧
      Keep [.a3, .a4, .a5, .t5, .a0, .a1] s₃ t := by
    obtain hs := hs.congr K3.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(K3.gpr (r := .a0) (by decide)).trans h.a0, (K3.gpr (r := .a1) (by decide)).trans h.a1, K3.gpr (r := .t5) (by decide),
      (K3.gpr (r := .t6) (by decide)).trans h.t6, M3, show s.mem.readW (off B (dT + 16 * i)) 64 = X₀ from r₀,
      show s.mem.readW (off B (dT + 16 * i + 8)) 64 = X₁ from r₁,
      hs.ld (show dT + 16 * i + 8 ≤ Z by omega_using [hT, hi]), hs.ld (show dT + 16 * i + 8 + 8 ≤ Z by omega_using [hT, hi]),
      hs.st (show dT + 16 * i + 8 ≤ Z by omega_using [hT, hi]), hs.st (show dT + 16 * i + 8 + 8 ≤ Z by omega_using [hT, hi]),
      hs.al8 (show dT + 16 * i + 8 ≤ Z by omega_using [hT, hi]) (by omega_using [hT8]),
      hs.al8 (show dT + 16 * i + 8 + 8 ≤ Z by omega_using [hT, hi]) (by omega_using [hT8])]
  refine WP.mono r fun t ⟨⟨tm, t5, ta0, ta1⟩, k4⟩ => ?_
  obtain n1 : (X₀ <<< 1 + s.gpr .t5 + s₃.gpr .s0).toNat = v1 := by
    obtain d := dd X₀ (by omega_using [o1, hv1])
    obtain d' : (X₀ <<< 1 + s.gpr .t5).toNat = 2 * X₀.toNat + (s.gpr .t5).toNat := by
      rw [toNat_add_lt (by rw [d]; omega_using [o1, hv1]), d]
    rw [toNat_add_lt (by rw [d', lo, hv1]; exact o1), d', lo, hv1]
  obtain n2 : (X₁ <<< 1 + s₃.gpr .s1 + (X₀ <<< 1 + s.gpr .t5 + s₃.gpr .s0) >>> 57).toNat = v2 := by
    obtain d := dd X₁ (by omega_using [o2, hv2])
    obtain d' : (X₁ <<< 1 + s₃.gpr .s1).toNat = 2 * X₁.toNat + hi57 X X := by
      rw [toNat_add_lt (by rw [d, hi']; omega_using [o2, hv2]), d, hi']
    rw [toNat_add_lt (by rw [d', srl57, n1, hv2]; exact o2), d', srl57, n1, hv2]
  generalize (X₀ <<< 1 + s.gpr .t5 + s₃.gpr .s0) = V1 at tm t5 n1 n2
  generalize (X₁ <<< 1 + s₃.gpr .s1 + V1 >>> 57) = V2 at tm t5 n2
  obtain w0 : word t.mem B (dT + 16 * i) = V1 &&& m57 := by
    rw [tm, wd_ne _ B _ (by omega_using []) (by omega_using [hn, hT, hi]) (by omega_using [hn, hT, hi]), word_writeW_self]
  obtain w1 : word t.mem B (dT + 16 * i + 8) = V2 &&& m57 := by rw [tm, word_writeW_self]
  obtain ot : Outside B (dT + 16 * i) 16 s.mem t.mem := by
    rw [tm]
    exact ((writeW_outside _ B _ (by omega_using [hn, hT, hi])).mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside _ B _ (by omega_using [hn, hT, hi])).mono (by omega_using []) (by omega_using []))
  obtain lv2 : ∀ m : Mem, lv m B dT (2 * (i + 1)) = lv m B dT (2 * i) + 2 ^ (114 * i) * ((word m B (dT + 16 * i)).toNat +
      2 ^ 57 * (word m B (dT + 16 * i + 8)).toNat) := fun m => by
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 from rfl, lv, lv, show dT + 8 * (2 * i) = dT + 16 * i by omega_using [],
      show dT + 8 * (2 * i + 1) = dT + 16 * i + 8 by omega_using [], show 57 * (2 * i) = 114 * i by omega_using [],
      show 57 * (2 * i + 1) = 114 * i + 57 by omega_using [], Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]
  refine ⟨⟨by rw [ta0, Nat.mul_succ, Nat.add_assoc], by rw [ta1, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_, ?_, ?_⟩,
    (K3.trans k4).mono (by decide)⟩
  · exact (h.out.mono (Nat.le_refl _) (by omega_using [])).trans (ot.mono (by omega_using []) (by omega_using []))
  · rw [lv2, lv2, w0, w1, and_m57, and_m57, n1, n2, t5, srl57, n2, ot.lv (d := dT) (by omega_using []) (by omega_using [hn, hT, hi]),
      dg, eX, e₀, e₁, show 114 * (i + 1) = 114 * i + 114 by omega_using [], Nat.pow_add, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, o4]
    obtain d := Nat.div_add_mod (X.toNat * X.toNat) (2 ^ 57)
    obtain d' : X.toNat * X.toNat = lo57 X X + 2 ^ 57 * hi57 X X := by unfold lo57 hi57; omega_using [d]
    rw [d']
    clear d d' o1 o2 o3 o4 hv1 hv2 n1 n2
    generalize lo57 X X + 2 ^ 57 * hi57 X X = y at *
    grind
  · refine LimF.append (j := 2 * i) (k := 2) (ot.lim (by omega_using []) (by omega_using [hn, hT, hi]) h.lim) ?_
    rw [show dT + 8 * (2 * i) = dT + 16 * i by omega_using []]
    intro c hc
    rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl
    · rw [Nat.mul_zero, Nat.add_zero, w0, and_m57]
      exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))
    · rw [Nat.mul_one, w1, and_m57]
      exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))
  · rw [t5, srl57, n2]; exact o3
  · rw [k4.gpr (by decide), K3.gpr (by decide)]; exact h.t6

theorem diag57_ok {s : State} {B : Addr} {Z q dM g : Nat} (h : In s B Z q dM) (lA : Lim s.mem B (oA q dM) (9 * q) L57)
    (lT : Lim s.mem B (oT q dM) (18 * q) g) (hg : 2 * g + L57 + 2 ^ 11 < 2 ^ 64) :
    WP isa diag57 s fun t => (Outside B (oT q dM) (144 * q) s.mem t.mem ∧ Lim t.mem B (oT q dM) (18 * q) L57 ∧
      ∃ c, lv t.mem B (oT q dM) (18 * q) + 2 ^ (1026 * q) * c = 2 * lv s.mem B (oT q dM) (18 * q) + dg s.mem B (oA q dM) (9 * q)) ∧
      Keep opRegs s t := by
  obtain q1 := h.q1
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  unfold diag57
  obtain r0 : WP isa (.block (mask57 ++ ([.li .t5 0, .addi .a0 .s5 0] : List Instr) ++ limbs ++ ([.addi .a1 .a7 0, .add .t3 .a7 .t2] : List Instr))) s
      fun t => (t.gpr .t6 = m57 ∧ t.gpr .t5 = 0#64 ∧ t.gpr .a0 = off B (oT q dM) ∧ t.gpr .a1 = off B (oA q dM) ∧
        t.gpr .t3 = off B (oA q dM + 72 * q) ∧ t.mem = s.mem) ∧ Keep [.t6, .t5, .a0, .t2, .a1, .t3] s t := by
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (mask57_ok s) fun u ⟨⟨u6, um⟩, ku⟩ => ?_
    rw [WP.block_append_iff]
    obtain r : WP isa (.block [.li .t5 0, .addi .a0 .s5 0]) u fun t => (t.gpr .t5 = 0#64 ∧ t.gpr .a0 = off B (oT q dM) ∧ t.mem = u.mem) ∧
        Keep [.t5, .a0] u t :=
      WP.keep _ (by brun [exec_li, (ku.gpr (r := .s5) (by decide)).trans h.s5, BitVec.add_zero]) (by rfl) (by rfl)
    refine WP.mono r fun v ⟨⟨v5, v0, vm⟩, kv⟩ => ?_
    obtain kuv := ku.trans kv
    rw [WP.block_append_iff]
    obtain hv : In v B Z q dM := h.of kuv (by decide) (by decide)
    refine WP.mono (limbs_ok hv) fun w ⟨⟨w2, wm⟩, kw⟩ => ?_
    obtain r : WP isa (.block [.addi .a1 .a7 0, .add .t3 .a7 .t2]) w fun t => (t.gpr .a1 = off B (oA q dM) ∧
        t.gpr .t3 = off B (oA q dM + 72 * q) ∧ t.mem = w.mem) ∧ Keep [.a1, .t3] w t :=
      WP.keep _ (by brun [w2, (kw.gpr (r := .a7) (by decide)).trans hv.a7, BitVec.add_zero]) (by rfl) (by rfl)
    exact WP.mono r fun t ⟨⟨t1, t3, tm⟩, kt⟩ => ⟨⟨by rw [kt.gpr (by decide), kw.gpr (by decide), kv.gpr (by decide), u6],
      by rw [kt.gpr (by decide), kw.gpr (by decide), v5], by rw [kt.gpr (by decide), kw.gpr (by decide), v0], t1, t3,
      by rw [tm, wm, vm, um]⟩, ((kuv.trans kw).trans kt).mono (by decide)⟩
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨t6, t5, a0, a1, t3, m1⟩, k1⟩ => ?_)
  refine WP.mono (ptr_loop (a := .a1) (e := .t3) (n := 9 * q) (by omega_using [q1]) (fun i t => Diag s t B (oA q dM) (oT q dM) i ∧
      t.gpr .t3 = off B (oA q dM + 72 * q) ∧ Keep ([.t6, .t5, .a0, .t2, .a1, .t3] ++ diagRegs) s t)
    (fun i hi t ⟨ht, h3, kt⟩ => ?_)
    ⟨⟨a0, a1, by rw [m1]; exact Outside.refl _ _ _ _, by rw [t5, m1]; rfl, fun i hi => absurd hi (by omega_using []), by rw [t5]; decide, t6⟩,
      t3, k1.mono (by decide)⟩)
    fun t ⟨ht, _, kt⟩ => ⟨⟨ht.out.mono (Nat.le_refl _) (by omega_using []), ?_, (t.gpr .t5).toNat, ?_⟩, kt.mono (by decide)⟩
  · refine WP.mono (diagStep_ok (n := 9 * q) (g := g) (h.scr.congr kt.2.2) ht hi (by unfold oA oT; omega_using [])
      (by unfold oT; omega_using [fit]) (by unfold oA; omega_using [dM8]) (by unfold oT; omega_using [dM8]) lA
      (by rw [show 2 * (9 * q) = 18 * q by omega_using []]; exact lT) hg) fun u ⟨hu, ku⟩ => ⟨⟨hu, (ku.gpr (by decide)).trans h3,
        Keep.trans' kt (ku.mono (by decide))⟩, ?_⟩
    rw [hu.a1, ku.gpr (by decide), h3, off_inj (by unfold oA; omega_using [hn, fit, hi]) (by unfold oA; omega_using [hn, fit])]
    omega_using []
  · obtain l := ht.lim
    rw [show 2 * (9 * q) = 18 * q by omega_using []] at l
    exact l
  · obtain v := ht.val
    rw [show 2 * (9 * q) = 18 * q by omega_using [], show 114 * (9 * q) = 1026 * q by omega_using []] at v
    exact v

/-! ## The operations -/

theorem srl_ofNat {n k : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, Nat.add_comm, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The working space before and after an operation, with array 0 at `d0`, for arrays of `8 q + 2` words. -/
structure Sp (s : State) (B : Addr) (Z q d0 : Nat) : Prop where
  scr : Scr s B Z
  q2 : 2 ≤ q
  q6 : q ≤ 6
  d8 : d0 % 8 = 0
  fit : d0 + 488 * q + 80 < Z
  a7 : s.gpr .a7 = off B d0
  s5 : s.gpr .s5 = BitVec.ofNat 64 (64 * q + 16)

theorem Sp.of {s t : State} {B : Addr} {Z q d0 : Nat} {rs : List Reg} (h : Sp s B Z q d0) (k : Keep rs s t)
    (h7 : Reg.a7 ∉ rs) (h5 : Reg.s5 ∉ rs) : Sp t B Z q d0 :=
  ⟨h.scr.congr k.2.2, h.q2, h.q6, h.d8, h.fit, (k.gpr h7).trans h.a7, (k.gpr h5).trans h.s5⟩

/-- `M`'s offset: array 2's. -/
abbrev oM (q d0 : Nat) : Nat := d0 + 128 * q + 32

theorem n8_calc {q : Nat} (h : q ≤ 6) :
    BitVec.ofNat 64 (64 * q + 16) >>> 3 + BitVec.ofNat 64 (64 * q + 16) - BitVec.ofNat 64 18 = BitVec.ofNat 64 (72 * q) := by
  rw [srl_ofNat (by omega_using [h]), ← BitVec.ofNat_add, sub_ofNat (by omega_using [])]
  refine congrArg _ ?_
  omega_using []

theorem enter_ok {s : State} {B : Addr} {Z q d0 : Nat} (h : Sp s B Z q d0) :
    WP isa (.block enter) s fun t => (In t B Z q (oM q d0) ∧ t.mem = s.mem) ∧ Keep [.t2, .t3, .a7, .s5] s t := by
  obtain q6 := h.q6
  obtain r : WP isa (.block enter) s fun t => (t.gpr .a7 = off B (oA q (oM q d0)) ∧ t.gpr .s5 = off B (oT q (oM q d0)) ∧ t.mem = s.mem) ∧
      Keep [.t2, .t3, .a7, .s5] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold enter
    brun [h.a7, h.s5, n8_calc q6, off_add]
    exact ⟨congrArg (off B) (by unfold oA oM; omega_using []), congrArg (off B) (by unfold oT oM; omega_using [])⟩
  refine WP.mono r fun t ⟨⟨a7, s5, m⟩, k⟩ => ⟨⟨⟨h.scr.congr k.2.2, by have := h.q2; omega_using [this], q6, ?_, ?_, a7, s5⟩, m⟩, k⟩
  · have := h.d8; unfold oM; omega_using [this]
  · have := h.fit; unfold oM; omega_using [this]

theorem leave_ok {s : State} {B : Addr} {Z q d0 : Nat} (h : In s B Z q (oM q d0)) :
    WP isa (.block leave) s fun t => (t.gpr .a7 = off B d0 ∧ t.gpr .s5 = BitVec.ofNat 64 (64 * q + 16) ∧
      t.gpr .t0 = BitVec.ofNat 64 (8 * q) ∧ t.mem = s.mem) ∧ Keep [.t2, .t3, .t4, .s5, .a7, .t0] s t := by
  obtain q6 := h.q6
  unfold leave
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun u ⟨⟨x2, um⟩, ku⟩ => ?_
  obtain e : BitVec.ofNat 64 (72 * q) * BitVec.ofNat 64 57 = BitVec.ofNat 64 (4104 * q) := by
    rw [← BitVec.ofNat_mul]; exact congrArg _ (by omega_using [])
  obtain e' : BitVec.ofNat 64 (4104 * q) >>> 6 = BitVec.ofNat 64 (64 * q) := by
    rw [srl_ofNat (by omega_using [q6])]; exact congrArg _ (by omega_using [q6])
  obtain e'' : BitVec.ofNat 64 (64 * q + 16) >>> 3 - BitVec.ofNat 64 2 = BitVec.ofNat 64 (8 * q) := by
    rw [srl_ofNat (by omega_using [q6]), sub_ofNat (by omega_using [])]; exact congrArg _ (by omega_using [])
  obtain r : WP isa (.block [.sub .t3 .a7 .t2, .addi .t3 .t3 (-24), .li .t4 57, .mul .t2 .t2 .t4, .shift .srl .d .t2 .t2 6,
    .addi .s5 .t2 16, .sub .a7 .t3 .s5, .sub .a7 .a7 .s5, .shift .srl .d .t0 .s5 3, .addi .t0 .t0 (-2)]) u fun t =>
      (t.gpr .a7 = off B d0 ∧ t.gpr .s5 = BitVec.ofNat 64 (64 * q + 16) ∧
      t.gpr .t0 = BitVec.ofNat 64 (8 * q) ∧ t.mem = u.mem) ∧ Keep [.t2, .t3, .t4, .s5, .a7, .t0] u t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [x2, (ku.gpr (r := .a7) (by decide)).trans h.a7, exec_li, e, e', ← BitVec.ofNat_add, e'',
      off_sub B (show 72 * q ≤ oA q (oM q d0) by unfold oA; omega_using []),
      off_sub B (show 24 ≤ oA q (oM q d0) - 72 * q by unfold oA; omega_using []),
      off_sub B (show 64 * q + 16 ≤ oA q (oM q d0) - 72 * q - 24 by unfold oA oM; omega_using []),
      off_sub B (show 64 * q + 16 ≤ oA q (oM q d0) - 72 * q - 24 - (64 * q + 16) by unfold oA oM; omega_using [])]
    exact congrArg (off B) (by unfold oA oM; omega_using [])
  exact WP.mono r fun t ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c, d.trans um⟩, (ku.trans k).mono (by decide)⟩

/-- The bound of the reduction's input. -/
theorem red_bound {a b N R : Nat} (ha : a < 2 * N) (hb : b < 2 * N) (hR : 4 * N ≤ R) : a * b + R * N ≤ R * R := by
  obtain l := Nat.mul_le_mul (Nat.le_of_lt ha) (Nat.le_of_lt hb)
  obtain l1 := Nat.mul_le_mul_left N hR
  obtain l2 := Nat.mul_le_mul_left R hR
  rw [Nat.mul_comm N R] at l1
  rw [show 2 * N * (2 * N) = N * (4 * N) by grind] at l
  rw [show R * (4 * N) = 4 * (R * N) by grind] at l2
  omega_using [l, l1, l2]

theorem red_out {a b N R o W : Nat} (ha : a < 2 * N) (hb : b < 2 * N) (hR : 4 * N ≤ R) (hW : W < R) (e : R * o = a * b + W * N) :
    o < 2 * N := by
  obtain hN : 0 < N := by omega_using [ha]
  obtain l := Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega_using [hN])
  obtain l1 := Nat.mul_le_mul_left N hR
  obtain l2 := (Nat.mul_lt_mul_right hN).mpr hW
  rw [Nat.mul_comm N R] at l1
  rw [show 2 * N * (2 * N) = N * (4 * N) by grind] at l
  exact Nat.lt_of_mul_lt_mul_left (a := R) (by rw [e, show R * (2 * N) = 2 * (R * N) by grind]; omega_using [l, l1, l2])

theorem red_one {a b N R o W : Nat} (ha : a < 2 * N) (hR : 4 * N ≤ R) (hW : W < R) (e : R * o = a * b + W * N) (hb : b ≤ 1) :
    o ≤ N := by
  obtain l := Nat.mul_le_mul_left a hb
  rw [Nat.mul_one] at l
  obtain l2 := Nat.mul_le_mul_right N (show W + 1 ≤ R from hW)
  rw [Nat.succ_mul] at l2
  refine Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left (a := R) ?_)
  rw [e, Nat.mul_succ]
  omega_using [l, l2, ha, hR]

/-- The modulus of an operation. -/
structure Mod57 (s : State) (B : Addr) (q d0 N : Nat) : Prop where
  mod : ModIn s B q (oM q d0) N
  pos : 0 < N
  lt : N < 2 ^ (512 * q)

theorem Mod57.four {s : State} {B : Addr} {q d0 N : Nat} (h : Mod57 s B q d0 N) (q2 : 2 ≤ q) : 4 * N ≤ 2 ^ (513 * q) := by
  obtain l := h.lt
  obtain p : 2 ^ (512 * q) * 2 ^ 2 ≤ 2 ^ (513 * q) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_using [q2])
  omega_using [l, p]

/-- The end of an operation: the reduction, and the registers back. -/
theorem finish57_ok {s₀ s : State} {B : Addr} {Z q d0 N a b : Nat} (h₀ : Sp s₀ B Z q d0) (hm : Mod57 s₀ B q d0 N)
    (h : In s B Z q (oM q d0)) (k : Keep (opRegs ++ ([.a7, .s5] : List Reg)) s₀ s) (out : Outside B (oT q (oM q d0)) (144 * q) s₀.mem s.mem)
    (hA : AIn s₀.mem B q (oM q d0) a) (ha : a < 2 * N) (hb : b < 2 * N)
    (lT : Lim s.mem B (oT q (oM q d0)) (18 * q) L57) (eV : lv s.mem B (oT q (oM q d0)) (18 * q) = a * b) :
    WP isa (.seq reduce57 (.block leave)) s fun t => (Sp t B Z q d0 ∧ t.gpr .t0 = BitVec.ofNat 64 (8 * q) ∧ Mod57 t B q d0 N ∧
      OutAT B q (oM q d0) s₀.mem t.mem ∧ ∃ o, AIn t.mem B q (oM q d0) o ∧ o < 2 * N ∧ o * 2 ^ (513 * q) % N = a * b % N ∧ (b ≤ 1 → o ≤ N)) ∧
        Keep opRegs s₀ t := by
  obtain q2 := h₀.q2
  obtain R4 := hm.four q2
  have hn := h.scr.nowrap
  obtain fit := h.fit
  obtain m : ModIn s B q (oM q d0) N := hm.mod.of k (by decide) out (by unfold oT; omega_using []) h₀.scr (by omega_using [fit]) h.q1
  refine WP.seq (WP.mono (reduce57_ok h m lT eV (red_bound ha hb R4) hm.pos (by
    rw [out.lv (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit])]; exact hA.pad))
    fun u ⟨⟨hu, mu, ou, o, W, hA', hW, e⟩, ku⟩ => ?_)
  refine WP.mono (leave_ok hu) fun t ⟨⟨a7, s5, t0, tm⟩, kt⟩ => ?_
  obtain K := (k.trans ku).trans kt
  obtain K' : Keep opRegs s₀ t := by
    refine ⟨fun r hr => ?_, K.2.1, K.2.2⟩
    by_cases h7 : r = .a7
    · subst h7; rw [a7, h₀.a7]
    by_cases h5 : r = .s5
    · subst h5; rw [s5, h₀.s5]
    refine K.gpr fun hm => ?_
    simp only [List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · exact hr hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hm.elim h7 h5
    · exact hr hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact h7 rfl | exact h5 rfl | exact hr (by decide)
  refine ⟨⟨h₀.of K' (by decide) (by decide), t0, ⟨?_, hm.pos, hm.lt⟩, ?_, o, by rw [tm]; exact hA', red_out ha hb R4 hW e, ?_, red_one ha R4 hW e⟩, K'⟩
  · exact ⟨by rw [tm]; exact mu.val, by rw [tm]; exact mu.lim, by rw [tm]; exact mu.pad, by
      rw [tm, kt.gpr (by decide)]; exact mu.inv⟩
  · rw [tm]; exact (outT out).trans ou
  · rw [Nat.mul_comm, e, Nat.add_mul_mod_self_right]

theorem lt_mul_pow {a b q : Nat} (ha : a < 2 ^ (513 * q)) (hb : b < 2 ^ (513 * q)) : a * b < 2 ^ (1026 * q) := by
  rw [show 1026 * q = 513 * q + 513 * q by omega_using [], Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (Nat.two_pow_pos _)

theorem no_carry {x c P V : Nat} (e : x + P * c = V) (h : V < P) : x = V := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.mul_zero, Nat.add_zero] at e; exact e
  · obtain l := Nat.le_mul_of_pos_right P hc
    omega_using [l, e, h]

theorem AIn.lt {m : Mem} {B : Addr} {q dM a : Nat} (h : AIn m B q dM a) : a < 2 ^ (513 * q) := by
  obtain l := lv_lt h.lim
  rw [h.val, show 57 * (9 * q) = 513 * q by omega_using []] at l
  exact l

theorem AIn.out {m m' : Mem} {B : Addr} {q dM a o n Z : Nat} (h : AIn m B q dM a) (ho : Outside B o n m m')
    (hd : oT q dM ≤ o ∨ o + n ≤ oA q dM) (hn : B.toNat + Z ≤ 2 ^ 64) (hZ : oT q dM ≤ Z) (hq : 1 ≤ q) : AIn m' B q dM a := by
  unfold oT at hd hZ
  refine ⟨?_, ?_, ?_⟩
  · rw [ho.lv (by unfold oA at *; omega_using [hd]) (by unfold oA; omega_using [hn, hZ])]; exact h.val
  · exact ho.lim (by unfold oA at *; omega_using [hd]) (by unfold oA; omega_using [hn, hZ]) h.lim
  · rw [ho.lv (by unfold oA at *; omega_using [hd, hq]) (by unfold oA; omega_using [hn, hZ])]; exact h.pad

/-- `sqrOp57`. -/
theorem sqrOp57_ok {s : State} {B : Addr} {Z q d0 N a : Nat} (h : Sp s B Z q d0) (hm : Mod57 s B q d0 N)
    (hA : AIn s.mem B q (oM q d0) a) (ha : a < 2 * N) :
    WP isa sqrOp57 s fun t => (Sp t B Z q d0 ∧ t.gpr .t0 = BitVec.ofNat 64 (8 * q) ∧ Mod57 t B q d0 N ∧
      OutAT B q (oM q d0) s.mem t.mem ∧ ∃ o, AIn t.mem B q (oM q d0) o ∧ o < 2 * N ∧ o * 2 ^ (513 * q) % N = a * a % N ∧ (a ≤ 1 → o ≤ N)) ∧
        Keep opRegs s t := by
  have hn := h.scr.nowrap
  unfold sqrOp57
  refine WP.seq (WP.mono (enter_ok h) fun s₁ ⟨⟨i1, m1⟩, k1⟩ => ?_)
  obtain fit := i1.fit
  obtain q6 := i1.q6
  obtain hZ : oT q (oM q d0) + 144 * q ≤ Z := by unfold oT; omega_using [fit]
  refine WP.seq (WP.mono (zeroT57_ok i1) fun s₂ ⟨⟨o2, z2⟩, k2⟩ => ?_)
  rw [m1] at o2
  obtain i2 := i1.of k2 (by decide) (by decide)
  obtain A2 := hA.out o2 (.inl (Nat.le_refl _)) hn (by omega_using [hZ]) i1.q1
  refine WP.seq (WP.mono (sqrRows_ok i2 A2 z2) fun s₃ h3 => ?_)
  obtain A3 := A2.out h3.out (.inl (Nat.le_refl _)) hn (by omega_using [hZ]) i1.q1
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  refine WP.seq (WP.mono (diag57_ok (g := 60 * L57 + 18 * 2 ^ 10) h3.ctx A3.lim
    (fun i hi => Nat.le_trans (h3.lim i hi) (sqF_le q6 (Nat.le_refl _) hi)) (by omega_using [hL])) fun s₄ ⟨⟨o4, l4, c, e4⟩, k4⟩ => ?_)
  obtain ev := h3.val
  rw [show 9 * q - 3 * (3 * q) = 0 by omega_using [], lv, Nat.mul_zero, Nat.add_zero, show 3 * (3 * q) = 9 * q by omega_using []] at ev
  obtain ed : dg s₃.mem B (oA q (oM q d0)) (9 * q) = dg s₂.mem B (oA q (oM q d0)) (9 * q) :=
    dg_congr fun i hi => h3.out.word (by unfold oA oT; omega_using [hi]) (by unfold oA; omega_using [hn, fit, hi])
  rw [ed, ev] at e4
  refine finish57_ok h hm (h3.ctx.of k4 (by decide) (by decide))
    ((((k1.trans k2).trans h3.keep).trans k4).mono (by decide)) ((o2.trans h3.out).trans o4) hA ha ha l4
    (no_carry e4 (lt_mul_pow hA.lt hA.lt))

/-- `mulOp57`. -/
theorem mulOp57_ok {s : State} {B : Addr} {Z q d0 N a e : Nat} (h : Sp s B Z q d0) (hm : Mod57 s B q d0 N)
    (hA : AIn s.mem B q (oM q d0) a) (ha : a < 2 * N) (lE : Lim s.mem B (oE q (oM q d0)) (9 * q) L57)
    (eE : lv s.mem B (oE q (oM q d0)) (9 * q) = e) (he : e < 2 * N) :
    WP isa mulOp57 s fun t => (Sp t B Z q d0 ∧ t.gpr .t0 = BitVec.ofNat 64 (8 * q) ∧ Mod57 t B q d0 N ∧
      OutAT B q (oM q d0) s.mem t.mem ∧ ∃ o, AIn t.mem B q (oM q d0) o ∧ o < 2 * N ∧ o * 2 ^ (513 * q) % N = a * e % N ∧ (e ≤ 1 → o ≤ N)) ∧
        Keep opRegs s t := by
  have hn := h.scr.nowrap
  unfold mulOp57
  refine WP.seq (WP.mono (enter_ok h) fun s₁ ⟨⟨i1, m1⟩, k1⟩ => ?_)
  obtain fit := i1.fit
  obtain q6 := i1.q6
  obtain dM8 := i1.dM8
  obtain hZ : oT q (oM q d0) + 144 * q ≤ Z := by unfold oT; omega_using [fit]
  refine WP.seq (WP.mono (zeroT57_ok i1) fun s₂ ⟨⟨o2, z2⟩, k2⟩ => ?_)
  rw [m1] at o2
  obtain i2 := i1.of k2 (by decide) (by decide)
  obtain A2 := hA.out o2 (.inl (Nat.le_refl _)) hn (by omega_using [hZ]) i1.q1
  obtain sE : oE q (oM q d0) = oT q (oM q d0) + 144 * q := by unfold oE oT; omega_using []
  obtain lE2 := o2.lim (Or.inr (by omega_using [sE])) (by unfold oE; omega_using [hn, fit]) lE
  obtain eE2 := (o2.lv (d := oE q (oM q d0)) (k := 9 * q) (Or.inr (by omega_using [sE])) (by unfold oE; omega_using [hn, fit])).trans eE
  refine WP.seq (WP.mono (mulRows_ok i2 A2 lE2 z2) fun s₃ h3 => ?_)
  obtain ev := h3.val
  rw [show 3 * (3 * q) = 9 * q by omega_using [], A2.val, eE2] at ev
  unfold normT
  obtain r : WP isa (.block (limbs ++ ([.addi .a0 .s5 0, .addi .a1 .s5 0, .shift .sll .d .t2 .t2 1, .add .t3 .a0 .t2] : List Instr))) s₃ fun t =>
      (t.gpr .a0 = off B (oT q (oM q d0)) ∧ t.gpr .a1 = off B (oT q (oM q d0)) ∧
        t.gpr .t3 = off B (oT q (oM q d0) + 144 * q) ∧ t.mem = s₃.mem) ∧ Keep [.t2, .a0, .a1, .t3] s₃ t := by
    rw [WP.block_append_iff]
    refine WP.mono (limbs_ok h3.ctx) fun u ⟨⟨x2, um⟩, ku⟩ => ?_
    obtain r : WP isa (.block [.addi .a0 .s5 0, .addi .a1 .s5 0, .shift .sll .d .t2 .t2 1, .add .t3 .a0 .t2]) u fun t =>
      (t.gpr .a0 = off B (oT q (oM q d0)) ∧ t.gpr .a1 = off B (oT q (oM q d0)) ∧
        t.gpr .t3 = off B (oT q (oM q d0) + 144 * q) ∧ t.mem = u.mem) ∧ Keep [.t2, .a0, .a1, .t3] u t := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [x2, (ku.gpr (r := .s5) (by decide)).trans h3.ctx.s5, shl1 (72 * q) (by omega_using [q6]), BitVec.add_zero]
      exact congrArg (off B) (by omega_using [])
    exact WP.mono r fun t ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c, d.trans um⟩, (ku.trans k).mono (by decide)⟩
  refine WP.seq (WP.seq (WP.mono r fun s₄ ⟨⟨a0, a1, t3, m4⟩, k4⟩ => ?_))
  obtain K4 := ((k1.trans k2).trans h3.keep).trans k4
  refine WP.mono (norm_ok (c := 6 * q) (dS := oT q (oM q d0)) (dD := oT q (oM q d0)) (h.scr.congr K4.2.2) a0 a1
    (by rw [t3, show 24 * (6 * q) = 144 * q by omega_using []]) (by have := i1.q1; omega_using [this]) (by unfold oT; omega_using [fit, i1.q1])
    (by omega_using [hZ]) (by unfold oT; omega_using [dM8]) (by unfold oT; omega_using [dM8])
    (.inl rfl) (by
      rw [m4, show 3 * (6 * q) = 18 * q by omega_using []]
      intro i hi
      refine Nat.le_trans (h3.lim i hi) ?_
      obtain b : 3 * q * rowMax ≤ 18 * rowMax := Nat.mul_le_mul_right _ (by omega_using [q6])
      obtain hL : L57 = 2 ^ 57 - 1 := rfl
      obtain hR : rowMax = 6 * L57 + 2 ^ 10 := rfl
      show 3 * q * rowMax ≤ 2 ^ 64 - 2 ^ 10 - 1
      omega_using [b, hL, hR])) fun s₅ ⟨⟨o5, ⟨c, e5⟩, l5⟩, k5⟩ => ?_
  rw [show 3 * (6 * q) = 18 * q by omega_using [], show 171 * (6 * q) = 1026 * q by omega_using [], m4, ev] at e5
  rw [show 3 * (6 * q) = 18 * q by omega_using []] at l5
  rw [show 24 * (6 * q) = 144 * q by omega_using [], m4] at o5
  obtain el : e < 2 ^ (513 * q) := by
    obtain l := lv_lt lE
    rw [eE, show 57 * (9 * q) = 513 * q by omega_using []] at l
    exact l
  exact finish57_ok h hm ((h3.ctx.of k4 (by decide) (by decide)).of k5 (by decide) (by decide))
    ((K4.trans k5).mono (by decide)) ((o2.trans h3.out).trans o5) hA ha he l5 (no_carry e5 (lt_mul_pow hA.lt el))

/-! ## Digits -/

theorem exec_srlReg' {s : State} {d n m : Reg} :
    exec (.shiftReg .srl .d d n m) s = some (s.write d (s.gpr n >>> ((s.gpr m).toNat % 64))) := rfl

theorem exec_sllReg' {s : State} {d n m : Reg} :
    exec (.shiftReg .sll .d d n m) s = some (s.write d (s.gpr n <<< ((s.gpr m).toNat % 64))) := rfl

theorem mod_digit (V b k : Nat) : V % 2 ^ (b * (k + 1)) = V % 2 ^ (b * k) + 2 ^ (b * k) * (V / 2 ^ (b * k) % 2 ^ b) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]

theorem lv_digits {m : Mem} {B : Addr} {d V : Nat} : ∀ {k : Nat}, (∀ i < k, (word m B (d + 8 * i)).toNat = V / 2 ^ (57 * i) % 2 ^ 57) →
    lv m B d k = V % 2 ^ (57 * k)
  | 0, _ => by rw [lv, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by rw [lv, lv_digits fun i hi => h i (by omega_using [hi]), h k (Nat.lt_succ_self k), mod_digit]

theorem wv_digits {m : Mem} {B : Addr} {d V : Nat} : ∀ {k : Nat}, (∀ i < k, (word m B (d + 8 * i)).toNat = V / 2 ^ (64 * i) % 2 ^ 64) →
    wordsVal m B d k = V % 2 ^ (64 * k)
  | 0, _ => by rw [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by rw [wordsVal_succ_top, wv_digits fun i hi => h i (by omega_using [hi]), h k (Nat.lt_succ_self k), mod_digit]

theorem wv_div (m : Mem) (B : Addr) (d j k : Nat) : wordsVal m B d (j + k) / 2 ^ (64 * j) = wordsVal m B (d + 8 * j) k := by
  rw [fios_wordsVal_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wordsVal_lt m B d j), Nat.zero_add]

theorem lv_div {m : Mem} {B : Addr} {d j k : Nat} (h : Lim m B d j L57) : lv m B d (j + k) / 2 ^ (57 * j) = lv m B (d + 8 * j) k := by
  rw [lv_append, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (lv_lt h), Nat.zero_add]

/-- The quotient of a number of two words and more. -/
theorem div_two {b x y r s t : Nat} (h : s + t = b) : (x + 2 ^ b * (y + 2 ^ b * r)) / 2 ^ s = x / 2 ^ s + 2 ^ t * (y + 2 ^ b * r) := by
  rw [← h, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s)]

theorem digit_57 {V w w' r p k s : Nat} (hp : p = 64 * k + s) (hs : s < 64) (hV : V / 2 ^ (64 * k) = w + 2 ^ 64 * (w' + 2 ^ 64 * r)) :
    V / 2 ^ p % 2 ^ 57 = (w / 2 ^ s + w' * 2 ^ (64 - s)) % 2 ^ 64 % 2 ^ 57 := by
  rw [hp, Nat.pow_add, ← Nat.div_div_eq_div_mul, hV, div_two (t := 64 - s) (by omega_using [hs])]
  rw [Nat.mod_mod_of_dvd _ (by decide : (2 : Nat) ^ 57 ∣ 2 ^ 64)]
  rw [Nat.mul_add, Nat.mul_comm w', ← Nat.add_assoc, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_comm (2 ^ (64 - s) * r) (2 ^ 64),
    show 2 ^ 64 = 2 ^ 57 * 2 ^ 7 by decide, Nat.mul_assoc (2 ^ 57), Nat.add_mul_mod_self_left]

theorem digit_64 {V x y z r p k s : Nat} (hp : p = 57 * k + s) (hs : s < 57)
    (hV : V / 2 ^ (57 * k) = x + 2 ^ 57 * (y + 2 ^ 57 * (z + 2 ^ 57 * r))) :
    V / 2 ^ p % 2 ^ 64 = (x / 2 ^ s + y * 2 ^ (57 - s) + z * 2 ^ 57 * 2 ^ (57 - s)) % 2 ^ 64 := by
  rw [hp, Nat.pow_add, ← Nat.div_div_eq_div_mul, hV, div_two (t := 57 - s) (by omega_using [hs])]
  obtain ⟨t, ht⟩ : ∃ t, 57 - s = t + 1 := ⟨56 - s, by omega_using [hs]⟩
  rw [ht]
  obtain e : x / 2 ^ s + 2 ^ (t + 1) * (y + 2 ^ 57 * (z + 2 ^ 57 * r)) =
      x / 2 ^ s + y * 2 ^ (t + 1) + z * 2 ^ 57 * 2 ^ (t + 1) + 2 ^ 64 * (2 ^ 51 * (2 ^ t * r)) := by
    rw [Nat.pow_succ]
    grind
  rw [e, Nat.add_mul_mod_self_left]

/-! ## Unpacking -/

theorem not_mod64 : ∀ i < 54, ((BitVec.ofNat 64 (57 * i) ^^^ (-BitVec.ofNat 64 1 : BitVec 64)).toNat % 64) = 63 - 57 * i % 64 := by
  decide +kernel

theorem sll_toNat (x : BitVec 64) (k : Nat) : (x <<< k).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem srl_toNat (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem unpack_val {x y : BitVec 64} {s : Nat} (hs : s < 64) :
    ((x >>> s + y <<< 1 <<< (63 - s)) &&& m57).toNat = (x.toNat / 2 ^ s + y.toNat * 2 ^ (64 - s)) % 2 ^ 64 % 2 ^ 57 := by
  rw [and_m57, BitVec.toNat_add, srl_toNat, sll_toNat, sll_toNat, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add,
    show 1 + (63 - s) = 64 - s by omega_using [hs], Nat.add_mod_mod]

def unpackRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .t2, .t4, .t5]

theorem unpack_ok {s : State} {B : Addr} {Z dS dD n w V : Nat} (hs : Scr s B Z) (h3 : s.gpr .t3 = off B dS) (h4 : s.gpr .t4 = off B dD)
    (h5 : s.gpr .t5 = BitVec.ofNat 64 n) (hn0 : 0 < n) (hn : n ≤ 54) (hw : 57 * n ≤ 64 * w + 56) (hz : word s.mem B (dS + 8 * w) = 0)
    (hV : wordsVal s.mem B dS w = V) (hS : dS + 8 * w + 8 ≤ Z) (hD : dD + 8 * n ≤ Z) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0)
    (sep : dS + 8 * w + 8 ≤ dD ∨ dD + 8 * n ≤ dS) :
    WP isa unpack s fun t => (Outside B dD (8 * n) s.mem t.mem ∧ Lim t.mem B dD n L57 ∧ lv t.mem B dD n = V % 2 ^ (57 * n)) ∧
      Keep unpackRegs s t := by
  have hnw := hs.nowrap
  unfold unpack countLoop
  obtain r : WP isa (.block [.li .s4 (-1), .shift .srl .d .s4 .s4 7, .li .t2 0]) s fun t => (t.gpr .s4 = m57 ∧ t.gpr .t2 = 0#64 ∧
      t.mem = s.mem) ∧ Keep [.s4, .t2] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li]
    rfl
  refine WP.seq (WP.mono r fun s₁ ⟨⟨x4, x2, m1⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .t5) (N := n) (by omega_using [hn]) hn0 (fun i t => t.gpr .s4 = m57 ∧
      t.gpr .t2 = BitVec.ofNat 64 (57 * i) ∧ t.gpr .t4 = off B (dD + 8 * i) ∧ Outside B dD (8 * i) s.mem t.mem ∧
      (∀ j < i, (word t.mem B (dD + 8 * j)).toNat = V / 2 ^ (57 * j) % 2 ^ 57) ∧ Keep unpackRegs s t)
    (fun i hi t ⟨t4, t2, tp, to, tv, tk⟩ _ => ?_) ⟨x4, x2, (k1.gpr (by decide)).trans h4, by rw [m1]; exact Outside.refl _ _ _ _,
      fun j hj => absurd hj (Nat.not_lt_zero j), k1.mono (by decide)⟩ ((k1.gpr (by decide)).trans h5))
    fun t ⟨_, _, _, to, tv, tk⟩ => ⟨⟨to, fun j hj => by rw [tv j hj]; exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide)), lv_digits tv⟩, tk⟩
  obtain hk : 57 * i / 64 + 1 ≤ w := by omega_using [hw, hi]
  obtain rd : ∀ j ≤ w, word t.mem B (dS + 8 * j) = word s.mem B (dS + 8 * j) := fun j hj =>
    to.word (by omega_using [sep, hj, hi]) (by omega_using [hS, hnw, hj])
  generalize ek : 57 * i / 64 = k at hk
  generalize es : 57 * i % 64 = sh
  obtain hp : 57 * i = 64 * k + sh := by rw [← ek, ← es]; omega_using []
  obtain hsh : sh < 64 := by rw [← es]; omega_using []
  obtain R0 := rd k (by omega_using [hk])
  obtain R1 := rd (k + 1) hk
  obtain a1 : BitVec.ofNat 64 (57 * i) >>> 6 <<< 3 = BitVec.ofNat 64 (8 * k) := by
    rw [srl_ofNat (by omega_using [hi, hn]), ← ek]
    apply BitVec.eq_of_toNat_eq
    rw [sll_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using []
  obtain a2 : BitVec.ofNat 64 (8 * k) + off B dS = off B (dS + 8 * k) := by
    rw [BitVec.add_comm, off_add]
  obtain a3 : (BitVec.ofNat 64 (57 * i)).toNat % 64 = sh := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 57 * i) (b := 2 ^ 64) (by omega_using [hi, hn]), es]
  obtain a4 := not_mod64 i (by omega_using [hi, hn])
  rw [es] at a4
  obtain r : WP isa (.block ([.shift .srl .d .s0 .t2 6, .shift .sll .d .s0 .s0 3, .add .s0 .s0 .t3, .load .d .s1 .s0 0,
      .load .d .s2 .s0 8, .shiftReg .srl .d .s1 .s1 .t2, .logicImm .xor .s3 .t2 (-1), .shift .sll .d .s2 .s2 1,
      .shiftReg .sll .d .s2 .s2 .s3, .add .s1 .s1 .s2, .logic .and .s1 .s1 .s4, .store .d .s1 .t4 0,
      .addi .t4 .t4 8, .addi .t2 .t2 57] ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun u =>
      (u.mem = t.mem.writeW (off B (dD + 8 * i)) ((word s.mem B (dS + 8 * k) >>> sh +
          word s.mem B (dS + 8 * (k + 1)) <<< 1 <<< (63 - sh)) &&& m57) ∧
        u.gpr .t2 = BitVec.ofNat 64 (57 * i + 57) ∧ u.gpr .t4 = off B (dD + 8 * i + 8) ∧
        u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.s0, .s1, .s2, .s3, .t2, .t4, .t5] t u := by
    obtain hs := hs.congr tk.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [t2, (tk.gpr (r := .t3) (by decide)).trans h3, tp, t4, a1, a2, a3, a4, ↓exec_srlReg', ↓exec_sllReg',
      hs.ld (show dS + 8 * k + 8 ≤ Z by omega_using [hS, hk]), hs.ld (show dS + 8 * k + 8 + 8 ≤ Z by omega_using [hS, hk]),
      hs.st (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]),
      hs.al8 (show dS + 8 * k + 8 ≤ Z by omega_using [hS, hk]) (by omega_using [hS8]),
      hs.al8 (show dS + 8 * k + 8 + 8 ≤ Z by omega_using [hS, hk]) (by omega_using [hS8]),
      hs.al8 (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]) (by omega_using [hD8]), ← BitVec.ofNat_add,
      show t.mem.readW (off B (dS + 8 * k)) 64 = word s.mem B (dS + 8 * k) from R0,
      show t.mem.readW (off B (dS + 8 * k + 8)) 64 = word s.mem B (dS + 8 * (k + 1)) from R1]
  refine WP.mono r fun u ⟨⟨um, u2, u4, u5⟩, ku⟩ => ?_
  obtain ou : Outside B (dD + 8 * i) 8 t.mem u.mem := by rw [um]; exact writeW_outside _ B _ (by omega_using [hD, hi, hnw])
  refine ⟨⟨(ku.gpr (by decide)).trans t4, by rw [u2, Nat.mul_succ], by rw [u4, Nat.mul_succ, Nat.add_assoc],
    (to.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using [])), fun j hj => ?_,
    Keep.trans' tk (ku.mono (by decide))⟩, u5⟩
  by_cases hji : j < i
  · rw [ou.word (by omega_using [hji]) (by omega_using [hD, hi, hji, hnw])]; exact tv j hji
  · obtain rfl : j = i := by omega_using [hj, hji]
    rw [um, word_writeW_self, unpack_val hsh]
    refine (digit_57 (r := wordsVal s.mem B (dS + 8 * (k + 2)) (w - k - 1)) hp hsh ?_).symm
    obtain e : V = wordsVal s.mem B dS (k + (2 + (w - k - 1))) := by
      rw [show k + (2 + (w - k - 1)) = w + 1 by omega_using [hk], wordsVal_succ_top, hz, hV]
      rfl
    rw [e, wv_div, show 2 + (w - k - 1) = (w - k - 1) + 1 + 1 by omega_using [], wordsVal, wordsVal,
      show dS + 8 * k + 8 = dS + 8 * (k + 1) by omega_using [], show dS + 8 * (k + 1) + 8 = dS + 8 * (k + 2) by omega_using []]

/-- Array 5's offset. -/
abbrev o5 (q d0 : Nat) : Nat := d0 + 320 * q + 80

theorem sll_ofNat (n k : Nat) : BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [sll_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mul_mod]

/-- `unpackFrom dst`, for `dst` that puts `dD` into `t4`. -/
theorem unpackFrom_ok {s : State} {B : Addr} {Z q d0 dD : Nat} {dst : List Instr} (h : Sp s B Z q d0)
    (hdst : ∀ u, Sp u B Z q d0 → u.gpr .t2 = BitVec.ofNat 64 (72 * q) →
      WP isa (.block dst) u fun t => (t.gpr .t4 = off B dD ∧ t.mem = u.mem) ∧ Keep [.t4] u t)
    (hD : dD + 72 * q ≤ Z) (hD8 : dD % 8 = 0) (sep : o5 q d0 + 64 * q + 8 ≤ dD ∨ dD + 72 * q ≤ o5 q d0) :
    WP isa (unpackFrom dst) s fun t => (∃ m₁, Outside B (o5 q d0 + 64 * q) 8 s.mem m₁ ∧ Outside B dD (72 * q) m₁ t.mem ∧
      Lim t.mem B dD (9 * q) L57 ∧ lv t.mem B dD (9 * q) = wordsVal s.mem B (o5 q d0) (8 * q)) ∧
      Keep (([.t3] : List Reg) ++ unpackRegs) s t := by
  obtain q2 := h.q2
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain d8 := h.d8
  have hn := h.scr.nowrap
  unfold unpackFrom
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain b1 : o5 q d0 + 64 * q + 8 ≤ Z := by unfold o5; omega_using [fit, q2]
  obtain e1 : BitVec.ofNat 64 (64 * q + 16) <<< 2 = BitVec.ofNat 64 (256 * q + 64) := by
    rw [sll_ofNat]; exact congrArg _ (by omega_using [])
  obtain e2 : BitVec.ofNat 64 (72 * q) >>> 3 = BitVec.ofNat 64 (9 * q) := by
    rw [srl_ofNat (by omega_using [q6])]; exact congrArg _ (by omega_using [])
  obtain e3 : BitVec.ofNat 64 (256 * q + 64) + BitVec.ofNat 64 (64 * q + 16) + off B d0 = off B (o5 q d0) := by
    rw [BitVec.add_comm, ← BitVec.ofNat_add, off_add]; exact congrArg (off B) (by unfold o5; omega_using [])
  obtain r : WP isa (.block [.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .add .t5 .t3 .s5, .addi .t5 .t5 (-16),
    .li .s0 0, .store .d .s0 .t5 0, .shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18),
    .shift .srl .d .t5 .t2 3]) s fun t => (t.gpr .t3 = off B (o5 q d0) ∧ t.gpr .t2 = BitVec.ofNat 64 (72 * q) ∧
      t.gpr .t5 = BitVec.ofNat 64 (9 * q) ∧ t.mem = s.mem.writeW (off B (o5 q d0 + 64 * q)) 0#64) ∧ Keep [.t3, .t5, .s0, .t2] s t := by
    obtain hs := h.scr
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.a7, h.s5, e1, e2, e3, n8_calc q6, exec_li, off_sub B (show 16 ≤ o5 q d0 + (64 * q + 16) by omega_using []),
      show o5 q d0 + (64 * q + 16) - 16 = o5 q d0 + 64 * q by omega_using [], hs.st (show o5 q d0 + 64 * q + 8 ≤ Z by omega_using [b1]),
      hs.al8 (show o5 q d0 + 64 * q + 8 ≤ Z by omega_using [b1]) (by unfold o5; omega_using [d8])]
  refine WP.mono r fun u ⟨⟨u3, u2, u5, um⟩, ku⟩ => ?_
  refine WP.mono (hdst u (h.of ku (by decide) (by decide)) u2) fun v ⟨⟨v4, vm⟩, kv⟩ => ?_
  obtain kuv := ku.trans kv
  obtain ou : Outside B (o5 q d0 + 64 * q) 8 s.mem v.mem := by rw [vm, um]; exact writeW_outside _ B _ (by omega_using [b1, hn])
  refine WP.mono (unpack_ok (w := 8 * q) (n := 9 * q) (dS := o5 q d0) (dD := dD) (h.scr.congr kuv.2.2) ((kv.gpr (by decide)).trans u3) v4
    ((kv.gpr (by decide)).trans u5) (by omega_using [q2]) (by omega_using [q6]) (by omega_using [q6])
    (by rw [show o5 q d0 + 8 * (8 * q) = o5 q d0 + 64 * q by omega_using [], vm, um, word_writeW_self]; rfl) rfl
    (by omega_using [b1]) (by omega_using [hD]) (by unfold o5; omega_using [d8]) hD8 (by omega_using [sep]))
    fun t ⟨⟨ot, lt, et⟩, kt⟩ => ⟨⟨v.mem, ou, ot.mono (Nat.le_refl _) (by omega_using []), lt, ?_⟩, (kuv.trans kt).mono (by decide)⟩
  rw [et, ou.wordsVal (by omega_using []) (by omega_using [b1, hn])]
  refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (wordsVal_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_using [])))

theorem atM_ok {u : State} {B : Addr} {Z q d0 : Nat} (h : Sp u B Z q d0) :
    WP isa (.block atM) u fun t => (t.gpr .t4 = off B (oM q d0) ∧ t.mem = u.mem) ∧ Keep [.t4] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold atM
  brun [h.a7, h.s5]
  exact congrArg (off B) (by unfold oM; omega_using [])

theorem atA_ok {u : State} {B : Addr} {Z q d0 : Nat} (h : Sp u B Z q d0) (h2 : u.gpr .t2 = BitVec.ofNat 64 (72 * q)) :
    WP isa (.block atA) u fun t => (t.gpr .t4 = off B (oA q (oM q d0)) ∧ t.mem = u.mem) ∧ Keep [.t4] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold atA atM
  brun [h.a7, h.s5, h2]
  exact congrArg (off B) (by unfold oA oM; omega_using [])

theorem atE_ok {u : State} {B : Addr} {Z q d0 : Nat} (h : Sp u B Z q d0) (h2 : u.gpr .t2 = BitVec.ofNat 64 (72 * q)) :
    WP isa (.block atE) u fun t => (t.gpr .t4 = off B (oE q (oM q d0)) ∧ t.mem = u.mem) ∧ Keep [.t4] u t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold atE atA atM
  brun [h.a7, h.s5, h2]
  exact congrArg (off B) (by unfold oE oM; omega_using [])

theorem pads_ok {s : State} {B : Addr} {Z q d0 : Nat} (h : Sp s B Z q d0) :
    WP isa (.block pads) s fun t => (Outside B (oM q d0) (144 * q + 48) s.mem t.mem ∧ lv t.mem B (oM q d0 + 72 * q) 3 = 0 ∧
      lv t.mem B (oA q (oM q d0) + 72 * q) 3 = 0) ∧ Keep [.t4, .t2, .s0] s t := by
  obtain q2 := h.q2
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain d8 := h.d8
  have hn := h.scr.nowrap
  generalize eP : oM q d0 + 72 * q = P
  generalize eQ : oA q (oM q d0) + 72 * q = Q
  obtain bP : P + 72 * q + 24 = Q := by rw [← eP, ← eQ]; unfold oA; omega_using []
  obtain bQ : Q + 24 ≤ Z := by rw [← eQ]; unfold oA oM; omega_using [fit]
  obtain P8 : P % 8 = 0 := by rw [← eP]; unfold oM; omega_using [d8]
  obtain Q8 : Q % 8 = 0 := by omega_using [bP, P8]
  obtain p0 : off B (d0 + (64 * q + 16) + (64 * q + 16) + 72 * q) = off B P :=
    congrArg (off B) (by rw [← eP]; unfold oM; omega_using [])
  obtain r : WP isa (.block pads) s fun t => (t.mem = ((((((s.mem.writeW (off B P) 0#64).writeW (off B (P + 8)) 0#64).writeW
      (off B (P + 16)) 0#64).writeW (off B Q) 0#64).writeW (off B (Q + 8)) 0#64).writeW (off B (Q + 16)) 0#64)) ∧ Keep [.t4, .t2, .s0] s t := by
    obtain hs := h.scr
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold pads
    brun [h.a7, h.s5, n8_calc q6, exec_li, p0,
      show P + (72 * q + 24) = Q by omega_using [bP], show P + (72 * q + 32) = Q + 8 by omega_using [bP],
      show P + (72 * q + 40) = Q + 16 by omega_using [bP], show P + 72 * q + 24 = Q by omega_using [bP],
      show P + 72 * q + 32 = Q + 8 by omega_using [bP],
      show P + 72 * q + 40 = Q + 16 by omega_using [bP],
      hs.st (show P + 8 ≤ Z by omega_using [bP, bQ]), hs.st (show P + 8 + 8 ≤ Z by omega_using [bP, bQ]),
      hs.st (show P + 16 + 8 ≤ Z by omega_using [bP, bQ]), hs.st (show Q + 8 ≤ Z by omega_using [bQ]),
      hs.st (show Q + 8 + 8 ≤ Z by omega_using [bQ]), hs.st (show Q + 16 + 8 ≤ Z by omega_using [bQ]),
      hs.al8 (show P + 8 ≤ Z by omega_using [bP, bQ]) P8, hs.al8 (show P + 8 + 8 ≤ Z by omega_using [bP, bQ]) (by omega_using [P8]),
      hs.al8 (show P + 16 + 8 ≤ Z by omega_using [bP, bQ]) (by omega_using [P8]), hs.al8 (show Q + 8 ≤ Z by omega_using [bQ]) Q8,
      hs.al8 (show Q + 8 + 8 ≤ Z by omega_using [bQ]) (by omega_using [Q8]), hs.al8 (show Q + 16 + 8 ≤ Z by omega_using [bQ]) (by omega_using [Q8])]
  refine WP.mono r fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_, ?_⟩, kt⟩
  · rw [tm]
    obtain wo : ∀ (m : Mem) (d : Nat), oM q d0 ≤ d → d + 8 ≤ Q + 24 → Outside B (oM q d0) (144 * q + 48) m (m.writeW (off B d) 0#64) :=
      fun m d h1 h2 => (writeW_outside m B _ (by omega_using [h2, bQ, hn])).mono h1 (by
        rw [← eQ] at h2; unfold oA at h2; omega_using [h2])
    exact ((((((wo _ _ (by omega_using [eP]) (by omega_using [bP])).trans (wo _ _ (by omega_using [eP]) (by omega_using [bP]))).trans
      (wo _ _ (by omega_using [eP]) (by omega_using [bP]))).trans (wo _ _ (by omega_using [eP, bP]) (by omega_using []))).trans
      (wo _ _ (by omega_using [eP, bP]) (by omega_using []))).trans (wo _ _ (by omega_using [eP, bP]) (by omega_using [])))
  · obtain f : ∀ (m : Mem) (d e : Nat), e + 8 ≤ d → d + 8 ≤ Z → word (m.writeW (off B d) 0#64) B e = word m B e :=
      fun m d e h1 h2 => wd_ne m B _ (.inr h1) (by omega_using [h2, hn]) (by omega_using [h1, h2, hn])
    rw [lv_three, tm, f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ, bP]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ, bP]), word_writeW_self,
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ, bP]), word_writeW_self,
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), f _ _ _ (by omega_using [bP]) (by omega_using [bQ]),
      f _ _ _ (by omega_using [bP]) (by omega_using [bQ]), word_writeW_self]
    rfl
  · obtain f : ∀ (m : Mem) (d e : Nat), e + 8 ≤ d → d + 8 ≤ Z → word (m.writeW (off B d) 0#64) B e = word m B e :=
      fun m d e h1 h2 => wd_ne m B _ (.inr h1) (by omega_using [h2, hn]) (by omega_using [h1, h2, hn])
    rw [lv_three, tm, f _ _ _ (by omega_using []) (by omega_using [bQ]), f _ _ _ (by omega_using []) (by omega_using [bQ]), word_writeW_self,
      f _ _ _ (by omega_using []) (by omega_using [bQ]), word_writeW_self, word_writeW_self]
    rfl

/-! ## Packing -/

theorem limb_of_bit : ∀ j < 48, 64 * j * 1150 / 65536 = 64 * j / 57 := by decide +kernel

theorem pack_val {x y z : BitVec 64} {s : Nat} :
    (x >>> s + y <<< (57 - s) + z <<< 57 <<< (57 - s)).toNat =
      (x.toNat / 2 ^ s + y.toNat * 2 ^ (57 - s) + z.toNat * 2 ^ 57 * 2 ^ (57 - s)) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, srl_toNat, sll_toNat, sll_toNat, sll_toNat, Nat.mod_mul_mod]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]

/-- Array 6's offset. -/
abbrev o6 (q d0 : Nat) : Nat := d0 + 384 * q + 96

def packRegs : List Reg := [.t2, .t3, .t4, .t5, .t6, .a2, .a3, .a4, .a5, .s0, .s1, .s2, .s3, .s4]

theorem pack_ok {s : State} {B : Addr} {Z q d0 a : Nat} (h : Sp s B Z q d0) (h0 : s.gpr .t0 = BitVec.ofNat 64 (8 * q))
    (hA : AIn s.mem B q (oM q d0) a) :
    WP isa pack s fun t => (Outside B (o6 q d0) (64 * q) s.mem t.mem ∧ wordsVal t.mem B (o6 q d0) (8 * q) = a % 2 ^ (64 * (8 * q))) ∧
      Keep packRegs s t := by
  obtain q2 := h.q2
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain d8 := h.d8
  have hn := h.scr.nowrap
  unfold pack countLoop
  obtain e1 : BitVec.ofNat 64 (64 * q + 16) <<< 2 = BitVec.ofNat 64 (256 * q + 64) := by
    rw [sll_ofNat]; exact congrArg _ (by omega_using [])
  obtain e3 : off (BitVec.ofNat 64 (256 * q + 64)) (64 * q + 16 + (64 * q + 16)) + off B d0 = off B (o6 q d0) := by
    rw [BitVec.add_comm, show off (BitVec.ofNat 64 (256 * q + 64)) (64 * q + 16 + (64 * q + 16)) =
      BitVec.ofNat 64 (256 * q + 64 + (64 * q + 16 + (64 * q + 16))) from BitVec.ofNat_add .. |>.symm, off_add]
    exact congrArg (off B) (by unfold o6; omega_using [])
  obtain r : WP isa (.block (([.shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18)] : List Instr) ++ atA ++
      ([.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .li .t6 0, .li .s4 57,
      .li .a2 1150, .addi .t5 .t0 0] : List Instr))) s fun t => (t.gpr .t4 = off B (oA q (oM q d0)) ∧ t.gpr .t3 = off B (o6 q d0) ∧
      t.gpr .t6 = 0#64 ∧ t.gpr .s4 = BitVec.ofNat 64 57 ∧ t.gpr .a2 = BitVec.ofNat 64 1150 ∧ t.gpr .t5 = BitVec.ofNat 64 (8 * q) ∧
      t.mem = s.mem) ∧ Keep [.t2, .t4, .t3, .t6, .s4, .a2, .t5] s t := by
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    obtain r : WP isa (.block [.shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18)]) s fun t =>
        (t.gpr .t2 = BitVec.ofNat 64 (72 * q) ∧ t.mem = s.mem) ∧ Keep [.t2] s t :=
      WP.keep _ (by brun [h.s5, n8_calc q6]) (by rfl) (by rfl)
    refine WP.mono r fun u ⟨⟨u2, um⟩, ku⟩ => ?_
    obtain hu := h.of ku (by decide) (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (atA_ok hu u2) fun v ⟨⟨v4, vm⟩, kv⟩ => ?_
    obtain hv := hu.of kv (by decide) (by decide)
    obtain r : WP isa (.block [.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .li .t6 0, .li .s4 57,
      .li .a2 1150, .addi .t5 .t0 0]) v fun t => (t.gpr .t3 = off B (o6 q d0) ∧
      t.gpr .t6 = 0#64 ∧ t.gpr .s4 = BitVec.ofNat 64 57 ∧ t.gpr .a2 = BitVec.ofNat 64 1150 ∧ t.gpr .t5 = BitVec.ofNat 64 (8 * q) ∧
      t.mem = v.mem) ∧ Keep [.t3, .t6, .s4, .a2, .t5] v t := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [hv.a7, hv.s5, e1, e3, exec_li, ((ku.trans kv).gpr (r := .t0) (by decide)).trans h0, BitVec.add_zero]
    exact WP.mono r fun t ⟨⟨a, b, c, d, e, f⟩, kt⟩ => ⟨⟨(kt.gpr (by decide)).trans v4, a, b, c, d, e, by rw [f, vm, um]⟩,
      ((ku.trans kv).trans kt).mono (by decide)⟩
  refine WP.seq (WP.mono r fun s₁ ⟨⟨x4, x3, x6, xs, xa, x5, m1⟩, k1⟩ => ?_)
  obtain bA : oA q (oM q d0) + 72 * q + 24 ≤ o6 q d0 := by unfold oA oM o6; omega_using []
  obtain bZ : o6 q d0 + 64 * q ≤ Z := by unfold o6; omega_using [fit, q2]
  obtain bA8 : oA q (oM q d0) % 8 = 0 := by unfold oA oM; omega_using [d8]
  obtain b68 : o6 q d0 % 8 = 0 := by unfold o6; omega_using [d8]
  refine WP.mono (wp_countdown (cnt := .t5) (N := 8 * q) (by omega_using [q6]) (by omega_using [q2]) (fun j t =>
      t.gpr .t4 = off B (oA q (oM q d0)) ∧ t.gpr .t3 = off B (o6 q d0 + 8 * j) ∧ t.gpr .t6 = BitVec.ofNat 64 (64 * j) ∧
      t.gpr .s4 = BitVec.ofNat 64 57 ∧ t.gpr .a2 = BitVec.ofNat 64 1150 ∧ Outside B (o6 q d0) (8 * j) s.mem t.mem ∧
      (∀ i < j, (word t.mem B (o6 q d0 + 8 * i)).toNat = a / 2 ^ (64 * i) % 2 ^ 64) ∧ Keep packRegs s t)
    (fun j hj t ⟨t4, t3, t6, ts, ta, to, tv, tk⟩ _ => ?_) ⟨x4, x3, x6, xs, xa, by rw [m1]; exact Outside.refl _ _ _ _,
      fun j hj => absurd hj (Nat.not_lt_zero j), k1.mono (by decide)⟩ x5)
    fun t ⟨_, _, _, _, _, to, tv, tk⟩ => ⟨⟨to.mono (Nat.le_refl _) (by omega_using []), wv_digits tv⟩, tk⟩
  obtain hk : 64 * j / 57 + 2 ≤ 9 * q + 2 := by omega_using [hj]
  generalize ek : 64 * j / 57 = k at hk
  obtain lm := limb_of_bit j (by omega_using [hj, q6])
  rw [ek] at lm
  obtain ⟨sh, hp, hsh⟩ : ∃ sh, 64 * j = 57 * k + sh ∧ sh < 57 := ⟨64 * j % 57, by rw [← ek]; omega_using [], by omega_using []⟩
  obtain rd : ∀ i ≤ 9 * q + 2, word t.mem B (oA q (oM q d0) + 8 * i) = word s.mem B (oA q (oM q d0) + 8 * i) := fun i hi =>
    to.word (by omega_using [bA, hi]) (by omega_using [bA, bZ, hi, hn])
  obtain R0 := rd k (by omega_using [hk])
  obtain R1 := rd (k + 1) (by omega_using [hk])
  obtain R2 := rd (k + 2) hk
  obtain a1 : (BitVec.ofNat 64 (64 * j) * BitVec.ofNat 64 1150) >>> 16 = BitVec.ofNat 64 k := by
    rw [← BitVec.ofNat_mul, srl_ofNat (by omega_using [hj, q6])]; exact congrArg _ lm
  obtain a2 : BitVec.ofNat 64 (64 * j) - BitVec.ofNat 64 k * BitVec.ofNat 64 57 = BitVec.ofNat 64 sh := by
    rw [← BitVec.ofNat_mul, sub_ofNat (by omega_using [hp])]; exact congrArg _ (by omega_using [hp])
  obtain a3 : BitVec.ofNat 64 57 - BitVec.ofNat 64 sh = BitVec.ofNat 64 (57 - sh) := sub_ofNat (Nat.le_of_lt hsh)
  obtain a4 : BitVec.ofNat 64 k <<< 3 + off B (oA q (oM q d0)) = off B (oA q (oM q d0) + 8 * k) := by
    rw [sll_ofNat, BitVec.add_comm, off_add]; exact congrArg (off B) (by omega_using [])
  obtain a5 : (BitVec.ofNat 64 sh).toNat % 64 = sh := by rw [BitVec.toNat_ofNat]; omega_using [hsh]
  obtain a6 : (BitVec.ofNat 64 (57 - sh)).toNat % 64 = 57 - sh := by rw [BitVec.toNat_ofNat]; omega_using [hsh]
  obtain r : WP isa (.block ([.mul .a3 .t6 .a2, .shift .srl .d .a3 .a3 16, .mul .a4 .a3 .s4, .sub .a4 .t6 .a4, .sub .a5 .s4 .a4,
      .shift .sll .d .a3 .a3 3, .add .a3 .a3 .t4, .load .d .s1 .a3 0, .load .d .s2 .a3 8, .load .d .s3 .a3 16,
      .shiftReg .srl .d .s1 .s1 .a4, .shiftReg .sll .d .s2 .s2 .a5, .shift .sll .d .s3 .s3 57,
      .shiftReg .sll .d .s3 .s3 .a5, .add .s1 .s1 .s2, .add .s1 .s1 .s3, .store .d .s1 .t3 0,
      .addi .t3 .t3 8, .addi .t6 .t6 64] ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun u =>
      (u.mem = t.mem.writeW (off B (o6 q d0 + 8 * j)) (word s.mem B (oA q (oM q d0) + 8 * k) >>> sh +
          word s.mem B (oA q (oM q d0) + 8 * (k + 1)) <<< (57 - sh) + word s.mem B (oA q (oM q d0) + 8 * (k + 2)) <<< 57 <<< (57 - sh)) ∧
        u.gpr .t6 = BitVec.ofNat 64 (64 * j + 64) ∧ u.gpr .t3 = off B (o6 q d0 + 8 * j + 8) ∧
        u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep [.a3, .a4, .a5, .s1, .s2, .s3, .t3, .t6, .t5] t u := by
    obtain hs := h.scr.congr tk.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [t3, t4, t6, ts, ta, a1, a2, a3, a4, a5, a6, ↓exec_srlReg', ↓exec_sllReg',
      hs.ld (show oA q (oM q d0) + 8 * k + 8 ≤ Z by omega_using [bA, bZ, hk]),
      hs.ld (show oA q (oM q d0) + 8 * k + 8 + 8 ≤ Z by omega_using [bA, bZ, hk]),
      hs.ld (show oA q (oM q d0) + 8 * k + 16 + 8 ≤ Z by omega_using [bA, bZ, hk]),
      hs.st (show o6 q d0 + 8 * j + 8 ≤ Z by omega_using [bZ, hj]),
      hs.al8 (show oA q (oM q d0) + 8 * k + 8 ≤ Z by omega_using [bA, bZ, hk]) (by omega_using [bA8]),
      hs.al8 (show oA q (oM q d0) + 8 * k + 8 + 8 ≤ Z by omega_using [bA, bZ, hk]) (by omega_using [bA8]),
      hs.al8 (show oA q (oM q d0) + 8 * k + 16 + 8 ≤ Z by omega_using [bA, bZ, hk]) (by omega_using [bA8]),
      hs.al8 (show o6 q d0 + 8 * j + 8 ≤ Z by omega_using [bZ, hj]) (by omega_using [b68]), ← BitVec.ofNat_add,
      show t.mem.readW (off B (oA q (oM q d0) + 8 * k)) 64 = word s.mem B (oA q (oM q d0) + 8 * k) from R0,
      show t.mem.readW (off B (oA q (oM q d0) + 8 * k + 8)) 64 = word s.mem B (oA q (oM q d0) + 8 * (k + 1)) from R1,
      show t.mem.readW (off B (oA q (oM q d0) + 8 * k + 16)) 64 = word s.mem B (oA q (oM q d0) + 8 * (k + 2)) from R2]
  refine WP.mono r fun u ⟨⟨um, u6, u3, u5⟩, ku⟩ => ?_
  obtain ou : Outside B (o6 q d0 + 8 * j) 8 t.mem u.mem := by rw [um]; exact writeW_outside _ B _ (by omega_using [bZ, hj, hn])
  refine ⟨⟨(ku.gpr (by decide)).trans t4, by rw [u3, Nat.mul_succ, Nat.add_assoc], by rw [u6, Nat.mul_succ],
    (ku.gpr (by decide)).trans ts, (ku.gpr (by decide)).trans ta,
    (to.mono (Nat.le_refl _) (by omega_using [])).trans (ou.mono (by omega_using []) (by omega_using [])), fun i hi => ?_,
    Keep.trans' tk (ku.mono (by decide))⟩, u5⟩
  by_cases hij : i < j
  · rw [ou.word (by omega_using [hij]) (by omega_using [bZ, hj, hij, hn])]; exact tv i hij
  · obtain rfl : i = j := by omega_using [hi, hij]
    rw [um, word_writeW_self, pack_val]
    refine (digit_64 (r := lv s.mem B (oA q (oM q d0) + 8 * (k + 3)) (9 * q - k)) hp hsh ?_).symm
    rw [← hA.pads, show 9 * q + 3 = k + (3 + (9 * q - k)) by omega_using [hk],
      lv_div (fun i' hi' => hA.lim i' (by omega_using [hi', hk])), lv_split3, lv_three,
      show oA q (oM q d0) + 8 * k + 8 = oA q (oM q d0) + 8 * (k + 1) by omega_using [],
      show oA q (oM q d0) + 8 * k + 16 = oA q (oM q d0) + 8 * (k + 2) by omega_using [],
      show oA q (oM q d0) + 8 * k + 24 = oA q (oM q d0) + 8 * (k + 3) by omega_using []]
    omega_using []

end VG.Proof.Bignum.RISCV64.Pow57
