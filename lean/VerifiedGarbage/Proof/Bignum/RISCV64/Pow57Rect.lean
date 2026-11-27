module

public import VerifiedGarbage.Impl.Bignum.RISCV64.Pow57
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Three rows of products in radix `2⁵⁷` on RISC-V
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

end VG.Proof.Bignum.RISCV64.Pow57
