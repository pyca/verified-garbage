module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Arm.Step
public import VerifiedGarbage.Proof.Mont.Words32

/-! ### `Mont.Arm.Dyn.Zeros`, which this module and modules that import it used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: clearing words

`zeros k o` clears `k` words at `[o]` through `r10`, up to `r9` (`zeros_ok`).
Pointers that loops move through the working space (`at_ptr`), and stores
into a range (`Outside.write32`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str op2_imm)

/-- A pointer `step·j` bytes past `K` bytes into the working space. -/
theorem at_ptr {t : State} {p : Reg} {B : BitVec 32} {K x : Nat} (hp : t.gpr p = B + BitVec.ofNat 32 K + BitVec.ofNat 32 x)
    (hB : t.gpr .r12 = B) : t.gpr p = t.gpr .r12 + BitVec.ofNat 32 (K + x) := by
  rw [hp, hB, Offset.add_add]

/-- A pointer `K` bytes into the working space. -/
theorem at_ptr' {t : State} {p : Reg} {B : BitVec 32} {K : Nat} (hp : t.gpr p = B + BitVec.ofNat 32 K)
    (hB : t.gpr .r12 = B) : t.gpr p = t.gpr .r12 + BitVec.ofNat 32 K := by
  rw [hp, hB]

/-- A pointer moved up a step. -/
theorem ptr_step {x B : BitVec 32} {K st j : Nat} (h : x = B + BitVec.ofNat 32 K + BitVec.ofNat 32 (st * j)) :
    x + BitVec.ofNat 32 st = B + BitVec.ofNat 32 K + BitVec.ofNat 32 (st * (j + 1)) := by
  rw [h, Offset.add_add, Offset.add_add, Offset.add_add, Nat.mul_succ]

/-- A store inside the range that may change. -/
theorem _root_.VG.Proof.Mont.Outside.write32 {base : Addr} {o n d : Nat} {m₀ m : Mem} (h : Outside base o n m₀ m)
    (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : o + n ≤ 2 ^ 64) (v : BitVec 32) :
    Outside base o n m₀ (m.writeW (off base d) v) :=
  h.trans ((writeW32_outside _ _ _ (by omega_using [h₂, hb])).mono h₁ h₂)

theorem w32_write_lt {m : Mem} {base : Addr} {o d : Nat} (hn : base.toNat + o + 4 ≤ 2 ^ 32)
    (hd : d + 4 ≤ o) (v : BitVec 32) : w32 (m.writeW (off base o) v) base d = w32 m base d :=
  w32_write_ne (size := o + 4) (by omega_using [hn]) (by omega_using []) (by omega_using [hd]) (.inl hd) v

/-- `[o] = 0`, `k` words. -/
theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {o k : Nat}
    (hk : 0 < k) (hok : o + 4 * k ≤ size) (h16 : o + 4 * k < 2 ^ 16) :
    WP isa (Dynamic.zeros k o) s fun t => Ws t base size ∧ (∀ j < k, w32 t.mem base (o + 4 * j) = 0) ∧
      Outside base o (4 * k) s.mem t.mem ∧ Rest [.r7, .r9, .r10] s t := by
  have hn := hs.nowrap
  unfold Dynamic.zeros
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega_using [h16]) fun s₁ u₁ =>
    wp_ptr (d := .r9) (by decide) (by omega_using [h16]) fun s₂ u₂ => wp_mov (op2_imm (by decide)) fun t u₃ => WP.block_nil ?_)
  have R : Rest [.r7, .r9, .r10] s t :=
    ((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))
  have wt : Ws t base size := hs.of_rest R (by decide)
  have r7 : t.gpr .r7 = 0 := u₃.gpr
  have mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have p0 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 o := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (o + 4 * k) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other .r12 (by decide)]
  clear u₁ u₂ u₃
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 o) (step := 4) (k := k)
    (fun j u => Ws u base size ∧ u.gpr .r7 = 0 ∧ Rest [.r7, .r9, .r10] s u ∧
      (∀ i < j, w32 u.mem base (o + 4 * i) = 0) ∧ Outside base o (4 * k) s.mem u.mem)
    (by decide) hk (by omega_using [h16]) (fun j u u' ⟨a, b, c, d, e⟩ f => ⟨a.of_fupd f, by rw [f.gpr]; exact b,
      c.trans (f.rest _), by rw [f.mem]; exact d, by rw [f.mem]; exact e⟩)
    ⟨wt, r7, R, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [mt]; exact Outside.refl _ _ _ _⟩
    p0 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, _, c, d, e⟩ _ => ⟨a, d, e, c⟩
  intro j hj u ⟨wu, r7u, Ru, Vu, Ou⟩ pu p9u
  have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  refine wp_str (by decide) (wu.ea (K := o + 4 * j) (at_ptr pu e12) (by omega_using [hok, hj])) (wu.write (d := o + 4 * j + 0) (n := 4) (by omega_using [hok, hj]))
    fun u₁ m₁ => wp_bump (by decide) fun u₂ v₂ => WP.block_nil ⟨⟨wu.of_mupd m₁ |>.of_upd v₂ (by decide), ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [v₂.other .r7 (by decide), m₁.gpr]; exact r7u
  · exact (Ru.trans (m₁.rest _)).trans (v₂.rest (by simp))
  · intro i hi
    rw [v₂.mem, m₁.mem]
    rcases Nat.lt_or_ge i j with h | h
    · rw [w32_write_lt (by omega_using [hok, hn, hj]) (by omega_using [h]), Vu i h]
    · rw [show i = j by omega_using [hi, h], Nat.add_zero, w32_write_self, r7u]; rfl
  · rw [v₂.mem, m₁.mem]; exact Ou.write32 (by omega_using []) (by omega_using [hj]) (by omega_using [h16]) _
  · rw [v₂.gpr, m₁.gpr, pu, Offset.add_add, Offset.add_add, Offset.add_add]; congr 2
  · rw [v₂.other .r9 (by decide), m₁.gpr]; exact p9u

end VG.Proof.Mont.Arm.Dyn

end

end

/-! ### `Mont.Arm.Dyn.Digit`, which this module and modules that import it used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: digits of a sum

A digit of `[a] + [b]` (`addDigitD_ok`) from the words in `r7` and `r2` and
the carry `r3`, stored at `[r8 + 4h]`, its carry to `r3`.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp op2_imm op2_reg op2_lsr dpVal
  toNat_add_lt toNat_shr)

theorem toNat_ofNat_dig (h : Nat) (w : Nat) : (BitVec.ofNat 32 (hdig w h)).toNat = hdig w h := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (hdig_lt _ _) (by decide))]

theorem toNat_add_eq {a b : BitVec 32} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y) (h : x + y < 2 ^ 32) :
    (a + b).toNat = x + y := by
  rw [toNat_add_lt (by rw [ha, hb]; exact h), ha, hb]

theorem toNat_sub_eq {a b : BitVec 32} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y) (h : y ≤ x) :
    (a - b).toNat = x - y := by
  rw [VG.Proof.X25519.Arm.toNat_sub_le (by rw [ha, hb]; exact h), ha, hb]

/-- A digit's sum, masked to its low half. -/
theorem and_mask_ofNat {x : BitVec 32} {v : Nat} (h : x.toNat = v) :
    x &&& VG.Proof.X25519.Arm.mask16 = BitVec.ofNat 32 (v % 2 ^ 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.toNat_and_mask16, BitVec.toNat_ofNat, h]
  omega_using []

/-- Digit `h` of `[a] + [b]`: `x + y + c` to `[r8 + 4h]` and its carry. -/
theorem addDigitD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {P h : Nat} (hh : h < 2)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (h8 : s.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 P)
    (hP : P + 4 * h + 4 ≤ size) (hc : (s.gpr .r3).toNat ≤ 1) :
    WP isa (.block (addDigitD h)) s fun u =>
      u.mem = s.mem.writeW (off base (P + 4 * h)) (BitVec.ofNat 32
        ((hdig (s.gpr .r7).toNat h + hdig (s.gpr .r2).toNat h + (s.gpr .r3).toNat) % 2 ^ 16)) ∧
      (u.gpr .r3).toNat = (hdig (s.gpr .r7).toNat h + hdig (s.gpr .r2).toNat h + (s.gpr .r3).toNat) / 2 ^ 16 ∧
      Rest [.r3, .r4, .r5] s u := by
  have hx := hdig_lt (s.gpr .r7).toNat h
  have hy := hdig_lt (s.gpr .r2).toNat h
  simp only [addDigitD]
  refine wp_half hh h6 fun s₁ u₁ => wp_half hh (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have w₅ : Ws s₅ base size :=
    ((((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)
  have e8 : s₅.gpr .r8 = s₅.gpr .r12 + BitVec.ofNat 32 P := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h8
  refine wp_str (by omega_using [hh]) (w₅.ea e8 (by omega_using [hP])) (w₅.write (by omega_using [hP])) fun s₆ m₆ =>
    wp_mov (op2_lsr (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have v4 : (s₄.gpr .r4).toNat = hdig (s.gpr .r7).toNat h + hdig (s.gpr .r2).toNat h + (s.gpr .r3).toNat := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal]
    refine toNat_add_eq (toNat_add_eq (toNat_ofNat_dig _ _) (toNat_ofNat_dig _ _) ?_) rfl ?_ <;> omega_arith
  refine ⟨?_, ?_, ?_⟩
  · rw [u₇.mem, m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    congr 1
    simp only [u₅.get, ↓reduceIte, dpVal]
    rw [u₄.other .r6 (by decide), u₃.other .r6 (by decide), u₂.other .r6 (by decide), u₁.other .r6 (by decide), h6]
    exact and_mask_ofNat v4
  · rw [u₇.gpr, toNat_shr, m₆.gpr, u₅.other .r4 (by decide), v4]
  · exact ((((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
      (u₅.rest (by simp))).trans ((m₆.rest _).trans (u₇.rest (by simp)))

end VG.Proof.Mont.Arm.Dyn

end

end

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: a sum as digits

`addDigits M acc a b` writes the `D + 1` digits of `[a] + [b]` at `[acc]`
(`addDigits_ok`), a word of each number (two digits) an iteration.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg op2_lsr dpVal
  toNat_add_lt toNat_shr)

/-- The registers the runtime-modulus arithmetic writes. -/
def dclob : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The digits up to an even count and the next two. -/
theorem dval_two (m : Mem) (base : Addr) (d j : Nat) :
    dval m base d (2 * j + 2) = dval m base d (2 * j) + w32 m base (d + 8 * j) * 2 ^ (32 * j) +
      w32 m base (d + 8 * j + 4) * (2 ^ 16 * 2 ^ (32 * j)) := by
  rw [show 2 * j + 2 = 2 * j + 1 + 1 by omega_using [], dval, dval, show d + 4 * (2 * j) = d + 8 * j by omega_using [],
    show d + 4 * (2 * j + 1) = d + 8 * j + 4 by omega_using [], show 16 * (2 * j) = 32 * j by omega_using [],
    show 16 * (2 * j + 1) = 16 + 32 * j by omega_using [], Nat.pow_add]

/-- An iteration of the addition, as numbers. -/
theorem add_step {D c A B P X Y x0 x1 y0 y1 : Nat} (h : D + c * P = A + B) (hX : X = x0 + x1 * 2 ^ 16)
    (hY : Y = y0 + y1 * 2 ^ 16) :
    D + (x0 + y0 + c) % 2 ^ 16 * P + (x1 + y1 + (x0 + y0 + c) / 2 ^ 16) % 2 ^ 16 * (2 ^ 16 * P) +
      (x1 + y1 + (x0 + y0 + c) / 2 ^ 16) / 2 ^ 16 * (2 ^ 32 * P) =
      A + P * X + (B + P * Y) := by
  subst hX hY
  obtain e0 := Nat.mod_add_div (x0 + y0 + c) (2 ^ 16)
  obtain e1 := Nat.mod_add_div (x1 + y1 + (x0 + y0 + c) / 2 ^ 16) (2 ^ 16)
  generalize (x0 + y0 + c) % 2 ^ 16 = a0 at *
  generalize (x0 + y0 + c) / 2 ^ 16 = q0 at *
  generalize (x1 + y1 + q0) % 2 ^ 16 = a1 at *
  generalize (x1 + y1 + q0) / 2 ^ 16 = q1 at *
  grind

/-- Two words stored at `Q` and `Q + 4`. -/
theorem pair_writes {m : Mem} {base : Addr} {Q : Nat} (hQ : base.toNat + Q + 8 ≤ 2 ^ 32) (v0 v1 : BitVec 32) :
    w32 ((m.writeW (off base Q) v0).writeW (off base (Q + 4)) v1) base Q = v0.toNat ∧
    w32 ((m.writeW (off base Q) v0).writeW (off base (Q + 4)) v1) base (Q + 4) = v1.toNat ∧
    Outside base Q 8 m ((m.writeW (off base Q) v0).writeW (off base (Q + 4)) v1) :=
  ⟨by rw [w32_write_lt (by omega_using [hQ]) (by omega_using []), w32_write_self], w32_write_self _ _ _ _,
    ((writeW32_outside _ _ _ (by omega_using [hQ])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hQ])).mono (by omega_using []) (by omega_using []))⟩

theorem toNat_ofNat_mod16 (v : Nat) : (BitVec.ofNat 32 (v % 2 ^ 16)).toNat = v % 2 ^ 16 := by
  rw [BitVec.toNat_ofNat]; omega_using []

/-- The digits at `[acc]` after an iteration that stored two more. -/
theorem digs_two {m m' : Mem} {base : Addr} {acc j : Nat} (hb : base.toNat + acc + 8 * j + 8 ≤ 2 ^ 32)
    (O : Outside base (acc + 8 * j) 8 m m') (hd : Digs m base acc (2 * j))
    (h0 : w32 m' base (acc + 8 * j) < 2 ^ 16) (h1 : w32 m' base (acc + 8 * j + 4) < 2 ^ 16) :
    Digs m' base acc (2 * j + 2) := by
  intro i hi
  rcases Nat.lt_or_ge i (2 * j) with h | h
  · rw [O.w32 (by omega_using [h]) (by omega_using [hb, hi])]; exact hd i h
  · rcases (by omega_using [hi, h] : i = 2 * j ∨ i = 2 * j + 1) with rfl | rfl
    · rw [show acc + 4 * (2 * j) = acc + 8 * j by omega_using []]; exact h0
    · rw [show acc + 4 * (2 * j + 1) = acc + 8 * j + 4 by omega_using []]; exact h1

/-- The loop's invariant after `j` words of `[a] + [b]`. -/
structure AddInv (s : State) (base : Addr) (size acc a b : Nat) (j : Nat) (u : State) : Prop where
  ws : Ws u base size
  rest : Rest dclob s u
  r6 : u.gpr .r6 = VG.Proof.X25519.Arm.mask16
  r3 : (u.gpr .r3).toNat ≤ 1
  r0 : u.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 b + BitVec.ofNat 32 (4 * j)
  r8 : u.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 acc + BitVec.ofNat 32 (8 * j)
  val : dval u.mem base acc (2 * j) + (u.gpr .r3).toNat * 2 ^ (32 * j) =
    val32 s.mem base a j + val32 s.mem base b j
  digs : Digs u.mem base acc (2 * j)
  out : Outside base acc (8 * j) s.mem u.mem

theorem AddInv.fupd {s : State} {base : Addr} {size acc a b j : Nat} {u u' : State}
    (h : AddInv s base size acc a b j u) (f : Fupd u u') : AddInv s base size acc a b j u' :=
  ⟨h.ws.of_fupd f, h.rest.trans (f.rest _), by rw [f.gpr]; exact h.r6, by rw [f.gpr]; exact h.r3,
    by rw [f.gpr]; exact h.r0, by rw [f.gpr]; exact h.r8, by rw [f.gpr, f.mem]; exact h.val,
    by rw [f.mem]; exact h.digs, by rw [f.mem]; exact h.out⟩

/-- `[acc] = [a] + [b]`, `D + 1` digits. -/
theorem addDigits_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc a b : Nat}
    (hn : 0 < M.n) (hacc : acc + 4 * (digits M + 1) ≤ size) (ha : a + 4 * words M ≤ size)
    (hb : b + 4 * words M ≤ size) (h16 : acc + 4 * (digits M + 1) < 2 ^ 16) (h16a : a + 4 * words M < 2 ^ 16)
    (h16b : b < 2 ^ 16) (hsa : acc + 4 * (digits M + 1) ≤ a ∨ a + 4 * words M ≤ acc)
    (hsb : acc + 4 * (digits M + 1) ≤ b ∨ b + 4 * words M ≤ acc) :
    WP isa (addDigits M acc a b) s fun t => Ws t base size ∧
      dval t.mem base acc (digits M + 1) = val32 s.mem base a (words M) + val32 s.mem base b (words M) ∧
      Digs t.mem base acc (digits M + 1) ∧ Outside base acc (4 * (digits M + 1)) s.mem t.mem ∧ Rest dclob s t := by
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  rw [hD] at hacc h16 hsa hsb ⊢
  rw [hW] at ha hb h16a hsa hsb ⊢
  obtain hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega_arith
  unfold addDigits
  rw [hW]
  refine WP.seq (wp_movw fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r0) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₅ u₅ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₆ =>
    WP.block_nil ?_)
  obtain R : Rest dclob s t := ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide)))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain I0 : AddInv s base size acc a b 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; decide
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; rfl
    · rw [mt]; exact Outside.refl _ _ _ _
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 a := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * W) := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
  clear u₁ u₂ u₃ u₄ u₅ u₆ mt R
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 a) (step := 4) (k := W)
    (AddInv s base size acc a b) (by decide) hW0 (by omega_arith) (fun _ _ _ h f => h.fupd f) I0 p10 p9 ?_
    fun u I _ => ?_)
  · -- An iteration.
    intro j hj u I pu p9u
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    obtain xa : w32 u.mem base (a + 4 * j + 0) = w32 s.mem base (a + 4 * j) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain xb : w32 u.mem base (b + 4 * j + 0) = w32 s.mem base (b + 4 * j) := I.out.w32 (by omega_arith) (by omega_arith)
    refine wp_ldr (by decide) (I.ws.ea (K := a + 4 * j) (at_ptr pu e12) (by omega_arith))
      (I.ws.read (d := a + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
    obtain w₁ := I.ws.of_upd v₁ (by decide)
    refine wp_ldr (by decide) (w₁.ea (K := b + 4 * j) (at_ptr (by rw [v₁.other .r0 (by decide)]; exact I.r0)
      (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_arith)) (w₁.read (d := b + 4 * j + 0) (n := 4) (by omega_arith))
      fun u₂ v₂ => ?_
    obtain w₂ := w₁.of_upd v₂ (by decide)
    obtain g6 : u₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
      simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact I.r6
    obtain g8 : u₂.gpr .r8 = u₂.gpr .r12 + BitVec.ofNat 32 (acc + 8 * j) := by
      simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact at_ptr I.r8 e12
    obtain g3 : u₂.gpr .r3 = u.gpr .r3 := by simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]
    obtain g7 : (u₂.gpr .r7).toNat = w32 s.mem base (a + 4 * j) := by
      simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact xa
    obtain g2 : (u₂.gpr .r2).toNat = w32 s.mem base (b + 4 * j) := by
      simp only [v₂.get, ↓reduceIte, v₁.mem]; exact xb
    refine VG.Proof.X25519.Arm.WP.append (addDigitD_ok w₂ (h := 0) (by decide) g6 g8 (by omega_arith) (by rw [g3]; exact I.r3))
      fun u₃ ⟨M₃, C₃, R₃⟩ => ?_
    obtain w₃ := w₂.of_rest R₃ (by decide)
    have := hdig_lt (u₂.gpr .r7).toNat 0
    have := hdig_lt (u₂.gpr .r2).toNat 0
    have := I.r3
    refine VG.Proof.X25519.Arm.WP.append (addDigitD_ok w₃ (P := acc + 8 * j) (h := 1) (by decide)
      (by rw [R₃.gpr _ (by decide)]; exact g6) (by rw [R₃.gpr _ (by decide), R₃.gpr _ (by decide)]; exact g8)
      (by omega_arith) (by rw [C₃, g3]; omega_arith)) fun u₄ ⟨M₄, C₄, R₄⟩ => ?_
    refine wp_bump (by decide) fun u₅ v₅ => wp_bump (by decide) fun u₆ v₆ => wp_bump (by decide) fun u₇ v₇ =>
      WP.block_nil ?_
    rw [R₃.gpr .r7 (by decide), R₃.gpr .r2 (by decide), C₃, g7, g2] at M₄ C₄
    rw [M₃, g7, g2, g3] at M₄
    rw [g3] at C₄
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at M₄
    obtain m₇ : u₇.mem = u₄.mem := by rw [v₇.mem, v₆.mem, v₅.mem]
    obtain R₇ : Rest dclob s u₇ := I.rest.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
      ((R₃.mono (by decide)).trans (R₄.mono (by decide)))).trans
      (((v₅.rest (by decide)).trans (v₆.rest (by decide))).trans (v₇.rest (by decide))))
    obtain ⟨d0, d1, O⟩ := pair_writes (m := u₂.mem) (base := base) (Q := acc + 8 * j) (by omega_arith)
      (BitVec.ofNat 32 ((hdig (w32 s.mem base (a + 4 * j)) 0 + hdig (w32 s.mem base (b + 4 * j)) 0 +
        (u.gpr .r3).toNat) % 2 ^ 16))
      (BitVec.ofNat 32 ((hdig (w32 s.mem base (a + 4 * j)) 1 + hdig (w32 s.mem base (b + 4 * j)) 1 +
        (hdig (w32 s.mem base (a + 4 * j)) 0 + hdig (w32 s.mem base (b + 4 * j)) 0 + (u.gpr .r3).toNat) / 2 ^ 16) %
        2 ^ 16))
    rw [← M₄] at d0 d1 O
    obtain mu₂ : u₂.mem = u.mem := by rw [v₂.mem, v₁.mem]
    rw [mu₂] at O
    rw [toNat_ofNat_mod16] at d0 d1
    obtain hx := word_digits (w32 s.mem base (a + 4 * j)) (BitVec.isLt _)
    obtain hy := word_digits (w32 s.mem base (b + 4 * j)) (BitVec.isLt _)
    obtain hx0 := hdig_lt (w32 s.mem base (a + 4 * j)) 0
    obtain hx1 := hdig_lt (w32 s.mem base (a + 4 * j)) 1
    obtain hy0 := hdig_lt (w32 s.mem base (b + 4 * j)) 0
    obtain hy1 := hdig_lt (w32 s.mem base (b + 4 * j)) 1
    obtain c₇ : u₇.gpr .r3 = u₄.gpr .r3 := by simp only [v₇.get, v₆.get, v₅.get, reduceCtorEq, ↓reduceIte]
    refine ⟨⟨((w₃.of_rest R₄ (by decide)).of_upd v₅ (by decide) |>.of_upd v₆ (by decide)).of_upd v₇ (by decide),
      R₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [v₇.get, v₆.get, v₅.get, reduceCtorEq, ↓reduceIte]
      rw [R₄.gpr _ (by decide), R₃.gpr _ (by decide)]; exact g6
    · rw [c₇, C₄]; omega_arith
    · simp only [v₇.get, v₆.get, v₅.get, reduceCtorEq, ↓reduceIte]
      rw [R₄.gpr _ (by decide), R₃.gpr _ (by decide), v₂.other .r0 (by decide), v₁.other .r0 (by decide)]
      exact ptr_step I.r0
    · simp only [v₇.get, v₆.get, v₅.get, reduceCtorEq, ↓reduceIte]
      rw [R₄.gpr _ (by decide), R₃.gpr _ (by decide), v₂.other .r8 (by decide), v₁.other .r8 (by decide), I.r8,
        Offset.add_add, Offset.add_add, Offset.add_add, show 8 * (j + 1) = 8 * j + 8 by omega_arith]
    · rw [m₇, c₇, C₄, show 2 * (j + 1) = 2 * j + 2 by omega_arith, dval_two, d0, d1, O.dval (by omega_arith) (by omega_arith),
        show 32 * (j + 1) = 32 + 32 * j by omega_arith, Nat.pow_add, val32_succ, val32_succ]
      exact add_step I.val hx hy
    · rw [m₇, show 2 * (j + 1) = 2 * j + 2 by omega_arith]
      exact digs_two (by omega_arith) O I.digs (by rw [d0]; omega_arith) (by rw [d1]; omega_arith)
    · rw [m₇]
      exact (I.out.mono (by omega_arith) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith))
    · simp only [v₇.get, v₆.get, v₅.get, reduceCtorEq, ↓reduceIte]
      rw [R₄.gpr _ (by decide), R₃.gpr _ (by decide), v₂.other .r10 (by decide), v₁.other .r10 (by decide)]
      exact ptr_step pu
    · simp only [v₇.get, v₆.get, v₅.get, reduceCtorEq, ↓reduceIte]
      rw [R₄.gpr _ (by decide), R₃.gpr _ (by decide), v₂.other .r9 (by decide), v₁.other .r9 (by decide)]
      exact p9u
  · -- The last digit.
    obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    refine wp_str (by decide) (I.ws.ea (K := acc + 8 * W) (d := 0) (at_ptr I.r8 e12) (by omega_arith))
      (I.ws.write (d := acc + 8 * W + 0) (n := 4) (by omega_arith)) fun t m => WP.block_nil ⟨I.ws.of_mupd m, ?_, ?_, ?_,
        I.rest.trans (m.rest _)⟩
    · rw [dval, m.mem, Nat.add_zero, show acc + 4 * (2 * W) = acc + 8 * W by omega_arith, w32_write_self,
        Outside.dval (writeW32_outside _ _ _ (by omega_arith)) (by omega_arith) (by omega_arith), ← I.val,
        show 16 * (2 * W) = 32 * W by omega_arith]
    · rw [m.mem, Nat.add_zero]
      intro i hi
      rcases Nat.lt_or_ge i (2 * W) with h | h
      · rw [w32_write_lt (by omega_arith) (by omega_arith)]; exact I.digs i h
      · have := I.r3
        rw [show i = 2 * W by omega_arith, show acc + 4 * (2 * W) = acc + 8 * W by omega_arith, w32_write_self]; omega_arith
    · rw [m.mem, Nat.add_zero]
      exact (I.out.mono (by omega_arith) (by omega_arith)).trans ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

end VG.Proof.Mont.Arm.Dyn
