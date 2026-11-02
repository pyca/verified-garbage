module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith
public import VerifiedGarbage.Proof.MlDsa.Arith.Zq
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on RISC-V: the arithmetic modulo `q`

The values the pieces of `Impl/MlDsa/RISCV64/Arith.lean` compute:

* `loadImm r v` leaves `v` in `r` (`loadImm_val`), and `consts` leaves
  `m = ⌊2⁶⁴ / q⌋` in `a5` and `q` in `a6`;
* `fixup` leaves `fixd u`: `u + q` if `u` is negative, `u` otherwise, which
  reduces a sum or a difference of reduced values (`fixd_add`, `fixd_sub`);
* `reduce` leaves `red x = x mod q` for every `x` (`red_toNat`): the
  quotient's estimate `bar x = ⌊x · m / 2⁶⁴⌋` is `⌊x / q⌋` or one less
  (`bar_le`, `lt_bar`), so `x - bar x · q < 2q`;
* `table T b` stores the 256 entries of `T`, each less than `2²³`
  (`table_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Arith

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.RISCV64 (align4_add setWidth32_ofNat)

/-! ## Constants -/

/-- `lui` of `hi20 v` and `addi` of the rest: `v`. -/
theorem loadImm_val {v : Nat} (hv : v < 2 ^ 31 - 2048) :
    sext32 (BitVec.ofNat 20 (hi20 v) ++ (0 : BitVec 12)) + BitVec.ofInt 64 ((v : Int) - 4096 * hi20 v) =
      BitVec.ofNat 64 v := by
  have hh : hi20 v < 2 ^ 19 := by unfold hi20; omega
  have e : BitVec.ofNat 20 (hi20 v) ++ (0 : BitVec 12) = BitVec.ofNat 32 (4096 * hi20 v) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    simp [Nat.shiftLeft_eq]; omega
  have es : sext32 (BitVec.ofNat 32 (4096 * hi20 v)) = BitVec.ofNat 64 (4096 * hi20 v) := by
    unfold sext32
    have hm : (BitVec.ofNat 32 (4096 * hi20 v)).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e, es]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  unfold hi20 at *
  omega

/-- The rest of `loadImm`, an `addi`'s immediate. -/
theorem loadImm_imm (v : Nat) : imm12 ((v : Int) - 4096 * hi20 v) := by
  unfold imm12 hi20; omega

theorem q_val : sext32 (BitVec.ofNat 20 (hi20 8380417) ++ (0 : BitVec 12)) +
    BitVec.ofInt 64 ((8380417 : Nat) - 4096 * hi20 8380417 : Int) = 8380417 := loadImm_val (by decide)

/-- `loadImm` of the constants, as instructions with their immediates. -/
theorem loadImm_q (r : Reg) : loadImm r 8380417 = [.lui r 0x7FE, .addi r r 1] := by
  simp only [loadImm, hi20]; rfl

/-- `loadM r`, as instructions with their immediates. -/
theorem loadM_eq (r : Reg) :
    loadM r = [.lui r 0x20080, .addi r r 448, .shift .sll .d r r 12, .addi r r 1537] := by
  simp only [loadM, loadImm, hi20]; rfl

theorem loadImm_inv (r : Reg) : loadImm r 8347681 = [.lui r 0x7F6, .addi r r 33] := by
  simp only [loadImm, hi20]; rfl

theorem q_lui : sext32 ((0x7FE : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 1 = 8380417 := by decide

theorem m_lui : (sext32 ((0x20080 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 448) <<< 12 +
    BitVec.ofInt 64 1537 = 2201172575745 := by decide

theorem inv_lui : sext32 ((0x7F6 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 33 = 8347681 := by decide

/-! ## Words -/

/-- A word sign-extended and cut back. -/
theorem setWidth_sext32 (v : BitVec 32) : (sext32 v).setWidth 32 = v := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [sext32, BitVec.getElem_setWidth, BitVec.getLsbD_signExtend]
  simp [hi]; omega

/-- A word sign-extended is zero exactly when it is. -/
theorem sext32_beq_zero (v : BitVec 32) : (sext32 v == 0) = (v == 0) := by
  by_cases h : v = 0
  · subst h; simp [sext32]
  · have : sext32 v ≠ 0 := fun e => h (by rw [← setWidth_sext32 v, e]; rfl)
    rw [beq_false_of_ne this, beq_false_of_ne h]

/-! ## Reduction modulo `q` -/

/-- What `fixup` leaves: `u + q` if `u` is negative, `u` otherwise. -/
def fixd (u : BitVec 64) : BitVec 64 := u + (u.sshiftRight 63 &&& 8380417)

theorem fixd_toNat {u : BitVec 64} (h : u.toNat < 8380417 ∨ 2 ^ 64 - 8380417 ≤ u.toNat) :
    (fixd u).toNat = if u.toNat < 8380417 then u.toNat else u.toNat + 8380417 - 2 ^ 64 := by
  unfold fixd
  cases hm : u.msb
  · have hu : u.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide u; rw [hm] at this; simp at this; omega
    have h0 : u >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, h0, BitVec.zero_and]
    split <;> bv_omega
  · have hu : 2 ^ 63 ≤ u.toNat := by
      have := BitVec.msb_eq_decide u; rw [hm] at this; simp at this; omega
    have h0 : (~~~u) >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, h0, BitVec.not_zero, BitVec.allOnes_and]
    split <;> bv_omega

/-- `fixd (a + b - q)`: the sum of reduced values, reduced. -/
theorem fixd_add {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixd (a + b - 8380417)).toNat = (a.toNat + b.toNat) % q := by
  rw [q_eq] at *
  rw [fixd_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixd (a - b)`: the difference of reduced values, reduced. -/
theorem fixd_sub {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    (fixd (a - b)).toNat = (a.toNat + q - b.toNat) % q := by
  rw [q_eq] at *
  rw [fixd_toNat (by bv_omega)]
  split <;> bv_omega

/-- `fixd (x - q)` of `x < 2q`: `x` reduced. -/
theorem fixd_subq {x : BitVec 64} (hx : x.toNat < 2 * q) : (fixd (x - 8380417)).toNat = x.toNat % q := by
  rw [q_eq] at *
  rw [fixd_toNat (by bv_omega)]
  split <;> bv_omega

/-- `m = ⌊2⁶⁴ / q⌋`, and `m q + 2365951 = 2⁶⁴`. -/
theorem m_q : 2201172575745 * q + 2365951 = 2 ^ 64 := by rw [q_eq]

/-- The quotient's estimate, `⌊x · m / 2⁶⁴⌋`, as `mulhu` computes it. -/
def bar (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat * 2201172575745 / 2 ^ 64)

/-- `x = bar x · q + e / 2⁶⁴` for `e = (x m mod 2⁶⁴) q + 2365951 x`, which is
less than `2q · 2⁶⁴`. -/
theorem bar_spec (x : Nat) (hx : x < 2 ^ 64) :
    x * 2201172575745 / 2 ^ 64 * q ≤ x ∧
      x < x * 2201172575745 / 2 ^ 64 * q + 2 * q := by
  have hd := Nat.div_add_mod (x * 2201172575745) (2 ^ 64)
  have hr := Nat.mod_lt (x * 2201172575745) (show 0 < 2 ^ 64 by decide)
  generalize x * 2201172575745 / 2 ^ 64 = T at *
  generalize x * 2201172575745 % 2 ^ 64 = R at *
  -- `x 2⁶⁴ = x (m q + 2365951) = (2⁶⁴ T + R) q + 2365951 x`
  have key : x * 2 ^ 64 = T * q * 2 ^ 64 + (R * q + 2365951 * x) := by
    have := m_q
    calc x * 2 ^ 64 = x * (2201172575745 * q + 2365951) := by rw [this]
      _ = (x * 2201172575745) * q + 2365951 * x := by rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm 2365951 x]
      _ = (2 ^ 64 * T + R) * q + 2365951 * x := by rw [hd]
      _ = T * q * 2 ^ 64 + (R * q + 2365951 * x) := by
        rw [Nat.add_mul, Nat.add_assoc, Nat.mul_comm (2 ^ 64) T, Nat.mul_right_comm T (2 ^ 64) q]
  have hq : 2365951 < q := by rw [q_eq]; decide
  -- `q` kept abstract: unifying with its value is what is slow
  generalize q = Q at *
  have e1 : R * Q < 2 ^ 64 * Q := Nat.mul_lt_mul_of_pos_right hr (by omega)
  have e2 : 2365951 * x < Q * 2 ^ 64 := Nat.mul_lt_mul_of_le_of_lt (by omega) hx (by omega)
  have hle : T * Q ≤ x :=
    Nat.le_of_mul_le_mul_right (show T * Q * 2 ^ 64 ≤ x * 2 ^ 64 by omega) (Nat.two_pow_pos 64)
  have h2 : x * 2 ^ 64 < T * Q * 2 ^ 64 + 2 * Q * 2 ^ 64 := by omega
  rw [← Nat.add_mul] at h2
  exact ⟨hle, Nat.lt_of_mul_lt_mul_right h2⟩

/-- What `reduce d t` leaves in `d`. -/
def red (x : BitVec 64) : BitVec 64 :=
  fixd (x - bar x + bar x <<< 13 - bar x <<< 13 <<< 10 - 8380417)

theorem red_toNat (x : BitVec 64) : (red x).toNat = x.toNat % q := by
  obtain ⟨hle, hlt⟩ := bar_spec x.toNat x.isLt
  have hx := x.isLt
  have hT : (bar x).toNat = x.toNat * 2201172575745 / 2 ^ 64 := by
    unfold bar; rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by rw [q_eq] at hle; omega)
  unfold red
  generalize bar x = B at hT ⊢
  generalize x.toNat * 2201172575745 / 2 ^ 64 = T at hle hlt hT
  subst hT
  rw [q_eq] at hle hlt ⊢
  have s13 : (B <<< 13).toNat = B.toNat * 8192 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have s23 : (B <<< 13 <<< 10).toNat = B.toNat * 8388608 % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, s13, Nat.shiftLeft_eq]; omega
  have v : (x - B + B <<< 13 - B <<< 13 <<< 10).toNat = x.toNat - B.toNat * 8380417 := by
    generalize B <<< 13 <<< 10 = U at *
    generalize B <<< 13 = V at *
    bv_omega
  rw [fixd_subq (by rw [v, q_eq]; omega), v, q_eq]
  have e : x.toNat = (x.toNat - B.toNat * 8380417) + 8380417 * B.toNat := by omega
  conv => rhs; rw [e]
  rw [Nat.add_mul_mod_self_left]

theorem red_lt (x : BitVec 64) : (red x).toNat < q := by
  rw [red_toNat]; exact Nat.mod_lt _ (by decide)

theorem toNat_val64 (x : Zq) : (BitVec.ofNat 64 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

/-- A product of reduced values, reduced. -/
theorem red_mul (a b : Zq) : (red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val)).toNat = (a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hp : (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val).toNat = a.val * b.val := by
    rw [BitVec.toNat_mul, toNat_val64, toNat_val64]
    exact Nat.mod_eq_of_lt (by have := mul_lt_q2 ha hb; omega)
  rw [red_toNat, hp, val_mul]

/-- A product of reduced values plus a reduced value, reduced. -/
theorem red_mulAdd (a b c : Zq) :
    (red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val + BitVec.ofNat 64 c.val)).toNat = (c + a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hc := val_lt c
  have hp : (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val + BitVec.ofNat 64 c.val).toNat =
      a.val * b.val + c.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, toNat_val64, toNat_val64, toNat_val64]
    have := mul_lt_q2 ha hb
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [red_toNat, hp, val_add', val_mul,
    Nat.add_comm (a.val * b.val), Nat.add_mod_mod]

/-- A reduced coefficient, as loaded. -/
theorem coeff64 (x : Zq) : (BitVec.ofNat 32 x.val).setWidth 64 = BitVec.ofNat 64 x.val :=
  VG.Proof.MlKem.RISCV64.setWidth64_ofNat (by have := val_lt x; omega)

/-! ## Steps -/

open VG.RISCV64.Steps (Upd)

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  Steps.WP.cons exec_mul (k _ (Steps.Upd.write _ _ _))

theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Steps.WP.cons exec_logic (k _ (Steps.Upd.write _ _ _))

theorem wp_sra {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d ((s.gpr n).sshiftRight sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sra .d d n sh :: is)) s Q :=
  Steps.WP.cons (exec_shift_d h) (k _ (Steps.Upd.write _ _ _))

/-- What a piece leaves: `d` set, the registers but `d` and `t` kept, and
the memory and permissions. -/
structure Kept2 (s s' : State) (d t : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → r ≠ t → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Kept2.trans {s s₁ s₂ : State} {d t : Reg} {v w : BitVec 64} (h₁ : Kept2 s s₁ d t v)
    (h₂ : Kept2 s₁ s₂ d t w) : Kept2 s s₂ d t w :=
  ⟨h₂.gpr, fun r h1 h2 => (h₂.other r h1 h2).trans (h₁.other r h1 h2), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

/-- `fixup d t rq`: `d + (d >> 63 & rq)`. -/
theorem fixup_ok {d t rq : Reg} (hdt : d ≠ t) (hrq : t ≠ rq)
    (k : ∀ s', Kept2 s s' d t (s.gpr d + ((s.gpr d).sshiftRight 63 &&& s.gpr rq)) → WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.MlKem.RISCV64.fixup d t rq ++ is)) s Q := by
  simp only [VG.Impl.MlKem.RISCV64.fixup, List.cons_append, List.nil_append]
  refine wp_sra (by decide) fun s₁ u₁ => wp_and fun s₂ u₂ => Steps.wp_add fun s₃ u₃ =>
    k s₃ ⟨?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.gpr, u₂.other _ hdt, u₁.gpr, u₁.other _ hdt, u₁.other _ hrq.symm]
  · rw [u₃.other _ h1, u₂.other _ h2, u₁.other _ h2]
  · rw [u₃.mem, u₂.mem, u₁.mem]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]
  · rw [u₃.sp, u₂.sp, u₁.sp]

/-- `reduce d t`: `red` of `d`. -/
theorem reduce_ok {d t : Reg} (hdt : d ≠ t) (h6d : d ≠ .a6) (h6t : t ≠ .a6)
    (h5 : s.gpr .a5 = 2201172575745) (h6 : s.gpr .a6 = 8380417)
    (k : ∀ s', Kept2 s s' d t (red (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (reduce d t ++ is)) s Q := by
  simp only [reduce, List.cons_append, List.nil_append]
  refine Steps.WP.cons exec_mulhu (Steps.wp_sub fun s₂ u₂ => Steps.wp_sll (by decide) fun s₃ u₃ =>
    Steps.wp_add fun s₄ u₄ => Steps.wp_sll (by decide) fun s₅ u₅ => Steps.wp_sub fun s₆ u₆ =>
    Steps.wp_sub fun s₇ u₇ => fixup_ok hdt h6t fun s₈ k₈ => k s₈ ⟨?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩)
  · let s₁ := s.write t (BitVec.ofNat 64 ((s.gpr d).toNat * (s.gpr .a5).toNat / 2 ^ 64))
    have e1t : s₁.gpr t = bar (s.gpr d) := by
      simp only [s₁, State.write, ite_true, h5, bar]; rfl
    have e1d : s₁.gpr d = s.gpr d := by simp only [s₁, State.write, hdt, ite_false]
    have e16 : s₁.gpr .a6 = 8380417 := by simp only [s₁, State.write, h6t.symm, ite_false, h6]
    have e2t : s₂.gpr t = bar (s.gpr d) := by rw [u₂.other _ hdt.symm, e1t]
    have e3d : s₃.gpr d = s.gpr d - bar (s.gpr d) := by rw [u₃.other _ hdt, u₂.gpr, e1d, e1t]
    have e3t : s₃.gpr t = bar (s.gpr d) <<< 13 := by rw [u₃.gpr, e2t]
    have e5t : s₅.gpr t = bar (s.gpr d) <<< 13 <<< 10 := by
      rw [u₅.gpr, u₄.other _ hdt.symm, e3t]
    have e5d : s₅.gpr d = s.gpr d - bar (s.gpr d) + bar (s.gpr d) <<< 13 := by
      rw [u₅.other _ hdt, u₄.gpr, e3d, e3t]
    have e66 : s₆.gpr .a6 = 8380417 := by
      rw [u₆.other _ h6d.symm, u₅.other _ h6t.symm, u₄.other _ h6d.symm, u₃.other _ h6t.symm,
        u₂.other _ h6d.symm, e16]
    have e7 : s₇.gpr d = s.gpr d - bar (s.gpr d) + bar (s.gpr d) <<< 13 - bar (s.gpr d) <<< 13 <<< 10 -
        8380417 := by
      rw [u₇.gpr, u₆.other _ h6d.symm, u₆.gpr, e5d, e5t, u₅.other _ h6t.symm, u₄.other _ h6d.symm,
        u₃.other _ h6t.symm, u₂.other _ h6d.symm, e16]
    have e76 : s₇.gpr .a6 = 8380417 := by rw [u₇.other _ h6d.symm, e66]
    rw [k₈.gpr, e7, e76]
    rfl
  · rw [k₈.other _ h1 h2, u₇.other _ h1, u₆.other _ h1, u₅.other _ h2, u₄.other _ h1, u₃.other _ h2,
      u₂.other _ h1]
    simp only [State.write, h2, ite_false]
  · rw [k₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]; rfl
  · rw [k₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; rfl
  · rw [k₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; rfl
  · rw [k₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; rfl

end

/-! ## Tables -/

/-- After the first `k` entries of a table at `B`. -/
structure TabInv (T : Nat → Nat) (B : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .t2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨B, 1024⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (B + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (T j)

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : Nat → Nat) (hT : ∀ k, T k < 2 ^ 23) {b : Reg} (hb : b ≠ .t2)
    {s₀ : State} {B : Addr} (hB : s₀.gpr b = B) (hal : B.toNat % 4 = 0)
    (hwr : ∀ k < 256, InRegions s₀.wr (B + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (TabInv T B s₀ 256) := by
  refine wp_range_flatMap (M := isa) (TabInv T B s₀) (fun k s hk h => ?_) 256 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hTk := hT k
  let s₁ := s.write .t2 (sext32 (BitVec.ofNat 20 (hi20 (T k)) ++ (0 : BitVec 12)))
  let s₂ := s₁.write .t2 (s₁.gpr .t2 + BitVec.ofInt 64 ((T k : Int) - 4096 * hi20 (T k)))
  have v2 : s₂.gpr .t2 = BitVec.ofNat 64 (T k) := by
    simp only [s₂, s₁, State.write, ite_true]; exact loadImm_val (by omega)
  have e : s₂.gpr b + BitVec.ofNat 64 (4 * k) = B + BitVec.ofNat 64 (4 * k) := by
    simp only [s₂, s₁, State.write, hb, ite_false, h.gpr b hb, hB]
  refine Wp.WP.cons exec_lui (Wp.WP.cons (exec_addi (loadImm_imm _))
    (Wp.WP.cons (exec_store_w (show 4 * k < 2048 by omega) (by rw [e]; exact align4_add hal k)
      (by show InRegions s₂.wr _ 4; rw [e]; exact h.wr ▸ hwr k hk)) (WP.block_nil ?_)))
  show TabInv T B s₀ (k + 1)
    { s₂ with mem := (s₂.mem.writeW (s₂.gpr b + BitVec.ofNat 64 (4 * k)) ((s₂.gpr .t2).setWidth 32)) }
  rw [e, v2, setWidth32_ofNat (v := T k) (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
    (by omega)]
  refine ⟨fun r hr => ?_, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · simp only [s₂, s₁, State.write, hr, ite_false]; exact h.gpr r hr
  · exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ 32 = _
    by_cases ej : j = k
    · subst ej; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab j (by omega)

theorem zetaTab_lt (k : Nat) : zetaTab k < 2 ^ 23 := by
  unfold zetaTab; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

theorem negZetaTab_lt (k : Nat) : negZetaTab k < 2 ^ 23 := by
  unfold negZetaTab; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

end VG.Proof.MlDsa.RISCV64.Arith
