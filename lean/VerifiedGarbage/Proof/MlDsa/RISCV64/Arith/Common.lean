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
  `2²³ − 1` in `a5` and `q` in `a6`;
* `fixup` leaves `fixd u`: `u + q` if `u` is negative, `u` otherwise, which
  reduces a sum or a difference of reduced values (`fixd_add`, `fixd_sub`);
* `fold` leaves `bfold x`, `(x mod 2²³) + ⌊x / 2²³⌋ · (2¹³ − 1)`, congruent
  to `x` (`foldN_mod`), and `reduce` leaves `red x = x mod q` for every
  `x < 2⁴⁷` (`red_toNat`): three folds bring it below `2q` (`fold3_lt`);
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

theorem mask_val : sext32 (BitVec.ofNat 20 (hi20 8388607) ++ (0 : BitVec 12)) +
    BitVec.ofInt 64 ((8388607 : Nat) - 4096 * hi20 8388607 : Int) = 8388607 := loadImm_val (by decide)

theorem q_val : sext32 (BitVec.ofNat 20 (hi20 8380417) ++ (0 : BitVec 12)) +
    BitVec.ofInt 64 ((8380417 : Nat) - 4096 * hi20 8380417 : Int) = 8380417 := loadImm_val (by decide)

/-- `loadImm` of the constants, as instructions with their immediates. -/
theorem loadImm_q (r : Reg) : loadImm r 8380417 = [.lui r 0x7FE, .addi r r 1] := by
  simp only [loadImm, hi20]; rfl

theorem loadImm_mask (r : Reg) : loadImm r 8388607 = [.lui r 0x800, .addi r r (-1)] := by
  simp only [loadImm, hi20]; rfl

theorem loadImm_inv (r : Reg) : loadImm r 8347681 = [.lui r 0x7F6, .addi r r 33] := by
  simp only [loadImm, hi20]; rfl

theorem q_lui : sext32 ((0x7FE : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 1 = 8380417 := by decide

theorem mask_lui : sext32 ((0x800 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 (-1) = 8388607 := by
  decide

theorem inv_lui : sext32 ((0x7F6 : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 33 = 8347681 := by decide

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

/-- A fold of `x`: `2²³ ≡ 2¹³ − 1 (mod q)`. -/
def foldN (x : Nat) : Nat := x % 2 ^ 23 + x / 2 ^ 23 * 8191

theorem foldN_mod (x : Nat) : foldN x % q = x % q := by
  unfold foldN
  rw [q_eq]
  omega

theorem foldN_le (x : Nat) : foldN x ≤ 8388607 + x / 2 ^ 23 * 8191 := by
  unfold foldN; have := Nat.mod_lt x (show 0 < 2 ^ 23 by decide); omega

/-- Three folds of `x < 2⁴⁷` leave less than `2q`. -/
theorem fold3_lt {x : Nat} (hx : x < 2 ^ 47) : foldN (foldN (foldN x)) < 2 * q := by
  have h1 := foldN_le x
  have h2 := foldN_le (foldN x)
  have h3 := foldN_le (foldN (foldN x))
  rw [q_eq]
  omega

/-- What `fold d t` leaves in `d`. -/
def bfold (x : BitVec 64) : BitVec 64 := (x &&& 8388607) - x >>> 23 + (x >>> 23) <<< 13

theorem bfold_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 47) : (bfold x).toNat = foldN x.toNat := by
  have hl : (x &&& 8388607).toNat = x.toNat % 2 ^ 23 := by
    rw [BitVec.toNat_and, show (8388607 : BitVec 64).toNat = 2 ^ 23 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hh : (x >>> 23).toNat = x.toNat / 2 ^ 23 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hs : ((x >>> 23) <<< 13).toNat = x.toNat / 2 ^ 23 * 8192 := by
    rw [BitVec.toNat_shiftLeft, hh, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  unfold bfold foldN
  generalize x &&& 8388607 = l at *
  generalize (x >>> 23) <<< 13 = u at *
  generalize x >>> 23 = h at *
  have := Nat.mod_lt x.toNat (show 0 < 2 ^ 23 by decide)
  bv_omega

theorem foldN_lt {x : Nat} (hx : x < 2 ^ 47) : foldN x < 2 ^ 47 := by
  have := foldN_le x; omega

/-- What `reduce d t` leaves in `d`. -/
def red (x : BitVec 64) : BitVec 64 := fixd (bfold (bfold (bfold x)) - 8380417)

theorem red_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 47) : (red x).toNat = x.toNat % q := by
  have e1 := bfold_toNat hx
  have e2 := bfold_toNat (x := bfold x) (by rw [e1]; exact foldN_lt hx)
  have e3 := bfold_toNat (x := bfold (bfold x)) (by rw [e2, e1]; exact foldN_lt (foldN_lt hx))
  unfold red
  rw [fixd_subq (by rw [e3, e2, e1]; exact fold3_lt hx), e3, e2, e1, foldN_mod, foldN_mod, foldN_mod]

theorem red_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 47) : (red x).toNat < q := by
  rw [red_toNat hx]; exact Nat.mod_lt _ (by decide)

theorem toNat_val64 (x : Zq) : (BitVec.ofNat 64 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega)]

/-- A product of reduced values, reduced. -/
theorem red_mul (a b : Zq) : (red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val)).toNat = (a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hp : (BitVec.ofNat 64 a.val * BitVec.ofNat 64 b.val).toNat = a.val * b.val := by
    rw [BitVec.toNat_mul, toNat_val64, toNat_val64]
    exact Nat.mod_eq_of_lt (by have := mul_lt_q2 ha hb; omega)
  rw [red_toNat (by rw [hp]; have := mul_lt_q2 ha hb; omega), hp, val_mul]

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
  rw [red_toNat (by rw [hp]; have := mul_lt_q2 ha hb; omega), hp, val_add', val_mul,
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

/-- `fold d t`. -/
theorem fold_ok {d t : Reg} (hdt : d ≠ t) (h5t : t ≠ .a5) (h5 : s.gpr .a5 = 8388607)
    (k : ∀ s', Kept2 s s' d t (bfold (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (fold d t ++ is)) s Q := by
  simp only [fold, List.cons_append, List.nil_append]
  refine Steps.wp_srl (by decide) fun s₁ u₁ => wp_and fun s₂ u₂ => Steps.wp_sub fun s₃ u₃ =>
    Steps.wp_sll (by decide) fun s₄ u₄ => Steps.wp_add fun s₅ u₅ => k s₅ ⟨?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : s₁.gpr d = s.gpr d := u₁.other _ hdt
    have e2 : s₂.gpr t = s.gpr d >>> 23 := by rw [u₂.other _ hdt.symm, u₁.gpr]
    rw [u₅.gpr, u₄.other _ hdt, u₄.gpr, u₃.gpr, u₃.other _ hdt.symm, u₂.gpr, e2, e1, u₁.other _ h5t.symm, h5]
    rfl
  · rw [u₅.other _ h1, u₄.other _ h2, u₃.other _ h1, u₂.other _ h1, u₁.other _ h2]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

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
theorem reduce_ok {d t : Reg} (hdt : d ≠ t) (h5d : d ≠ .a5) (h5t : t ≠ .a5) (h6d : d ≠ .a6) (h6t : t ≠ .a6)
    (h5 : s.gpr .a5 = 8388607) (h6 : s.gpr .a6 = 8380417)
    (k : ∀ s', Kept2 s s' d t (red (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (reduce d t ++ is)) s Q := by
  simp only [reduce, List.append_assoc]
  refine fold_ok hdt h5t h5 fun s₁ k₁ => fold_ok hdt h5t (by rw [k₁.other _ h5d.symm h5t.symm, h5])
    fun s₂ k₂ => fold_ok hdt h5t (by rw [k₂.other _ h5d.symm h5t.symm, k₁.other _ h5d.symm h5t.symm, h5])
    fun s₃ k₃ => ?_
  rw [List.cons_append]
  refine Steps.wp_sub fun s₄ u₄ => fixup_ok hdt h6t fun s₅ k₅ => k s₅ ?_
  have k₄ : Kept2 s₃ s₄ d t (s₃.gpr d - 8380417) :=
    ⟨by rw [u₄.gpr, k₃.other _ h6d.symm h6t.symm, k₂.other _ h6d.symm h6t.symm, k₁.other _ h6d.symm h6t.symm, h6],
      fun r h1 _ => u₄.other r h1, u₄.mem, u₄.rd, u₄.wr, u₄.sp⟩
  have e6 : s₄.gpr .a6 = 8380417 := by
    rw [u₄.other _ h6d.symm, k₃.other _ h6d.symm h6t.symm, k₂.other _ h6d.symm h6t.symm,
      k₁.other _ h6d.symm h6t.symm, h6]
  refine (k₁.trans (k₂.trans (k₃.trans (k₄.trans k₅)))) |> fun K => ⟨?_, K.other, K.mem, K.rd, K.wr, K.sp⟩
  rw [K.gpr, k₄.gpr, k₃.gpr, k₂.gpr, k₁.gpr, e6]
  rfl

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
