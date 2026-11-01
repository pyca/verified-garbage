module

public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ML-DSA on RISC-V: what the proofs of `HintBitPack` and `HintBitUnpack` share

The 32-bit argument `omega`, zero-extended (`zext_eq`); the comparisons of
small numbers (`ltBit`: the sign bit of a 64-bit difference); the counter of
a loop that compares with 256; and the byte loads and stores, one
instruction at a time (`wp_lbz`, `wp_stb`, `lbu` and `sb` with PPC64LE's
arguments).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG VG.RISCV64
open VG.Spec.MlDsa

/-- The 32-bit argument in `r`. -/
abbrev w32 (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `omega` zero-extended, as `zextOmega` leaves it. -/
theorem zext_eq (x : BitVec 64) : x <<< 32 >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by decide,
    Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by decide)]
  omega

/-- The sign bit of `x - y`, for `x` and `y` less than `2⁶³`: whether `x < y`. -/
theorem ltBit_eq {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if x < y then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  split <;> omega

/-- Whether `ltBit`'s bit is zero. -/
theorem ltBit_zero {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 == 0) = decide (y ≤ x) := by
  rw [ltBit_eq hx hy]
  split
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

/-- The counter of a loop over 256 coefficients: `j + 1 - 256`. -/
theorem cnt256 {j : Nat} (hj : j < 256) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 != 0) = decide (j + 1 ≠ 256) := by
  by_cases h : j + 1 = 256
  · rw [h]; rfl
  · rw [decide_eq_true h]
    simp only [bne_iff_ne, ne_eq]
    intro e
    apply h
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    simp at this
    omega

theorem ofNat_succ (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 1 = BitVec.ofNat 64 (x + 1) := by
  rw [BitVec.ofNat_add_ofNat]

theorem ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The low byte of a register holding a number. -/
theorem lowByte (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

/-- A byte, zero-extended, as a number. -/
theorem byte_ofNat (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, ofNat_lt (by have := b.isLt; omega),
    Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- A word, zero-extended: zero exactly when the word is. -/
theorem word_w_zero (v : BitVec 32) : (v.setWidth 64 == 0) = (v == 0) := by
  by_cases h : v = 0
  · subst h; rfl
  · have : v.setWidth 64 ≠ 0 := fun e => h (by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := v.isLt; omega)] at this
      exact this)
    rw [beq_false_of_ne this, beq_false_of_ne h]

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

/-- `beqz` of a register holding a number. -/
theorem eval_zero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.zero r) s = some (decide (k = 0)) := by
  show some (s.gpr r == 0) = _
  rw [h, Option.some.injEq]
  by_cases e : k = 0
  · subst e; rfl
  · rw [decide_eq_false e]
    refine beq_false_of_ne fun h0 => e ?_
    have := congrArg BitVec.toNat h0
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this

/-- `bnez` of a register holding a number. -/
theorem eval_nonzero_ofNat' (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.nonzero r) s = some (decide (k ≠ 0)) := by
  have e := eval_zero_ofNat s r hk h
  change some (s.gpr r == 0) = _ at e
  show some (s.gpr r != 0) = _
  rw [bne, Option.some.inj e]
  by_cases e' : k = 0 <;> simp [e']

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `lbu`, with PPC64LE's arguments (`Proof/MlDsa/PPC64LE/Pack/HintBase.lean`). -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (_hn : n ≠ .t0) (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Steps.Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .b t n off :: is)) s Q :=
  Steps.wp_lbu ho ha hin k

/-- `sb`, with PPC64LE's arguments. -/
theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (_hn : n ≠ .t0) (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Steps.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .b t n off :: is)) s Q :=
  Steps.wp_sb ho ha hout k

end

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

/-- The parameters of the hint encodings. -/
theorem mem_hintParams' {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ 55 ≤ ω ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

end VG.Proof.MlDsa.RISCV64.Pack.Hint
