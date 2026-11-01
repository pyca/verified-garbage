module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ML-DSA on PPC64LE: what the proofs of `HintBitPack` and `HintBitUnpack` share

The 32-bit argument `omega`, zero-extended (`zext_eq`); the comparisons of
small numbers (`ltBit`: the sign bit of a 64-bit difference); the counter of
a loop that compares with 256; and the byte loads and stores, one
instruction at a time (`wp_lbz`, `wp_stb`), as `Step.lean` has them for
words.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack.Hint

open VG VG.PPC64LE
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
theorem word_w_zero (v : BitVec 32) : ((v.setWidth 64).setWidth 32 == 0) = (v == 0) := by
  rw [lo32_ext]

theorem eval_zero_w (s : State) (r : Reg) :
    isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  change VG.PPC64LE.eval (.zero .w r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha]
  simp only [Mem.read]
  rw [VG.Proof.MlKem.PPC64LE.setWidth_zero_append]

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha]
  rfl

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

end VG.Proof.MlDsa.PPC64LE.Pack.Hint
