module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Block
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RC2 on PPC64LE: mixing and mashing

`mix_run`, `reverseMix_run` and `mash_run`: each step of the rounds maps
the four words in `r6`–`r9` (`Holds`) to the specification's step of them.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The four words are in `r6`–`r9`, zero-extended. -/
def Holds (v : Spec.Rc2.State) (s : State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 64

/-- What the rounds need: the schedule at `r3`, `T`, readable a doubleword at
a time. -/
structure KeyEnv (T : Addr) (s : State) : Prop where
  r3 : s.gpr .r3 = T
  rd : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 o) n

theorem KeyEnv.keep {T : Addr} {s t : State} (E : KeyEnv T s) {rs : List Reg} (h : Keep rs s t)
    (h3 : Reg.r3 ∉ rs) : KeyEnv T t :=
  ⟨by rw [h.gpr h3]; exact E.r3, fun o n hn => by rw [h.2.1, h.2.2]; exact E.rd o n hn⟩

/-! ## Words in 64-bit registers -/

/-- Bytes `k` and `k + 1` of a word, as a little-endian 16-bit word. -/
theorem word16_bytes (x : BitVec 32) (k : Nat) :
    (x >>> (8 * k)).setWidth 16 =
      (x.extractLsb' (8 * k) 8).zeroExtend 16 ||| (x.extractLsb' (8 * (k + 1)) 8).zeroExtend 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.truncate_eq_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8, Nat.add_comm]
  · simp only [h8, decide_false, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and,
      decide_true, show i - 8 < 8 by omega, show i - 8 < 16 by omega]
    rw [show 8 * k + i = 8 * (k + 1) + (i - 8) by omega]

theorem key_word (m : Mem) (T : Addr) {o k j : Nat} (hk : k ≤ 2) (hj : j < 64) (ho : o + k = 2 * j) :
    ((m.readW (T + BitVec.ofNat 64 o) 32) >>> (8 * k)).setWidth 16 = (Spec.Rc2.scheduleAt m T).getD j 0 := by
  rw [word16_bytes, ← Mem.readW_byte m _ (by omega), ← Mem.readW_byte m _ (by omega), Offset.add_add,
    Offset.add_add, Spec.Rc2.scheduleAt, Proof.Rc2.getD_ofFn _ _ hj]
  simp only
  rw [show o + k = 2 * j from ho, show o + (k + 1) = 2 * j + 1 by omega]

theorem lo16_add (x y : BitVec 64) : (x + y).setWidth 16 = x.setWidth 16 + y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by decide), Nat.add_mod]

theorem lo16_sub (x y : BitVec 64) : (x - y).setWidth 16 = x.setWidth 16 - y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  omega

theorem lo16_ext (x : BitVec 16) : (x.setWidth 64).setWidth 16 = x :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq x)

theorem lo16_and (x y : BitVec 64) : (x &&& y).setWidth 16 = x.setWidth 16 &&& y.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo16_xor (x y : BitVec 64) : (x ^^^ y).setWidth 16 = x.setWidth 16 ^^^ y.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem andNot_xor (a c : BitVec 16) : c ^^^ (a &&& c) = ~~~a &&& c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem mask16 (x : BitVec 64) : (x <<< 48) >>> 48 = (x.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < 16
  · simp [h, hi]; intro _; omega
  · simp [h]; intro _; omega

theorem rot16 (y : BitVec 16) {s : Nat} (h1 : 1 ≤ s) (h2 : s < 16) :
    (((y.setWidth 64 >>> (16 - s)) ||| (y.setWidth 64 <<< s)) <<< 48) >>> 48 = (y.rotateLeft s).setWidth 64 := by
  rw [mask16]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt h2]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    hi, decide_true, Bool.true_and, show i < 64 by omega]
  by_cases h : i < s
  · rw [ite_eq_left h]
    simp [h, show 16 - s + i < 64 by omega, show 16 - s + i < 16 by omega]
  · rw [ite_eq_right h]
    simp [h, show 16 - s + i < 64 by omega, show i - s < 64 by omega, show i - s < 16 by omega,
      BitVec.getLsbD_of_ge y (16 - s + i) (by omega)]

/-! ## The steps, for any registers -/

/-- The registers of a step: the word `x` it changes and the words `a`,
`b`, `c` before it, apart from each other and from the code's other
registers. -/
structure StepRegs (x a b c : Reg) : Prop where
  ne : [x, a, b, c, Reg.r0, .r3, .r4, .r5, .r10, .r11, .r12].Nodup

theorem loadKey_run (u : State) {T : Addr} (E : KeyEnv T u) {j : Nat} (hj : j < 64) :
    WP isa (.block (loadKey j)) u fun t =>
      (t.gpr .r12).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem ∧
        Keep [.r12] u t := by
  refine WP.mono (WP.keep (c := .block (loadKey j)) [.r12] (Q := fun t =>
      (t.gpr .r12).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem) ?_
    (by unfold loadKey; split <;> simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold loadKey
  split
  · rrun [E.r3, E.rd (2 * j) 4 (by omega), show 2 * j < 32768 by omega]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    have := key_word u.mem T (o := 2 * j) (k := 0) (j := j) (by decide) hj (by omega)
    rwa [Nat.mul_zero, BitVec.ushiftRight_zero] at this
  · have : j = 63 := by omega
    subst this
    rrun [E.r3, E.rd 124 4 (by decide)]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), lo32_ext]
    exact key_word u.mem T (o := 124) (k := 2) (j := 63) (by decide) (by decide) (by decide)

end VG.Proof.Rc2.PPC64LE
