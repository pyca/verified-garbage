module

import VerifiedGarbage.Proof.Rc2.RISCV64.Lookup
public import VerifiedGarbage.Impl.Rc2.RISCV64.Block
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
public import VerifiedGarbage.Spec.Rc2

/-!
# RC2 on RISC-V: the words and the key words

`Holds`: the four words are in `a3`–`a6`; `KeyEnv`: the schedule's copy is
at `a2`; `loadKey_run`: `lhu` reads a key word from the copy. The lemmas
about 16-bit words of the steps, as on PPC64LE (`Proof/Rc2/PPC64LE/Mix.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The four words are in `a3`–`a6`, zero-extended. -/
noncomputable def Holds (v : Spec.Rc2.State) (s : State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 64

/-- What the rounds need: the schedule's copy at `a2`, `T`, aligned to 8
bytes and readable. -/
structure KeyEnv (T : Addr) (s : State) : Prop where
  a2 : s.gpr .a2 = T
  al : T.toNat % 8 = 0
  rd : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 o) n

theorem KeyEnv.keep {T : Addr} {s t : State} (E : KeyEnv T s) {rs : List Reg} (h : Keep rs s t)
    (h2 : Reg.a2 ∉ rs) : KeyEnv T t :=
  ⟨by rw [h.gpr h2]; exact E.a2, E.al, fun o n hn => by rw [h.2.1, h.2.2]; exact E.rd o n hn⟩

/-! ## Words in 64-bit registers -/

theorem bv16_bytes (x : BitVec 16) :
    x = (x.extractLsb' 0 8).zeroExtend 16 ||| (x.extractLsb' 8 8).zeroExtend 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8]
  · simp only [h8, decide_false, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and,
      decide_true, show i - 8 < 8 by omega, show i - 8 < 16 by omega]
    rw [show 8 + (i - 8) = i by omega]

theorem readW16_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 2) :
    (m.readW a 16).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 2) hi]
  simp only [Mem.readW]
  rfl

theorem key_word (m : Mem) (T : Addr) {j : Nat} (hj : j < 64) :
    m.readW (T + BitVec.ofNat 64 (2 * j)) 16 = (Spec.Rc2.scheduleAt m T).getD j 0 := by
  rw [bv16_bytes (m.readW _ 16), show (0 : Nat) = 8 * 0 from rfl, show (8 : Nat) = 8 * 1 from rfl,
    readW16_byte m _ (by decide), readW16_byte m _ (by decide), Offset.add_add, Offset.add_add,
    Spec.Rc2.scheduleAt, Proof.Rc2.getD_ofFn _ _ hj]
  simp only [Nat.add_zero]

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

theorem al2 {T : Addr} (hT : T.toNat % 8 = 0) (j : Nat) : (T + BitVec.ofNat 64 (2 * j)).toNat % 2 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem loadKey_run (u : State) {T : Addr} (E : KeyEnv T u) {j : Nat} (hj : j < 64) :
    WP isa (.block (loadKey j)) u fun t =>
      (t.gpr .t2).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem ∧
        Keep [.t2] u t := by
  refine WP.mono (WP.keep (c := .block (loadKey j)) [.t2] (Q := fun t =>
      (t.gpr .t2).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold loadKey
  rrun [E.a2, E.rd (2 * j) 2 (by omega), al2 E.al j, show 2 * j < 2048 by omega]
  rw [lo16_ext, key_word _ _ hj]

end VG.Proof.Rc2.RISCV64
