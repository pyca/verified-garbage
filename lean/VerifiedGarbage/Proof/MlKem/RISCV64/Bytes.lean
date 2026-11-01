module

public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ML-KEM on RISC-V: bytes written

What the proofs of the functions that write bytes share: a byte after a
byte written (`byte_writeW8`), and one more byte of an invariant saying
which bytes of an output are written (`byte_one`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG

/-- Byte `k` after writing byte `a`, of the bytes at `O`. -/
theorem byte_writeW8 (m : Mem) (O : Addr) {a k : Nat} (ha : a < 2 ^ 64) (hk : k < 2 ^ 64) (v : Byte) :
    (m.writeW (O + BitVec.ofNat 64 a) v) (O + BitVec.ofNat 64 k) =
      if k = a then v else m (O + BitVec.ofNat 64 k) := by
  rw [writeW8_apply]
  by_cases h : k = a
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right]
    intro e
    apply h
    have := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp e)
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt ha] at this

/-- The next byte written, from an invariant saying which are. -/
theorem byte_one {m m₀ : Mem} {O : Addr} {out : Nat → Byte} {a L : Nat} (ha : a < L)
    (hL : L < 2 ^ 64) (h : ∀ k < L, m (O + BitVec.ofNat 64 k) = if k < a then out k else m₀ (O + BitVec.ofNat 64 k))
    {v : Byte} (hv : v = out a) :
    ∀ k < L, (m.writeW (O + BitVec.ofNat 64 a) v) (O + BitVec.ofNat 64 k) =
      if k < a + 1 then out k else m₀ (O + BitVec.ofNat 64 k) := by
  intro k hk
  rw [byte_writeW8 _ _ (by omega) (by omega), h k hk]
  by_cases e : k = a
  · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self k), hv]
  · rw [ite_eq_right e]
    by_cases hk' : k < a
    · rw [ite_eq_left hk', ite_eq_left (by omega)]
    · rw [ite_eq_right hk', ite_eq_right (by omega)]

/-- A byte of a region disjoint from one written. -/
theorem byte_writeW_disj {m : Mem} {R S : Region} (hd : R.Disjoint S) {a x : Addr} {w : Nat}
    (v : BitVec w) (ha : S.Contains a (w / 8)) (hx : R.Contains x 1) : (m.writeW a v) x = m x :=
  Mem.write_apply fun h => hd x hx (ha.byte h)

/-- A byte zero-extended, as `lbu` loads it. -/
theorem setWidth_zero_append (b : Byte) : (0#0 ++ b).setWidth 64 = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp

end VG.Proof.MlKem.RISCV64
