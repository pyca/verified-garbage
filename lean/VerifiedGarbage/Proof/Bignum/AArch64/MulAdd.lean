module

public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Multiword arithmetic on AArch64: a multiply-accumulate step

`mac down`: the word `x1 · y + c + x` (`y` at `x17`, `x` at `x16` or
`x16 + 8`, `c` represented by `x2 + C`), whose low word is stored at
`x16` and whose carry is returned as `x2 + C`; both pointers advance
(`mac_ok`). `carryOut_ok` folds C into x2 at the row boundary.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem add_ofNat0 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

theorem add_zero64 (x : BitVec 64) : x + (0 : BitVec 64) = x := BitVec.add_zero x

theorem zero_add64 (x : BitVec 64) : (0 : BitVec 64) + x = x := BitVec.zero_add x

/-- The deferred row carry is a register word and one carry flag. -/
def carry (s : State) : Nat := (s.gpr .x2).toNat + s.c.toNat

/-- A limb preserves the complete numerical sum while deferring the last
carry bit. The resulting carry still fits in one word. -/
theorem mac_val (a y c x : BitVec 64) (ci : Bool)
    (hc : c.toNat + ci.toNat < 2 ^ 64) :
    let lo := a * y + c + BitVec.ofNat 64 ci.toNat
    let hi := BitVec.ofNat 64 (a.toNat * y.toNat / 2 ^ 64) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (a * y).toNat + c.toNat + ci.toNat)).toNat
    (lo + x).toNat + 2 ^ 64 * (hi.toNat +
      (decide (2 ^ 64 ≤ lo.toNat + x.toNat)).toNat) =
      a.toNat * y.toNat + c.toNat + ci.toNat + x.toNat ∧
    hi.toNat + (decide (2 ^ 64 ≤ lo.toNat + x.toNat)).toNat < 2 ^ 64 := by
  have ha := a.isLt; have hy := y.isLt; have hx := x.isLt
  have hle : a.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega_arith) (by omega_arith)
  dsimp only
  by_cases h1 : 2 ^ 64 ≤ (a * y).toNat + c.toNat + ci.toNat <;>
  by_cases h2 : 2 ^ 64 ≤ (a * y + c + BitVec.ofNat 64 ci.toNat).toNat + x.toNat <;>
  simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  cases ci <;>
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Bool.toNat_true, Bool.toNat_false] at hc h1 h2 ⊢ <;>
  generalize a.toNat * y.toNat = P at * <;>
  omega_arith

/-- A row boundary resolves its deferred carry without changing memory. -/
theorem carryOut_ok (s : State) (h7 : s.gpr .x7 = 0) (hc : carry s < 2 ^ 64) :
    WP isa (.block carryOut) s fun t =>
      (t.mem = s.mem ∧ (t.gpr .x2).toNat = carry s) ∧ Keep [.x2] s t := by
  refine WP.keep [.x2] ?_ (by decide) (by decide) (by decide +kernel)
  unfold carryOut
  brun [h7]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show (0 : BitVec 64).toNat = 0 from rfl]
  unfold carry at hc ⊢
  have hci := Bool.toNat_le s.c
  omega_arith

/-- A multiply-accumulate step: `x1 · [x17] + (x2 + C) + [x16 + xo]` (`xo` 8 if
`down`, else 0), its low word stored at `x16`. -/
theorem mac_ok (s : State) (down : Bool) {B : Addr} {Z eD eS : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eD) (h17 : s.gpr .x17 = off B eS) (h7 : s.gpr .x7 = 0)
    (hS : eS + 8 ≤ Z) (hX : eD + (if down then 8 else 0) + 8 ≤ Z) (hD : eD + 8 ≤ Z)
    (hc : carry s < 2 ^ 64) :
    WP isa (.block (mac down)) s fun t =>
      ∃ lo : BitVec 64, t.mem = s.mem.writeW (off B eD) lo ∧
        lo.toNat + 2 ^ 64 * carry t = (s.gpr .x1).toNat * (word s.mem B eS).toNat +
          carry s + (word s.mem B (eD + if down then 8 else 0)).toNat ∧
        t.gpr .x16 = off B (eD + 8) ∧ t.gpr .x17 = off B (eS + 8) ∧ carry t < 2 ^ 64 := by
  unfold carry at hc ⊢
  cases down <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at hX ⊢ <;>
  · unfold mac
    brun [h16, h17, h7, hs.ld hS, hs.ld hX, hs.st hD]
    simp only [Bool.toNat_false, Nat.add_zero, add_ofNat0, add_zero64]
    refine ⟨_, rfl, ?_⟩
    simpa only [Nat.add_assoc] using (mac_val _ _ _ _ s.c hc)

end VG.Proof.Bignum.AArch64
