import VerifiedGarbage.Impl.Weierstrass.X86_64.Inv
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.Law
import Mathlib.Data.Nat.Prime.Defs

/-!
# Inversion by divsteps on x86-64: what it computes

What the proofs of the functions that invert need, without the algebra of
its proof (`InvMain.lean`): the slots (`InvLay`), what the inversion writes
(`invW`), the configuration's facts about the modulus (`InvOk`: batches
enough for its bits, and the constants), and `InvSound m`, that the
inversion leaves `[acc] = [base]^(m - 2)` (in Montgomery form), which a prime
`m` gives (`InvSounds`). The proof of that needs Mathlib's algebra, so the
proofs of the functions take it as a hypothesis, and a curve's variant on
x86-64 (`HasLawInv`, `Variants/<Curve>/X86_64/Law.lean`) supplies it with its
group law.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass

/-- The words of the inversion's working area: `8 n + 8`. -/
def invTbl (n : Nat) : Nat := 8 * (8 * n + 8)

/-- The inversion's slots: the result, the input and the working area in the
working space, apart, and the modulus and its temporary area apart from them. -/
structure InvLay (P : InvCfg) (size : Nat) : Prop where
  n4 : 4 ≤ P.M.n
  n7 : P.M.n < 7
  acc : P.acc + 8 * P.M.n ≤ size
  base : P.base + 8 * P.M.n ≤ size
  tbl : P.tbl + invTbl P.M.n ≤ size
  mo : P.M.mo + 8 * P.M.n ≤ size
  tmp : P.M.tmp + 8 * P.M.n ≤ size
  acc_base : P.acc + 8 * P.M.n ≤ P.base ∨ P.base + 8 * P.M.n ≤ P.acc
  acc_tbl : P.acc + 8 * P.M.n ≤ P.tbl ∨ P.tbl + invTbl P.M.n ≤ P.acc
  base_tbl : P.base + 8 * P.M.n ≤ P.tbl ∨ P.tbl + invTbl P.M.n ≤ P.base
  acc_tmp : P.acc + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.acc
  tbl_tmp : P.tbl + invTbl P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.tbl
  mo_acc : P.M.mo + 8 * P.M.n ≤ P.acc ∨ P.acc + 8 * P.M.n ≤ P.M.mo
  mo_tbl : P.M.mo + 8 * P.M.n ≤ P.tbl ∨ P.tbl + invTbl P.M.n ≤ P.M.mo
  mo_tmp : P.M.mo + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.M.mo

/-- The registers the inversion changes: a power's, and the count of batches in `r14`. -/
def invClob (n : Nat) : List Reg := .r14 :: powClob n

/-- What the inversion writes: the result, the working area and the modulus's temporary area. -/
def invW (P : InvCfg) : List (Nat × Nat) :=
  [(P.acc, 8 * P.M.n), (P.tbl, invTbl P.M.n), (P.M.tmp, 8 * P.M.n)]

/-- The inversion is the modulus's: batches enough for its divsteps to end
(`590` for up to 4 words, `885` for up to 6), counts the loop can take, and
the constants `C = 2^(5 B) R³ mod m` and `Cn = m - C`. -/
structure InvOk (P : InvCfg) (m : Nat) : Prop where
  B1 : 1 ≤ P.B
  B16 : P.B < 2 ^ 16
  C : P.C = 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 % m
  Cpos : 0 < P.C
  Cn : P.Cn = m - P.C
  bound : (P.M.n ≤ 4 ∧ 590 ≤ 59 * P.B) ∨ (P.M.n ≤ 6 ∧ 885 ≤ 59 * P.B)

/-- The inversion modulo `m` leaves `[acc] = [base]^(m - 2)` (in Montgomery form). -/
def InvSound (m : Nat) [NeZero m] : Prop :=
  ∀ {P : InvCfg} {base : Addr} {size : Nat}, InvLay P size → 2 < m → UnitMod m (2 ^ (64 * P.M.n)) →
    ∀ {s : State}, Scr s base size → ModOk P.M size m s.mem base → wordsVal s.mem base P.base P.M.n < m →
      InvOk P m → WP isa (InvCfg.inv P) s fun s' =>
        KeepRegs (invClob P.M.n) s s' ∧ Unch base (invW P) s.mem s'.mem ∧
        wordsVal s'.mem base P.acc P.M.n < m ∧
        toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
          toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2)

/-- Every prime modulus's inversion is sound (`InvMain.lean`'s `invSound_of_toM`
and `InvArith.lean`'s `invToM_of_prime`). -/
def InvSounds : Prop := ∀ {m : Nat} [NeZero m], m.Prime → InvSound m

/-- The group law of `C` and the soundness of the inversions, as a value: the
variant of a curve's interface on x86-64 (`Variants/<Curve>/X86_64/Law.lean`,
see `TCB/Emit.lean`), as `HasLaw` is on the other targets. -/
structure HasLawInv (C : Spec.Weierstrass.Curve) : Type where
  law : Law C
  inv : InvSounds

theorem ofMod_C (M : Mod) (acc base tbl m : Nat) :
    (InvCfg.ofMod M acc base tbl m).C =
      2 ^ (5 * (InvCfg.ofMod M acc base tbl m).B) * (2 ^ (64 * M.n)) ^ 3 % m := rfl

theorem ofMod_Cn (M : Mod) (acc base tbl m : Nat) :
    (InvCfg.ofMod M acc base tbl m).Cn = m - (InvCfg.ofMod M acc base tbl m).C := rfl

/-- `InvOk` for `InvCfg.ofMod`: its constant nonzero, and its batches for the modulus's words. -/
theorem InvOk.ofMod {M : Mod} {acc base tbl m : Nat} (hC : 0 < (InvCfg.ofMod M acc base tbl m).C)
    (hn : M.n ≤ 6) : InvOk (InvCfg.ofMod M acc base tbl m) m := by
  refine ⟨?_, ?_, ofMod_C _ _ _ _ _, hC, ofMod_Cn _ _ _ _ _, ?_⟩ <;>
    simp only [InvCfg.ofMod] <;> split <;> omega

end VG.Proof.Weierstrass.X86_64
