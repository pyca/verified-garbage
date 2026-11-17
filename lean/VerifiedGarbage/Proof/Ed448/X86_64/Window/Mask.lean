module

public import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
public import VerifiedGarbage.Impl.Ed448.SignedWindow
public import VerifiedGarbage.Proof.X448.BaseTable
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ed448.Window

/-! ### `Ed448.SignedWindow`, which this module and modules that import it used -/

section

/-! ### `Ed448.Window`, which this module and modules that import it used -/

section

/-! The fixed table and scalar arithmetic for four-bit Ed448 verification windows. -/

@[expose] public section

namespace VG.Proof.Ed448.Window

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw

private def checkEntry (i : Nat) : Bool :=
  let p := pointMul i basePoint
  let q := Impl.Ed448.Window.entry i
  q.1 * p.Z == p.X && q.2 * p.Z == p.Y

private theorem entries_check : ∀ i < 16, checkEntry i = true := by decide +kernel

theorem entry_rep (i : Nat) (hi : i < 16) :
    Rep (VG.Proof.X448.basePt (Impl.Ed448.Window.entry i)) (i • baseAff) := by
  have h := entries_check i hi
  simp only [checkEntry, Bool.and_eq_true, beq_iff_eq] at h
  exact VG.Proof.X448.basePt_rep (pointMul_rep _ basePoint_rep) h.1 h.2

/-- The runtime table, defined even for malformed points. Group representation is conditional
on valid decoding, while the machine-code proof runs unconditionally. -/
def multiples (p : Point) : Nat → Point
  | 0 => identity
  | n + 1 => pointAdd (multiples p n) p

theorem multiples_rep {p : Point} {a : EPoint dZ} (h : Rep p a) :
    ∀ n, Rep (multiples p n) (n • a)
  | 0 => by rw [multiples, zero_smul]; exact identity_rep
  | n + 1 => by rw [multiples, succ_nsmul]; exact pointAdd_rep (multiples_rep h n) h

end VG.Proof.Ed448.Window

end

end

/-! Balanced five-bit recoding, including all 456 input bits. -/

@[expose] public section

namespace VG.Proof.Ed448.SignedWindow
set_option exponentiation.threshold 1024

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw

private theorem entry16_check :
    let p := pointMul 16 basePoint
    let q := Impl.Ed448.SignedWindow.entry 16
    q.1 * p.Z = p.X ∧ q.2 * p.Z = p.Y := by decide +kernel

theorem entry_rep (i : Nat) (hi : i < 17) :
    Rep (VG.Proof.X448.basePt (Impl.Ed448.SignedWindow.entry i)) (i • baseAff) := by
  by_cases he : i = 16
  · subst i
    exact VG.Proof.X448.basePt_rep (pointMul_rep _ basePoint_rep) entry16_check.1 entry16_check.2
  · simpa only [Impl.Ed448.SignedWindow.entry, ite_eq_right he] using Window.entry_rep i (by omega_using [hi, he])

def carry (k t : Nat) : Nat := if t = 0 then 0 else k / 2 ^ (t - 1) % 2

theorem bit_zero {k t : Nat} (hk : k < 2 ^ 456) (ht : 456 ≤ t) : k / 2 ^ t = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) ht))

def signedPoint (b : Bool) (p : Point) : Point := if b then negPoint p else p

theorem signedPoint_rep {p : Point} {a : EPoint dZ} {n : Nat} (h : Rep p (n • a)) (b : Bool) :
    Rep (signedPoint b p) ((if b then -(n : Int) else n) • a) := by
  cases b
  · simpa only [signedPoint, Bool.false_eq_true, ite_false, natCast_zsmul] using h
  · simpa only [signedPoint, ite_true, neg_zsmul, natCast_zsmul] using h.neg

end VG.Proof.Ed448.SignedWindow

end

end

/-! Expanded scalar bits preserved by verification's point operations. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep off ofs Outside clob mask contains_sc cswapE opSwap)
open VG.Impl.X448.X86_64 (BITS slot)

/-- The expanded scalar bits, beyond the slots every point operation modifies. -/
def Bits (base : Addr) (o k : Nat) (s : State) : Prop :=
  ∀ t < 461, s.mem (off base (o - 1 + t)) = BitVec.ofNat 8 (SignedWindow.carry k t)

theorem Bits.bit {base : Addr} {o k : Nat} {s : State} (h : Bits base o k s)
    (ho : 1 ≤ o) {t : Nat} (ht : t < 460) :
    s.mem (off base (o + t)) = BitVec.ofNat 8 (k / 2 ^ t % 2) := by
  have hh := h (t + 1) (by omega_using [ht])
  simpa only [SignedWindow.carry, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel, show o - 1 + (t + 1) = o + t by omega_using [ho]] using hh

end VG.Proof.Ed448.X86_64.Window
