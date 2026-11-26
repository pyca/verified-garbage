module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Spec.Sha3
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Keccak's round constants as literals

The specification's `rc` reads a vector of the 255 positions of a shift
register's period, each computed from the start, and the kernel builds the
vector again in every check that evaluates a round constant (seconds).
`rcL` and `rcLane` are `Spec.Sha3.rc` and `RC` with a table of the bits that
the 24 rounds use, and of the 24 constants, in one number each, which
`lit_decide` and `materialize_code` read in their place. (The names of
their literals cannot be in `VG.Spec`, which only the specifications
declare.)
-/

@[expose] public section

namespace VG.Proof.Sha3

/-- The shift register's low bit at position `t`, as a number. -/
def rcBitN (t : Nat) : Nat := Nat.repeat Spec.Sha3.rcStep t 1 % 2

theorem rc_eq_bit {t : Nat} (ht : t < 255) : Spec.Sha3.rc t = (rcBitN t == 1) := by
  simp only [Spec.Sha3.rc, Spec.Sha3.rcBits, Vector.getElem_ofFn, rcBitN, Nat.mod_eq_of_lt ht]

materialize_table rcBitN 168

theorem rc_eq_lit {t : Nat} (ht : t < 255) : Spec.Sha3.rc t = (rcBitN.lit t == 1) := by
  rw [rc_eq_bit ht, ← rcBitN.lit_eq]

/-- `Spec.Sha3.rc`, from the table. -/
noncomputable abbrev rcL.lit (t : Nat) : Bool := cond (Nat.blt t 168) (rcBitN.lit t == 1) (Spec.Sha3.rc t)

theorem rcL.lit_eq : Spec.Sha3.rc = rcL.lit := by
  funext t
  rw [rcL.lit]
  cases h : Nat.blt t 168
  · rfl
  · exact rc_eq_lit (Nat.lt_trans (Nat.blt_eq.mp h) (by decide))

/-- The round constant of round `ir < 24`, as a number. -/
def rcLaneN (ir : Nat) : Nat :=
  ((List.range 7).foldl (fun RC j => if Spec.Sha3.rc (j + 7 * ir) then RC ||| (1#64 <<< (2 ^ j - 1)) else RC)
    0).toNat

materialize_table rcLaneN 24

/-- `Spec.Sha3.RC`, from the table. -/
noncomputable abbrev rcLane.lit (ir : Nat) : BitVec 64 := BitVec.ofNat 64 (rcLaneN.lit ir)

theorem rcLane.lit_eq : Spec.Sha3.RC = rcLane.lit := by
  funext ir
  rw [rcLane.lit, ← rcLaneN.lit_eq, rcLaneN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

end VG.Proof.Sha3
