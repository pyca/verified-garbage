module

public import VerifiedGarbage.Proof.Weierstrass.Layout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
public import VerifiedGarbage.Proof.Weierstrass.Pow
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Short Weierstrass curves on AArch64: the registers powers and loops change

`powClob`: the registers the counted loops (the ladder, powers by chains) may
change, the Montgomery operations' and the counter `x19`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- The registers a power changes. -/
def powClob (n : Nat) : List Reg := .x19 :: clob n

theorem x19_not_clob (n : Nat) : Reg.x19 ∉ clob n := fun h => absurd (mem_clobAll h) (by decide)

end VG.Proof.Weierstrass.AArch64
