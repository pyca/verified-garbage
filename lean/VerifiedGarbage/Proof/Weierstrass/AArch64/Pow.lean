import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.Pow

/-!
# Short Weierstrass curves on AArch64: the registers powers and loops change

`powClob`: the registers the counted loops (the ladder, powers by chains) may
change, the Montgomery operations' and the counter `x19`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- The registers a power changes. -/
def powClob (n : Nat) : List Reg := .x19 :: clob n

theorem x19_not_clob (n : Nat) : Reg.x19 ∉ clob n := fun h => absurd (mem_clobAll h) (by decide)

end VG.Proof.Weierstrass.AArch64
