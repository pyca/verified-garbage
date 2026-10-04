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

theorem x19_not_clob (n : Nat) : Reg.x19 ∉ clob n := by
  intro h
  simp only [clob, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h | h | h | h | h | h <;> exact absurd h (by decide)
  · have := List.mem_of_mem_take h
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at this

end VG.Proof.Weierstrass.AArch64
