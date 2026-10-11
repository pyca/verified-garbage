module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower

/-!
# The scalar permutation with its rounds unrolled

The same round core as `vectorPermute` (`vectorCoreInstrs`: the lanes in
GPRs, the two temporary lanes of theta in v24/v25), but the 24 rounds are
unrolled, each XORing its round constant into lane 0 from an immediate
(`Control.constant`, in `x26`): no table of round constants in scratch, no
pointer to it kept in AdvSIMD registers, and no loop. On Neoverse N2 the
transfers between the general and AdvSIMD registers that the counted loop
needs each round compete with the round's own integer operations.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- Round `r`: theta, rho, pi and chi, then iota from an immediate. -/
def unrolledRound (r : Nat) : List Instr :=
  vectorCoreInstrs ++ (Control.constant (Spec.Sha3.RC r) ++ ([.logic .eor .x .x0 .x0 .x26] : List Instr))

/-- The 24 rounds. -/
def unrolledRounds : List Instr := (List.range 24).flatMap unrolledRound

/-- The permutation, with the boundary of `vectorPermute`. -/
def unrolledPermute : Prog isa := Boundary.wrap (.block unrolledRounds)

end VG.Impl.Sha3.AArch64.Scalar
