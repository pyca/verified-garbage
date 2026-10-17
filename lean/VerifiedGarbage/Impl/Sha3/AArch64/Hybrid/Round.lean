module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.MemLower
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
public import VerifiedGarbage.Impl.Weave

/-!
# Keccak-f[1600] on three states: two with the SHA-3 extension, one scalar

A round of two states in the vector registers (`Sha3.Vector`: theta, rho,
pi and chi with EOR3, RAX1, XAR and BCAX) woven with a round of a third
state in the general registers (`Scalar.memCoreInstrs`, its two temporary
lanes at `[sp, #off]`), so that a core runs the scalar round on its integer
pipes while the vector round occupies the SHA-3 ones. Iota follows for all
three, from one round constant in `x26` (`x16`, where the vector round keeps
it, holds a scalar lane here).
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Hybrid
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (Op)

/-- Theta, rho, pi and chi on the two vector states. -/
def vecCore : List Instr :=
  (Sha3.Vector.theta ++ Sha3.Vector.rhoPi ++ Sha3.Vector.chi).map Op.instr

/-- Iota on all three states, from the constant in `x26`. -/
def iota : List Instr :=
  [.logic .eor .x .x0 .x0 .x26, .vop (.dup .d2 .v26 .x26), .vop (.logic .eor .v0 .v0 .v26)]

/-- Round `r`, the scalar state's temporary lanes at `[sp, #off]`. -/
def round (off r : Nat) : List Instr :=
  VG.Impl.Weave.weave vecCore (Scalar.memCoreInstrs off) ++
    Scalar.Control.constant (Spec.Sha3.RC r) ++ iota

/-- The 24 rounds. -/
def rounds (off : Nat) : List Instr := (List.range 24).flatMap (round off)

end VG.Impl.Sha3.AArch64.Hybrid
