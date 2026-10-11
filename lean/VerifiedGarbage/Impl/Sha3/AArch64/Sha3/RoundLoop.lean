import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector

/-!
# Keccak-f[1600] rounds in a loop, with their constants in memory

`roundsLoop core p` runs `core`, the 65 vector operations of a round before
iota, 24 times. Each iteration then loads its round constant, in both 64-bit
halves of a 16-byte entry of the table at `p` (`rcStore`), into `v26`, XORs it
into lane 0, and advances `p` by 16. `x16` counts the rounds down, so the
loop's branch depends on nothing but the count; after the loop `p` is
restored, so only `x16` and the vector registers change.
-/

namespace VG.Impl.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64

/-- The 24 round constants to `[p + off]`, each twice, through `x16`. -/
def rcStore (p : Reg) (off : Nat) : List Instr :=
  (List.range 24).flatMap fun r =>
    constant (Spec.Sha3.RC r) ++ [.str .x .x16 p (off + 16 * r), .str .x .x16 p (off + 16 * r + 8)]

/-- The vector operations of a round of the register-resident permutation before iota. -/
def core : List Instr := (theta ++ rhoPi ++ chi).map Op.instr

/-- The 24 rounds of `core` and iota, with their constants from the table at `p`. -/
def roundsLoop (core : List Instr) (p : Reg) : Prog isa :=
  .seq (.block [.movz .x .x16 24 0])
    (.seq (.loop (.block (core ++ [.ldrq .v26 p 0, .vop (.logic .eor .v0 .v0 .v26),
        .addImm .x p p 16, .subImm .x .x16 .x16 1])) (.nonzero .x .x16))
      (.block [.subImm .x p p 384]))

end VG.Impl.Sha3.AArch64.Sha3.Vector
