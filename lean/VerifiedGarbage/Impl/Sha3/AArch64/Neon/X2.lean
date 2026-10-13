module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
public import VerifiedGarbage.Spec.Sha3.X2

/-!
# Keccak-f[1600] on two interleaved states, as a function (AArch64)

`vg_keccak_f1600_x2(states, scratch)` and `vg_keccak_f1600_x2_sha3`
(`Spec/Sha3/X2.lean`; AAPCS64: `states` in `x0`, `scratch` in `x1`) run the
two-lane rounds that the paired SHAKE samplers inlined (`Pair.roundsProg`,
with the SHA-3 extension's instructions for `_sha3`): `q8`–`q15` saved in
`scratch`, both states loaded into `v0`–`v24`, the 24 rounds, the states
stored and `q8`–`q15` restored. Only `x16` and the vector registers change.

A caller (`call`) passes the states' pointer and its working space, keeps
its return address next to that working space, and squeezes the output from
memory (`squeeze`).
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.X2

open VG VG.AArch64

/-- The function's code. -/
def code (sha3 : Bool) : Prog isa :=
  .seq (.block (VG.Impl.Sha3.AArch64.Sha3.Vector.save ++ Pair.load .x0))
    (.seq (Pair.roundsProg sha3 24)
      (.block (Pair.store .x0 ++ VG.Impl.Sha3.AArch64.Sha3.Vector.restore)))

/-- `vg_keccak_f1600_x2`, and `vg_keccak_f1600_x2_sha3` for the SHA-3 extension. -/
def name (sha3 : Bool) : String :=
  Spec.Sha3.permuteX2Api.name ++ if sha3 then "_sha3" else ""

/-- A call on the states at `p`, with the function's working space at
`base + off` (`off` below 8190, in two immediates), and the caller's return
address kept in the 8 bytes after it: the working space keeps `x1` across the
call, which writes only `x16`, `x17`, `x30` and vector registers. -/
def call (sha3 : Bool) (p base : Reg) (off : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x1 base (off / 2), .addImm .x .x1 .x1 (off - off / 2),
      .str .x .x30 .x1 128, .addImm .x .x0 p 0])
    (.seq (.call (name sha3) (code sha3)) (.block [.ldr .x .x30 .x1 128]))

/-- The first `words` words of each of the states at `p`, to `a` and `b`. -/
def squeeze (words : Nat) (p a b : Reg) : List Instr :=
  (List.range words).flatMap fun i =>
    [.ldr .x .x6 p (16*i), .ldr .x .x7 p (16*i+8), .str .x .x6 a (8*i), .str .x .x7 b (8*i)]

end VG.Impl.Sha3.AArch64.Neon.X2
