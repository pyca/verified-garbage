module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Common

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_ntt_poly`

`rejNTT(seed = r3, a = r4, scratch = r5) -> r3` (see `Common.lean` for the
layout) squeezes 840 bytes of SHAKE128 of the 34 bytes of the seed (5
blocks), which the first 280 iterations of `RejNTTPoly`'s loop take 3 bytes
at a time (`rnTry 280`); in the rare case that fewer than 256 coefficients
are kept, it starts again with 1008 bytes (`rnTry 336`, 6 blocks; the least
bound of FIPS 204 Appendix C is 894 bytes), which the 336 iterations of the
loop take, as on 32-bit ARM. Starting again squeezes the first 840 bytes
again, but needs no code to continue a squeeze, and is all but never taken:
of 280 values of 23 bits, more than 24 are at least `q` with probability
below 2⁻¹²⁸. The loop runs with `r3` at the 3 bytes of the iteration, `r4` at
`a[j]`, `r5` = `j`, the number of coefficients sampled, `r6` counting down
and `r7` = `q`: the value of the 3 bytes (`b₀ + 2⁸ b₁ + 2¹⁶ (b₂ mod 2⁷)`, in
`r10`) is stored to `a[j]` and `j` incremented if it is less than `q` and
`j < 256` (the AND of two sign bits). It returns `j >> 8`: 1 if `j = 256`,
and 0 otherwise.

The loop's branches and the addresses of its stores depend on the XOF
output, a function of the seed, which the contract lets it leak.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sample

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- The value of the 3 bytes at `r3` in `r10`. -/
def rnLoad : List Instr :=
  [.lbz .r8 .r3 0, .lbz .r9 .r3 1, .lbz .r10 .r3 2, .lsl .r9 .r9 8, .lsl .r10 .r10 57, .lsr .d .r10 .r10 41,
    .add .r10 .r10 .r9, .add .r10 .r10 .r8]

def rnBody : Prog isa :=
  .seq (.block (rnLoad ++ testJ [.sub .r12 .r10 .r7]))
    (.seq (accept .r10) (.block [.addi .r3 .r3 3, .subi .r6 .r6 1]))

/-- The loop of `n` iterations, from the XOF output at `scratch + 840`. -/
def rnLoop (n : Nat) : Prog isa :=
  .seq (.block ([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] ++ loadQ))
    (.loop rnBody (.nonzero .d .r6))

/-- `3n` bytes squeezed, and the loop of `n` iterations over them. -/
def rnTry (n : Nat) : Prog isa := .seq (sponge 168 (3 * n)) (rnLoop n)

def rejNTT : Prog isa :=
  .seq (.block (pro .r5 .r4 .r3 [.li .r28 34] []))
    (.seq (rnTry 280)
      (.seq (.seq (.block [.subi .r12 .r5 256]) (.ite (.zero .d .r12) (.block []) (rnTry 336)))
        (.block (retJ ++ epi))))

end VG.Impl.MlDsa.PPC64LE.Sample
