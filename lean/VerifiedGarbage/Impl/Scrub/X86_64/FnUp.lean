module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-!
# The cleanup at the level `sse` of code that runs AVX functions through tables (x86-64)

`scrubAllUp rb n c` is `scrubAll .sse rb n c` but for its MXCSR, which it
leaves as `scrubTail` at the level `sse` does (`scrub`'s default): for code of
the baseline ISA that may run, through its tables of functions, functions
with AVX instructions that end with `vzeroupper` (RSA's padding over the
hash functions). Clearing only the SSE registers, it needs no CPU feature;
that the upper halves of the vector registers it leaves agree between two
runs is proven of the code, not cleared (`Proof/Framework/X86_64/ScrubUpFill.lean`).
-/

@[expose] public section

namespace VG.Impl.Scrub.X86_64

open VG.X86_64

/-- `c`, then the clearing at the level `sse` of every SSE register, of
every granule of the `n` bytes below the stack pointer (`chunksA n`), and of
every caller-saved register but the `rb` bits of the result. -/
def scrubAllUp (rb n : Nat) (c : Prog isa) : Prog isa :=
  scrub .sse rb xregs (psOf (wipeKs (chunksA n))) (gsAll (wipeKs (chunksA n))) (wipeKs (chunksA n)) (chunksA n) c

/-- `scrubAllUp rb n c` at the level `sse`, `scrubAll v rb n c` at the
higher levels `v`, whose clearing the code's own CPU features allow. -/
def scrubAllOrUp (v : VecLevel) (rb n : Nat) (c : Prog isa) : Prog isa :=
  match v with
  | .sse => scrubAllUp rb n c
  | v => scrubAll v rb n c

end VG.Impl.Scrub.X86_64
