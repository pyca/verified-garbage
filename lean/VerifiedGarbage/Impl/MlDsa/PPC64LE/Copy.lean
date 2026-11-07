module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Frag
public import VerifiedGarbage.Impl.Gather.PPC64LE

/-!
# ML-DSA on PPC64LE: copies of whole doublewords

`copyW src dst n` copies the `n` (at least 1) doublewords at `src` to `dst`
(pointers: a register and an offset below 2³¹), with the source in `r3`, the
destination in `r9` and the count in `r5`, moved there as a call's
arguments are (`glue`), and the doubleword loop of the gathers
(`Impl/Gather/PPC64LE.lean`), which copies through `r0`. It writes only `r0`,
`r3`, `r5`, `r9` and the registers `glue` writes, all caller-saved. Prepared
keys use it to copy encoded keys and polynomials (1024 bytes, 128
doublewords).
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE

open VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen (Ptr Arg glue)

/-- The `n` doublewords at `src` to `dst`. -/
def copyW (src dst : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (glue [(.r3, .ptr src), (.r9, .ptr dst), (.r5, .imm n)])) Impl.Gather.PPC64LE.copyWords

end VG.Impl.MlDsa.PPC64LE
