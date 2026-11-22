module

public import VerifiedGarbage.Impl.Sha3.AArch64.Callee
public import VerifiedGarbage.Impl.ICall

/-!
# Calling a Keccak permutation by the address in `d8`

A function that is the same code for every Keccak permutation it calls
calls the permutation by its address, which its caller leaves in the low 64
bits of `v8` (`d8`, which the calling convention preserves across calls):
`umov x16, v8.d[0]`, then `blr x16`, an indirect call of `c`
(`Code.icalls`), whose printed code does not name `c`.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64

open VG.AArch64

/-- The call of `c` by the address in `v8`'s low 64 bits. -/
def Callee.viaD8 (c : Callee) : Prog isa :=
  .seq (.block [.umov .x .x16 .v8 0]) (Code.icalls (.blr .x16) [(c.name, c.code)])

end VG.Impl.Sha3.AArch64
