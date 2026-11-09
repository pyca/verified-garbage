module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# The digest of a hash value on ARMv7, a function of the tables of `MdHash`

`digest out` (`digest(value = r0, out = r1)`) writes the digest of the hash
value at `value` to `out`, as the streaming code whose digest code is `out`
writes it (`Impl.Pbkdf2.Md.Arm.Hash.out`, which reads the hash value at `r0`,
writes to `r6`, and writes only `r9` and `r10`): our caller's `r6`, `r9` and
`r10` are kept in `r2`, `r3` and `r12`, which `out` does not write, and `r6`
is set to `out`. It is the function 4 of a table of `MdHash`
(`Spec/MdHashTable.lean`), whose callers compress a message themselves and
take its digest from the hash value after its last block.
-/

@[expose] public section

namespace VG.Impl.MdHashTable.Arm

open VG.Arm

/-- `digest(value = r0, out = r1)`. -/
def digest (out : List Instr) : Prog isa :=
  .block ([.mov .r2 (.reg .r6), .mov .r3 (.reg .r9), .mov .r12 (.reg .r10), .mov .r6 (.reg .r1)] ++ out ++
    [.mov .r6 (.reg .r2), .mov .r9 (.reg .r3), .mov .r10 (.reg .r12)])

end VG.Impl.MdHashTable.Arm
