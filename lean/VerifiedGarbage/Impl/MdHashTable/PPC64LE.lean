module

public import VerifiedGarbage.Impl.MdStream.PPC64LE

/-!
# The digest of a hash value on PPC64LE, a function of the tables of `MdHash`

`digest P` (`digest(value = r3, out = r4)`) writes the digest of the hash
value at `value` to `out`, as the Merkle–Damgård code of the parameters `P`
writes it (`P.out`, which reads the hash value at `r26` and writes to
`r28`, writing only `r8` and `r11`): our caller's `r26` and `r28` are kept in
`r9` and `r10`, and `r26` and `r28` set from the arguments. It is the
function 4 of a table of `MdHash` (`Spec/MdHashTable.lean`), whose callers
compress a message themselves and take its digest from the hash value after
its last block.
-/

@[expose] public section

namespace VG.Impl.MdHashTable.PPC64LE

open VG.PPC64LE VG.Impl.MdStream.PPC64LE

/-- `digest(value = r3, out = r4)`. -/
def digest (P : Params) : Prog isa :=
  .block ([mov .r9 .r26, mov .r10 .r28, mov .r26 .r3, mov .r28 .r4] ++ P.out ++ [mov .r26 .r9, mov .r28 .r10])

end VG.Impl.MdHashTable.PPC64LE
