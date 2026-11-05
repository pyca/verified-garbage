module

public import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# The digest of a hash value on AArch64, a function of the tables of `MdHash`

`digest P` (`digest(value = x0, out = x1)`) writes the digest of the hash
value at `value` to `out`, as the streaming code of the parameters `P`
writes it (`P.out`, which reads the hash value at `x19` and writes to `x21`,
and writes only `x9`): `x19` and `x21` are set from the arguments, and our
caller's kept in `x10` and `x11`. It is the function 4 of a table of
`MdHash` (`Spec/MdHashTable.lean`), whose callers compress a message
themselves and take its digest from the hash value after its last block, as
on x86-64 (`Impl/MdHashTable/X86_64.lean`).
-/

@[expose] public section

namespace VG.Impl.MdHashTable.AArch64

open VG.AArch64
open VG.Impl.MdStream.AArch64 (mov)

/-- `digest(value = x0, out = x1)`. -/
def digest (P : Impl.Pbkdf2.AArch64.Params) : Prog isa :=
  .block ([mov .x10 .x19, mov .x11 .x21, mov .x19 .x0, mov .x21 .x1] ++ P.out ++ [mov .x19 .x10, mov .x21 .x11])

end VG.Impl.MdHashTable.AArch64
