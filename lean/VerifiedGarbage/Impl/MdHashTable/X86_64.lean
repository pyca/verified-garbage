module

public import VerifiedGarbage.Impl.MdStream.X86_64

/-!
# The digest of a hash value on x86-64, a function of the tables of `MdHash`

`digest P` (`digest(value = rdi, out = rsi)`) writes the digest of the hash
value at `value` to `out`, as the streaming code of the parameters `P`
writes it (`P.out`, which reads the hash value at `rbx` and writes to
`rbp`): `rbx` and `rbp` are set from the arguments, and our caller's kept in
`r8` and `r9`, which `P.out` does not write. It is the function 4 of a table
of `MdHash` (`Spec/MdHashTable.lean`), whose callers compress a message
themselves and take its digest from the hash value after its last block.
-/

@[expose] public section

namespace VG.Impl.MdHashTable.X86_64

open VG.X86_64 VG.Impl.MdStream.X86_64

/-- `digest(value = rdi, out = rsi)`. -/
def digest (P : Params) : Prog isa :=
  .block ([.mov .r8 (.reg .rbx), .mov .r9 (.reg .rbp), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi)] ++ P.out ++
    [.mov .rbx (.reg .r8), .mov .rbp (.reg .r9)])

end VG.Impl.MdHashTable.X86_64
