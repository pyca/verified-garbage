module

public import VerifiedGarbage.TCB.X86.Isa

/-!
# The digest of a hash value on x86 (32-bit), a function of the tables of `MdHash`

`digest out` writes the digest of the hash value at `ebx` to `eax`, as the
streaming code's digest code `out` writes it (`Impl.MdStream.X86.Params.out`,
which writes only `ecx` and `edx`, and the flags): its arguments are in
those two registers, which the callers through a table of `MdHash`
(`Impl/RsaPss/X86/Table.lean`) set before the call, and it keeps every other
register. It is the function 4 of a table of `MdHash`
(`Spec/MdHashTable.lean`), whose callers compress a message themselves and
take its digest from the hash value after its last block.
-/

@[expose] public section

namespace VG.Impl.MdHashTable.X86

open VG.X86

/-- `digest(value = ebx, out = eax)`. -/
def digest (out : List Instr) : Prog isa := .block out

end VG.Impl.MdHashTable.X86
