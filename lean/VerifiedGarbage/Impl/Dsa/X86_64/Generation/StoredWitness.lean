module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ForceWitness
public import VerifiedGarbage.Impl.Bignum.X86_64

/-! # Transform a witness buffer while retaining the primality workspace base -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- Force the witness at header word `ptr`, of the length in header word `len`. -/
def forceStoredWitness (ptr len : Nat) : Prog isa := seqs [
  .block [.mov .rbx (.reg .rdi), .mov .rcx (.mem (hdr len)), .mov .rdi (.mem (hdr ptr))],
  .block forceWitness,
  .block [.mov .rdi (.reg .rbx)]]

end VG.Impl.Dsa.X86_64.Generation
