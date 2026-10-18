module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ForceWitness
public import VerifiedGarbage.Impl.Rsa.X86_64

/-! # Transform a witness buffer while retaining the primality workspace base -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

def forceStoredWitness (ptr len : Nat) : Prog isa := seqs [
  .block [.mov .rbx (.reg .rdi), .mov .rdi (.mem (hdr ptr))],
  .block (forceWitness len),
  .block [.mov .rdi (.reg .rbx)]]

end VG.Impl.Dsa.X86_64.Generation
