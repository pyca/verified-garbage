module

public import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-! # Load a DSA candidate or witness, clearing padded limbs -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

def loadPadded (a ptr len : Nat) : Prog isa := seqs [
  Rsa.X86_64.Crt.zeroArr a,
  .block [.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len)),
    .mov .rbx (.mem (hdr (sArr a)))],
  loadBE]

end VG.Impl.Dsa.X86_64.Generation
