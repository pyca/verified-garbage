module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Impls

/-! # The implementations of `SlhDsaThash4` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.SlhDsaThash4.X86_64

open VG.Proof.SlhDsa.X86_64

/-- Every implementation for outputs of 16 bytes, best first: each function
generic over them is emitted with each (the registration files that import
this), and its dispatcher tries them in this order. -/
def variants16 : List (Thash4Impl 16) := [avx512vl_16, avx2_16, base16]

/-- For outputs of 24 bytes, best first. -/
def variants24 : List (Thash4Impl 24) := [avx512vl_24, avx2_24, base24]

/-- For outputs of 32 bytes, best first. -/
def variants32 : List (Thash4Impl 32) := [avx512vl_32, avx2_32, base32]

end VG.Proof.Variants.SlhDsaThash4.X86_64
