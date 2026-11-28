module

-- separate module: the literals of every `thash4`, which the checks of its implementations' records evaluate

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4Base
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4Base
meta import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SLH-DSA on x86-64: the code of each `thash4`, as literals

The code of each implementation of `thash4` (`Thash4Impls.lean`), a
definition of its own, as a literal (`materialize_code`), which the checks
of what the cleanup of its callers needs (`calleeSide`) read.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Thash4Lit

open VG.X86_64

def base16 : Prog isa := Impl.SlhDsa.X86_64.Thash4Base.thash4 16
def base24 : Prog isa := Impl.SlhDsa.X86_64.Thash4Base.thash4 24
def base32 : Prog isa := Impl.SlhDsa.X86_64.Thash4Base.thash4 32
def avx2_16 : Prog isa := Impl.SlhDsa.X86_64.Thash4.thash4 16 false
def avx2_24 : Prog isa := Impl.SlhDsa.X86_64.Thash4.thash4 24 false
def avx2_32 : Prog isa := Impl.SlhDsa.X86_64.Thash4.thash4 32 false
def avx512vl_16 : Prog isa := Impl.SlhDsa.X86_64.Thash4.thash4 16 true
def avx512vl_24 : Prog isa := Impl.SlhDsa.X86_64.Thash4.thash4 24 true
def avx512vl_32 : Prog isa := Impl.SlhDsa.X86_64.Thash4.thash4 32 true

materialize_code base16
materialize_code base24
materialize_code base32
materialize_code avx2_16
materialize_code avx2_24
materialize_code avx2_32
materialize_code avx512vl_16
materialize_code avx512vl_24
materialize_code avx512vl_32

end VG.Proof.SlhDsa.X86_64.Thash4Lit
