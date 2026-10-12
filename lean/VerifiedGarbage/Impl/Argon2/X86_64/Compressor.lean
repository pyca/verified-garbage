module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# The compression function the derivation calls

The derivation calls an implementation of G (`vg_argon2_compress` or one of
its variants, e.g. `vg_argon2_compress_avx2`): its name and code. The code
that calls it takes it as an instance argument, so that the derivation is
written, and proven, once for every implementation.
-/

@[expose] public section

namespace VG.Impl.Argon2.X86_64

open VG.X86_64

/-- The implementation of G that the derivation calls. -/
class Compressor where
  /-- Its name, which the emitted call refers to. -/
  name : String
  /-- Its code, which the model runs for the call. -/
  code : Prog isa

end VG.Impl.Argon2.X86_64
