module

public import VerifiedGarbage.Impl.Argon2.X86_64.RandomSource
public import VerifiedGarbage.Impl.Argon2.X86_64.FillKernel

/-! Select the random word and update one active matrix cell. -/

@[expose] public section

namespace VG.Impl.Argon2.X86_64.FillBlock

variable [Compressor]

open VG.X86_64

def code : Prog isa := .seq RandomSource.code FillKernel.code

end VG.Impl.Argon2.X86_64.FillBlock
