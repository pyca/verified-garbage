module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Impl.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Impl.MlKem1024.X86_64.CheckEkAvx2

/-! # ML-KEM on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and the `n` bytes of stack its frames use zeroed.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `Spec.MlKem.checkEkApi`'s function as emitted. -/
def checkEk : Prog isa := scrubAll .sse 32 0 Impl.MlKem.X86_64.checkEk

/-- `Spec.MlKem.checkEkApi`'s function with AVX2 as emitted. -/
def checkEkAvx2 : Prog isa := scrubAll .avx 32 0 Impl.MlKem.X86_64.checkEkAvx2

/-- `Spec.MlKem1024.checkEkApi`'s function as emitted. -/
def checkEk1024 : Prog isa := scrubAll .sse 32 0 Impl.MlKem1024.X86_64.checkEk1024

/-- `Spec.MlKem1024.checkEkApi`'s function with AVX2 as emitted. -/
def checkEk1024Avx2 : Prog isa := scrubAll .avx 32 0 Impl.MlKem1024.X86_64.checkEk1024Avx2

end VG.Impl.MlKem.X86_64.Fn
