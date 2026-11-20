module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Impl.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Impl.MlKem1024.X86_64.CheckEkAvx2
public import VerifiedGarbage.Impl.MlKem.X86_64.Wipe

/-! # ML-KEM on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and the `n` bytes of stack its frames use zeroed.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.MlKem.checkEkApi`'s function as emitted. -/
def checkEk : Prog isa := scrubAll .sse 32 0 Impl.MlKem.X86_64.checkEk

/-- `Spec.MlKem.checkEkApi`'s function with AVX2 as emitted. -/
def checkEkAvx2 : Prog isa := scrubAll .avx 32 0 Impl.MlKem.X86_64.checkEkAvx2

/-- `Spec.MlKem1024.checkEkApi`'s function as emitted. -/
def checkEk1024 : Prog isa := scrubAll .sse 32 0 Impl.MlKem1024.X86_64.checkEk1024

/-- `Spec.MlKem1024.checkEkApi`'s function with AVX2 as emitted. -/
def checkEk1024Avx2 : Prog isa := scrubAll .avx 32 0 Impl.MlKem1024.X86_64.checkEk1024Avx2

/-- `vg_mlkem768_keygen` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def keyGen (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.keyGenW c sfx zname zcode)

/-- `vg_mlkem768_encaps_h` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def encapsH (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.encapsHW c sfx zname zcode)

/-- `vg_mlkem768_encaps` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def encaps (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.encapsW c sfx zname zcode)

/-- `vg_mlkem768_decaps` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def decaps (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.decapsW c sfx zname zcode)

/-- `vg_mlkem1024_keygen` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def keyGen1024 (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.keyGen1024W c sfx zname zcode)

/-- `vg_mlkem1024_encaps_h` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def encapsH1024 (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.encapsH1024W c sfx zname zcode)

/-- `vg_mlkem1024_encaps` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def encaps1024 (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.encaps1024W c sfx zname zcode)

/-- `vg_mlkem1024_decaps` as emitted, over the implementation `c` of `vg_mlkem_sample_ntt4`
(its names ending with `sfx`) and the zeroize function `zcode` named
`zname`, its cleanup at the level `v`. -/
def decaps1024 (v : VecLevel) (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  scrubAll v 32 56 (Impl.MlKem.X86_64.decaps1024W c sfx zname zcode)

end VG.Impl.MlKem.X86_64.Fn
