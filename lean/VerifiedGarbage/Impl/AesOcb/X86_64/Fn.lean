module

public import VerifiedGarbage.Impl.AesOcb.X86_64
public import VerifiedGarbage.Impl.AesOcb.X86_64AesNi
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-OCB on x86-64: the functions as emitted

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open` over the AES
functions `c`, or in AES-NI registers in one pass, each in a frame of its
working space, then its cleanup (`Impl.Scrub.X86_64.scrubAll v 0 n`): every
vector register at the level `v` and every caller-saved register cleared,
and its whole frame wiped.
-/

@[expose] public section

namespace VG.Impl.AesOcb.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

/-- `vg_aes_ocb_init` over `c`, in a frame of only the bytes it writes itself
when `c`'s encryption and key expansion need no working space (`free`). -/
def init (v : VecLevel) (free : Bool) (c : Callees) : Prog isa :=
  if free then scrubAll v 0 40 (withStackScratch 32 .rcx (X86_64.init c))
  else scrubAll v 0 2576 (withStackScratch 2568 .rcx (X86_64.init c))

/-- `vg_aes_ocb_seal` over `c`, as emitted. -/
def «seal» (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 0 3640 (withStackArgScratch 3632 4 (X86_64.«seal» c))

/-- `vg_aes_ocb_open` over `c`, as emitted. -/
def «open» (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 32 3640 (withStackArgScratch 3632 4 (X86_64.open c))

/-- `vg_aes_ocb_seal_aesni`, as emitted. -/
def sealOnePass (v : VecLevel) : Prog isa := scrubAll v 0 696 (withStackArgScratch 688 4 X86_64AesNi.«seal»)

/-- `vg_aes_ocb_open_aesni`, as emitted. -/
def openOnePass (v : VecLevel) : Prog isa := scrubAll v 32 904 (withStackArgScratch 896 4 X86_64AesNi.open)

end VG.Impl.AesOcb.X86_64.Fn
