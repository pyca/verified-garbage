module

public import VerifiedGarbage.Impl.AesGcm.X86.SealGather
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# AES-GCM on x86 (32-bit): the functions as emitted

Each function of `Impl/AesGcm/X86.lean`, in its frame of working space
(`withStackScratch`), and then its cleanup (`Impl.Scrub.X86.scrubF rb W`):
the `W` bytes of stack below `esp` that it and its callees use (its
contract's stack) zeroed, and the registers a callee may change cleared but
the `rb` bits of the result, so that it returns without secret residue.
They take the implementations they call (`Callees`, and for `open_to` its
`vg_aes_ctr32_to`), so that each is emitted with each variant.

`vg_aes_gcm_seal_gather` calls `vg_aes_gcm_seal`'s code without the cleanup,
as the internal function `vg_aes_gcm_seal<suffix>_core`: its own cleanup
zeroes the stack of that call too.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86.Fn

open VG.X86
open Impl.StackScratch.X86 (withStackScratch)

variable (c : Callees)

-- Qualified: inside `Fn`, a bare `init` is the `Fn.init` being defined.

/-- `vg_aes_gcm_init`, as emitted. -/
def init : Prog isa := Impl.Scrub.X86.scrubF 0 2612 (withStackScratch 2580 3 (Impl.AesGcm.X86.init c))

/-- `vg_aes_gcm_stream_init`, as emitted. -/
def streamInit : Prog isa :=
  Impl.Scrub.X86.scrubF 0 2608 (withStackScratch 2584 4 (Impl.AesGcm.X86.streamInit c))

/-- `vg_aes_gcm_stream_aad`, as emitted. -/
def streamAad : Prog isa :=
  Impl.Scrub.X86.scrubF 0 2616 (withStackScratch 2592 6 (Impl.AesGcm.X86.streamAad c))

/-- `vg_aes_gcm_stream_encrypt`, as emitted. -/
def streamEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubF 0 2636 (withStackScratch 2604 9 (Impl.AesGcm.X86.streamEncrypt c))

/-- `vg_aes_gcm_stream_decrypt`, as emitted. -/
def streamDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubF 0 2636 (withStackScratch 2604 9 (Impl.AesGcm.X86.streamDecrypt c))

/-- `vg_aes_gcm_stream_finish`, as emitted. -/
def streamFinish : Prog isa :=
  Impl.Scrub.X86.scrubF 0 2632 (withStackScratch 2600 8 (Impl.AesGcm.X86.streamFinish c))

/-- `vg_aes_gcm_stream_verify`, as emitted. -/
def streamVerify : Prog isa :=
  Impl.Scrub.X86.scrubF 32 2636 (withStackScratch 2604 9 (Impl.AesGcm.X86.streamVerify c))

/-- `vg_aes_gcm_seal`, as emitted. -/
def «seal» : Prog isa := Impl.Scrub.X86.scrubF 0 2636 (withStackScratch 2604 9 (Impl.AesGcm.X86.«seal» c))

/-- `vg_aes_gcm_open`, as emitted. -/
def «open» : Prog isa := Impl.Scrub.X86.scrubF 32 2640 (withStackScratch 2608 10 (Impl.AesGcm.X86.«open» c))

/-- `vg_aes_gcm_open_to`, calling `vg_aes_ctr32_to` (`f`) for its whole
blocks, as emitted. -/
def openTo (f : Impl.AesGcm.X86.Fn) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 2696 (withStackScratch 2616 12 (Impl.AesGcm.X86.Open.openTo c f))

/-- `vg_aes_gcm_seal_gather` of the variant whose names end with `sfx`,
calling `vg_aes_gcm_seal`'s code, unscrubbed, as `vg_aes_gcm_seal<sfx>_core`,
as emitted. -/
def sealGather (sfx : String) : Prog isa :=
  Impl.Scrub.X86.scrubF 0 2688 (Impl.AesGcm.X86.SealGather.sealGather ("vg_aes_gcm_seal" ++ sfx ++ "_core")
    (withStackScratch 2604 9 (Impl.AesGcm.X86.«seal» c)))

end VG.Impl.AesGcm.X86.Fn
