module

public import VerifiedGarbage.Impl.Sm4Gcm.X86
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# SM4-GCM on x86 (32-bit): the functions as emitted

Each function of `Impl/Sm4Gcm/X86.lean`, in its frame of working space
(`withStackScratch`), and then its cleanup (`Impl.Scrub.X86.scrubAll rb W`):
the `W` bytes of stack below `esp` that it and its callees use (its
contract's stack: that frame, and the frames of its calls of
`vg_sm4_ctr32`, `vg_sm4_expand_key_core` and `vg_ghash`) zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. `init` takes the implementations of
the key schedule and of `vg_sm4_ctr32` it calls, and the others those of
`vg_ghash` (`Callees`) and of `vg_sm4_ctr32`, so that each is emitted with
each variant. `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad` are
AES-GCM's as emitted (`Impl.AesGcm.X86.Fn`).
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.X86.Fn

open VG.X86
open Impl.StackScratch.X86 (withStackScratch)
open Impl.AesGcm.X86 (Callees)

-- Qualified: inside `Fn`, a bare `init` is the `Fn.init` being defined.

/-- `vg_sm4_gcm_init`, as emitted, calling the implementations `k` of the
key schedule and `t` of `vg_sm4_ctr32`. -/
def init (k t : Impl.AesGcm.X86.Fn) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 4112 (withStackScratch 2576 2 (Impl.Sm4Gcm.X86.init k t))

variable (c : Callees) (t : Impl.AesGcm.X86.Fn)

/-- `vg_sm4_gcm_stream_encrypt`, as emitted. -/
def streamEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 4136 (withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamEncrypt c t))

/-- `vg_sm4_gcm_stream_decrypt`, as emitted. -/
def streamDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 4136 (withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamDecrypt c t))

/-- `vg_sm4_gcm_stream_finish`, as emitted. -/
def streamFinish : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 4132 (withStackScratch 2596 7 (Impl.Sm4Gcm.X86.streamFinish c t))

/-- `vg_sm4_gcm_stream_verify`, as emitted. -/
def streamVerify : Prog isa :=
  Impl.Scrub.X86.scrubAll 32 4136 (withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamVerify c t))

/-- `vg_sm4_gcm_seal`, as emitted. -/
def «seal» : Prog isa := Impl.Scrub.X86.scrubAll 0 4136 (withStackScratch 2600 8 (Impl.Sm4Gcm.X86.«seal» c t))

/-- `vg_sm4_gcm_open`, as emitted. -/
def «open» : Prog isa := Impl.Scrub.X86.scrubAll 32 4140 (withStackScratch 2604 9 (Impl.Sm4Gcm.X86.«open» c t))

end VG.Impl.Sm4Gcm.X86.Fn
