module

public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
public import VerifiedGarbage.Impl.Aes.AArch64.Callee
public import VerifiedGarbage.Impl.Gcm.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# AES-GCM on AArch64: the functions as emitted

Each function is its code in a frame that holds its working space, then its
cleanup (`Impl.Residue.AArch64.scrubAll`): the registers it writes that the
calling convention does not preserve are cleared, and the stack it uses is
zeroed, so that it returns without secret residue
(`Proof/AesGcm/AArch64/GhashImpls.lean`).

The functions are generic over the implementations they call (`Calls`): of
`vg_aes_ctr32`, of its out-of-place form, of `vg_aes_expand_key_scratch` and
of `vg_ghash`. Their frames are sized to the working space the implementation
of `vg_aes_ctr32` needs (`Calls.wn`, `Calls.initWn`, `Calls.pwWn`). The
cleanup clears every register the calling convention does not preserve but
the high halves of v8–v15 (`own`), which neither the functions' own
instructions nor the implementations write.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64

open VG.AArch64
open VG.Impl.Residue.AArch64 (Clear scrubAll allGprs allVecs)
open VG.Impl.StackScratch.AArch64 (withStackScratch withStackArgScratch)

/-- What the functions of a variant of AES-GCM call, and what chooses their
code. -/
structure Calls where
  /-- The implementation of `vg_aes_ctr32`. -/
  ctr : Impl.Aes.AArch64.Ctr32
  /-- Its out-of-place form, which `vg_aes_gcm_open_to` calls. -/
  ctrTo : Impl.Aes.AArch64.Ctr32
  /-- The implementation of `vg_aes_expand_key_scratch`. -/
  key : Fn
  /-- The implementation of `vg_ghash`. -/
  gh : Fn
  /-- Whether `gh` is the implementation with PMULL: `seal`, `open` and
  `open_to` then have the path for the records of TLS (`Fast.lean`). -/
  pmull : Bool
  /-- Whether the `*_with_powers` functions take those records with the loops
  that interleave counter mode and GHASH (`Stitch.lean`). -/
  stitch : Bool
  /-- What the functions' names end with. -/
  suffix : String

namespace Calls

variable (v : Calls)

/-- The implementations, as the code takes them. -/
def callees : Callees :=
  ⟨⟨v.ctr.name, v.ctr.code⟩, v.key, v.gh, ⟨v.ctrTo.name, v.ctrTo.code⟩⟩

/-- The bytes of working space of the functions: 768 over an implementation
of counter mode that needs none, else 2560. -/
def wn : Nat := if v.ctr.scratch = 0 then 768 else 2560

/-- The bytes of working space of `vg_aes_gcm_init`, as `wn`. -/
def initWn : Nat := if v.ctr.scratch = 0 then 1024 else 2560

/-- The bytes of working space of the `*_with_powers` functions: 1024 with
the interleaved loops over an implementation of counter mode that needs no
working space, else `wn`. -/
def pwWn : Nat := if v.stitch = true ∧ v.ctr.scratch = 0 then 1024 else v.wn

end Calls

namespace Fn

/-- The registers the cleanup of each function clears: every general-purpose
and vector register the calling convention does not preserve, and no high
half of v8–v15. -/
def own : Clear := ⟨allGprs, allVecs, []⟩

/-- `vg_aes_gcm_seal`'s code: with the path for the records of TLS where
PMULL is there. -/
def sealCode (v : Calls) : Prog isa :=
  if v.pmull then Fast.«seal» v.callees else AesGcm.AArch64.«seal» v.callees

/-- `vg_aes_gcm_open`'s code, as `sealCode`. -/
def openCode (v : Calls) : Prog isa :=
  if v.pmull then Fast.«open» v.callees else AesGcm.AArch64.«open» v.callees

/-- `vg_aes_gcm_open_to`'s code, as `sealCode`. -/
def openToCode (v : Calls) : Prog isa :=
  if v.pmull then Fast.openTo v.callees else openG v.callees true 4

/-- `vg_aes_gcm_seal_with_powers`'s code, calling `w`, an implementation of
`vg_ghash_with_powers`: with the interleaved loops if `v.stitch`. -/
def sealPwCode (v : Calls) (w : AesGcm.AArch64.Fn) : Prog isa :=
  if v.stitch then Stitch.sealWithPw v.callees w else Fast.sealWithPw v.callees w

/-- `vg_aes_gcm_open_with_powers`'s code, as `sealPwCode`. -/
def openPwCode (v : Calls) (w : AesGcm.AArch64.Fn) : Prog isa :=
  if v.stitch then Stitch.openWithPw v.callees w else Fast.openWithPw v.callees w

/-- `vg_aes_gcm_open_to_with_powers`'s code, as `sealPwCode`. -/
def openToPwCode (v : Calls) (w : AesGcm.AArch64.Fn) : Prog isa :=
  if v.stitch then Stitch.openToWithPw v.callees w else Fast.openToWithPw v.callees w

/-- `vg_aes_gcm_stream_init`. -/
def streamInit (v : Calls) : Prog isa :=
  scrubAll v.wn 0 own (withStackScratch v.wn .x4 (AesGcm.AArch64.streamInit v.callees))

/-- `vg_aes_gcm_stream_aad`. -/
def streamAad (v : Calls) : Prog isa :=
  scrubAll v.wn 0 own (withStackScratch v.wn .x5 (AesGcm.AArch64.streamAad v.callees))

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncrypt (v : Calls) : Prog isa :=
  scrubAll v.wn 0 own (withStackScratch v.wn .x7 (AesGcm.AArch64.streamEncrypt v.callees))

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecrypt (v : Calls) : Prog isa :=
  scrubAll v.wn 0 own (withStackScratch v.wn .x7 (AesGcm.AArch64.streamDecrypt v.callees))

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinish (v : Calls) : Prog isa :=
  scrubAll v.wn 0 own (withStackScratch v.wn .x6 (AesGcm.AArch64.streamFinish v.callees))

/-- `vg_aes_gcm_stream_verify`, which returns 32 bits. -/
def streamVerify (v : Calls) : Prog isa :=
  scrubAll v.wn 32 own (withStackScratch v.wn .x7 (AesGcm.AArch64.streamVerify v.callees))

/-- `vg_aes_gcm_seal`: its working space after a copy of its stack argument. -/
def «seal» (v : Calls) : Prog isa :=
  scrubAll (v.wn + 16) 0 own (withStackArgScratch (v.wn + 16) 1 (sealCode v))

/-- `vg_aes_gcm_init`. -/
def init (v : Calls) : Prog isa :=
  scrubAll v.initWn 0 own (withStackScratch v.initWn .x3 (AesGcm.AArch64.init v.callees))

/-- `vg_aes_gcm_open`, which returns 32 bits: its working space after copies
of its two stack arguments. -/
def «open» (v : Calls) : Prog isa :=
  scrubAll (v.wn + 32) 32 own (withStackArgScratch (v.wn + 32) 2 (openCode v))

/-- `vg_aes_gcm_open_to`, as `open`, with four stack arguments. -/
def openTo (v : Calls) : Prog isa :=
  scrubAll (v.wn + 48) 32 own (withStackArgScratch (v.wn + 48) 4 (openToCode v))

/-- `vg_aes_gcm_seal_gather`, calling `seal`, the instance of
`vg_aes_gcm_seal` of the same variant. -/
def sealGather (v : Calls) : Prog isa :=
  scrubAll 2592 0 own (SealGather.sealGather ⟨"vg_aes_gcm_seal" ++ v.suffix, «seal» v⟩)

/-- `vg_aes_gcm_seal_with_powers`, calling `w`. -/
def sealWithPowers (v : Calls) (w : AesGcm.AArch64.Fn) : Prog isa :=
  scrubAll (v.pwWn + 32) 0 own (withStackArgScratch (v.pwWn + 32) 2 (sealPwCode v w))

/-- `vg_aes_gcm_open_with_powers`, calling `w`. -/
def openWithPowers (v : Calls) (w : AesGcm.AArch64.Fn) : Prog isa :=
  scrubAll (v.pwWn + 32) 32 own (withStackArgScratch (v.pwWn + 32) 3 (openPwCode v w))

/-- `vg_aes_gcm_open_to_with_powers`, calling `w`. -/
def openToWithPowers (v : Calls) (w : AesGcm.AArch64.Fn) : Prog isa :=
  scrubAll (v.pwWn + 48) 32 own (withStackArgScratch (v.pwWn + 48) 5 (openToPwCode v w))

/-- `vg_aes_gcm_seal_with_powers` of implementations without code that reads
the powers: `seal`'s code, in the frame of 2576 bytes its contract states. -/
def sealWithPowersBase (v : Calls) : Prog isa :=
  scrubAll 2576 0 own (withStackArgScratch 2576 1 (sealCode v))

/-- `vg_aes_gcm_open_with_powers` of those implementations, as
`sealWithPowersBase`. -/
def openWithPowersBase (v : Calls) : Prog isa :=
  scrubAll 2592 32 own (withStackArgScratch 2592 2 (openCode v))

/-- `vg_aes_gcm_open_to_with_powers` of those implementations, as
`sealWithPowersBase`. -/
def openToWithPowersBase (v : Calls) : Prog isa :=
  scrubAll 2608 32 own (withStackArgScratch 2608 4 (openToCode v))

/-- `vg_aes_gcm_store_powers` in the baseline ISA: `Impl.Gcm.AArch64.keyPowers`
with its working space in its frame. -/
def storePowers : Prog isa :=
  scrubAll 80 0 own (withStackScratch 80 .x2 Impl.Gcm.AArch64.keyPowers)

end Fn

end VG.Impl.AesGcm.AArch64
