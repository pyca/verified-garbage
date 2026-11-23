module

public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Impl.Aes.AArch64.Callee
public import VerifiedGarbage.Impl.Gcm.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.Sha3.AArch64.ViaD8

/-!
# AES-GCM on AArch64: the functions as emitted

Each function is its code in a frame that holds its working space, then its
cleanup (`Impl.Scrub.AArch64.scrubAll`): the registers it writes that the
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
open VG.Impl.Scrub.AArch64 (Clear scrubAll allGprs allVecs)
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

/-! ## Calling the implementations by the addresses in d8, d9 and d10

The functions of the implementations without PMULL are the same code for each
of them but for the functions they call: `vg_ghash`'s implementation, whose
address is in `d8`, `vg_aes_ctr32`'s, in `d9`, and its out-of-place form's,
in `d10`. Each is then the code it was, made to call those by their addresses
(`Code.viaDAt`), in a function named for it alone (`…_core`), called by an
entry that puts the addresses there (`entryDS`); its cleanup also clears
the high halves of the registers the entry writes the low halves of
(`clearDL`). -/

/-- The implementation of `vg_ghash` and the register of its address. -/
def ghR (v : Calls) : String × VReg := (v.gh.name, .v8)

/-- The implementation of `vg_aes_ctr32` and the register of its address. -/
def ctrR (v : Calls) : String × VReg := (v.ctr.name, .v9)

/-- The out-of-place form of `vg_aes_ctr32` and the register of its address. -/
def toR (v : Calls) : String × VReg := (v.ctrTo.name, .v10)

/-- The function named `core`, whose code is `F`, with `k` stack words, made
to call the functions `L` names by the registers it pairs them with, called
with their addresses there, then the cleanup over `W` bytes of stack and the
entry's frame, for a result of `rb` bits. -/
def viaDS (L : List (String × VReg)) (W : Nat) (core : String) (rb k : Nat) (F : Prog isa) : Prog isa :=
  scrubAll (W + Impl.Sha3.AArch64.frameDS k L.length) rb (Impl.Sha3.AArch64.clearDL L)
    (Impl.Sha3.AArch64.entryDS L core k (Impl.Sha3.AArch64.Code.viaDAt L F))

/-- `vg_aes_gcm_init`, by `d9`. -/
def initDS (v : Calls) : Prog isa :=
  viaDS [ctrR v] v.initWn "vg_aes_gcm_init_core" 0 0
    (withStackScratch v.initWn .x3 (AesGcm.AArch64.init v.callees))

/-- `vg_aes_gcm_stream_init`, by `d8`. -/
def streamInitDS (v : Calls) : Prog isa :=
  viaDS [ghR v] v.wn "vg_aes_gcm_stream_init_core" 0 0
    (withStackScratch v.wn .x4 (AesGcm.AArch64.streamInit v.callees))

/-- `vg_aes_gcm_stream_aad`, by `d8`. -/
def streamAadDS (v : Calls) : Prog isa :=
  viaDS [ghR v] v.wn "vg_aes_gcm_stream_aad_core" 0 0
    (withStackScratch v.wn .x5 (AesGcm.AArch64.streamAad v.callees))

/-- `vg_aes_gcm_stream_encrypt`, by `d8` and `d9`. -/
def streamEncryptDS (v : Calls) : Prog isa :=
  viaDS [ghR v, ctrR v] v.wn "vg_aes_gcm_stream_encrypt_core" 0 0
    (withStackScratch v.wn .x7 (AesGcm.AArch64.streamEncrypt v.callees))

/-- `vg_aes_gcm_stream_decrypt`, by `d8` and `d9`. -/
def streamDecryptDS (v : Calls) : Prog isa :=
  viaDS [ghR v, ctrR v] v.wn "vg_aes_gcm_stream_decrypt_core" 0 0
    (withStackScratch v.wn .x7 (AesGcm.AArch64.streamDecrypt v.callees))

/-- `vg_aes_gcm_stream_finish`, by `d8` and `d9`. -/
def streamFinishDS (v : Calls) : Prog isa :=
  viaDS [ghR v, ctrR v] v.wn "vg_aes_gcm_stream_finish_core" 0 0
    (withStackScratch v.wn .x6 (AesGcm.AArch64.streamFinish v.callees))

/-- `vg_aes_gcm_stream_verify`, which returns 32 bits, by `d8` and `d9`. -/
def streamVerifyDS (v : Calls) : Prog isa :=
  viaDS [ghR v, ctrR v] v.wn "vg_aes_gcm_stream_verify_core" 32 0
    (withStackScratch v.wn .x7 (AesGcm.AArch64.streamVerify v.callees))

/-- `vg_aes_gcm_seal_with_powers` of implementations without code that reads
the powers, by `d8` and `d9`: its one stack argument copied by the entry,
then by `withStackArgScratch`. -/
def sealWithPowersBaseDS (v : Calls) : Prog isa :=
  viaDS [ghR v, ctrR v] 2576 "vg_aes_gcm_seal_with_powers_core" 0 1
    (withStackArgScratch 2576 1 (sealCode v))

/-- `vg_aes_gcm_open_with_powers` of those implementations, by `d8` and `d9`,
as `sealWithPowersBaseDS`. -/
def openWithPowersBaseDS (v : Calls) : Prog isa :=
  viaDS [ghR v, ctrR v] 2592 "vg_aes_gcm_open_with_powers_core" 32 2
    (withStackArgScratch 2592 2 (openCode v))

/-- `vg_aes_gcm_open_to_with_powers` of those implementations, by `d8`, `d9`
and `d10`, as `sealWithPowersBaseDS`. -/
def openToWithPowersBaseDS (v : Calls) : Prog isa :=
  viaDS [ghR v, ctrR v, toR v] 2608 "vg_aes_gcm_open_to_with_powers_core" 32 4
    (withStackArgScratch 2608 4 (openToCode v))

end Fn

end VG.Impl.AesGcm.AArch64
