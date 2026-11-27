module

public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fn

/-!
# AES-GCM-SIV on AArch64: the functions as emitted

Each function is its code in a frame that holds its working space, then its
cleanup (`Impl.Scrub.AArch64.scrubAll`): the registers it writes that the
calling convention does not preserve are cleared, and the stack it uses is
zeroed, so that it returns without secret residue
(`Proof/AesGcmSiv/AArch64/Stitch/Verified.lean`).

The functions are generic over the implementations they call, as AES-GCM's
(`Impl.AesGcm.AArch64.Calls`), and their cleanup clears the same registers
(`Impl.AesGcm.AArch64.Fn.own`).
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.AArch64.Fn

open VG.AArch64
open VG.Impl.AesGcm.AArch64 (Calls)
open VG.Impl.AesGcm.AArch64.Fn (own)
open VG.Impl.Scrub.AArch64 (scrubAll)
open VG.Impl.StackScratch.AArch64 (withStackArgScratch)

/-- The bytes of working space of the functions: what they use themselves,
then what the implementations need, key expansion's 512 bytes over an
implementation of counter mode that needs none, else counter mode's 2048. -/
def wn (v : Calls) : Nat := if v.ctr.scratch = 0 then 2272 else 3808

/-- `vg_aes_gcm_siv_seal`'s code: with the loops that interleave counter mode
and POLYVAL where PMULL is there, with `eor3` if `v.stitch`. -/
def sealCode (v : Calls) : Prog isa :=
  if v.pmull then Stitch.«seal» v.stitch v.callees else AesGcmSiv.AArch64.«seal» v.callees

/-- `vg_aes_gcm_siv_open`'s code, as `sealCode`. -/
def openCode (v : Calls) : Prog isa :=
  if v.pmull then Stitch.«open» v.stitch v.callees else AesGcmSiv.AArch64.«open» v.callees

/-- `vg_aes_gcm_siv_seal`: its working space after a copy of its stack
argument. -/
def «seal» (v : Calls) : Prog isa :=
  scrubAll (wn v + 16) 0 own (withStackArgScratch (wn v + 16) 0 (sealCode v))

/-- `vg_aes_gcm_siv_open`, which returns 32 bits, as `seal`. -/
def «open» (v : Calls) : Prog isa :=
  scrubAll (wn v + 16) 32 own (withStackArgScratch (wn v + 16) 0 (openCode v))

end VG.Impl.AesGcmSiv.AArch64.Fn
