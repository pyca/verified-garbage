module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Impl.AesGcmSiv.X86
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Impl.AesGcmSiv.X86
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

-- separate module: it evaluates AES-GCM-SIV's code with stubs, without the
-- GHASH field algebra that `Frame.lean`, its one importer, imports.

/-!
# What the cleanup of AES-GCM-SIV needs of its code (x86, 32-bit)

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are generic over the
implementations of `vg_aes_ctr32_to`, `vg_aes_expand_key` and `vg_ghash`
they call (`GcmImpl`, `Proof/Variants/AesGcm/X86.lean`). What the
cleanup needs of their code over the 2888 bytes of stack of their contracts
(`X86.Scrub.scrubFSide`, for `verifiedScrubbedAll`) holds of every
implementation (`seal_scrub`, `open_scrub`): from their code with stub implementations, whose code is
`.block []`, which the kernel evaluates here (`seal_side`, …), the
implementations' own facts (`Ctr32Impl.scrub`, `expandScrub`,
`GhashImpl.scrub`, their stacks), and `Fill`, which `fill_calls` proves of
any implementation by walking only AES-GCM-SIV's code. The code chooses
its blocks by the name of AES (`hardware`) and its byte reversal by that of
GHASH (`shuffles`), so there is a stub for each of the four choices.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Impl.AesGcmSiv.X86
open Impl.StackScratch.X86 (withStackScratch)
open Proof.AesGcm.X86 (GcmImpl)

/-- Implementations with no code, by the names that choose AES-NI's blocks
(`ni`) and the copies with `pshufb` (`pc`). -/
def stub (ni pc : Bool) : Impl.AesGcm.X86.Callees :=
  ⟨⟨if ni then "vg_aes_ctr32_to_aesni" else "", .block []⟩, ⟨"", .block []⟩,
    ⟨if pc then "vg_ghash_pclmul" else "", .block []⟩⟩

-- AES-GCM-SIV's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code sealStub := withStackScratch 2856 8 («seal» (stub false false))
materialize_code sealStubNi := withStackScratch 2856 8 («seal» (stub true false))
materialize_code sealStubPc := withStackScratch 2856 8 («seal» (stub false true))
materialize_code sealStubNiPc := withStackScratch 2856 8 («seal» (stub true true))
materialize_code openStub := withStackScratch 2856 8 («open» (stub false false))
materialize_code openStubNi := withStackScratch 2856 8 («open» (stub true false))
materialize_code openStubPc := withStackScratch 2856 8 («open» (stub false true))
materialize_code openStubNiPc := withStackScratch 2856 8 («open» (stub true true))

theorem seal_side : scrubFSide (withStackScratch 2856 8 («seal» (stub false false))) [] 2888 = true := by
  lit_decide

theorem sealNi_side : scrubFSide (withStackScratch 2856 8 («seal» (stub true false))) [] 2888 = true := by
  lit_decide

theorem sealPc_side : scrubFSide (withStackScratch 2856 8 («seal» (stub false true))) [] 2888 = true := by
  lit_decide

theorem sealNiPc_side : scrubFSide (withStackScratch 2856 8 («seal» (stub true true))) [] 2888 = true := by
  lit_decide

theorem open_side : scrubFSide (withStackScratch 2856 8 («open» (stub false false))) [] 2888 = true := by
  lit_decide

theorem openNi_side : scrubFSide (withStackScratch 2856 8 («open» (stub true false))) [] 2888 = true := by
  lit_decide

theorem openPc_side : scrubFSide (withStackScratch 2856 8 («open» (stub false true))) [] 2888 = true := by
  lit_decide

theorem openNiPc_side : scrubFSide (withStackScratch 2856 8 («open» (stub true true))) [] 2888 = true := by
  lit_decide

/-- `scrubFSide` of `vg_aes_gcm_siv_seal`, whatever the implementations. -/
theorem seal_scrub (v : GcmImpl) :
    scrubFSide (withStackScratch 2856 8 («seal» v.callees)) [] 2888 = true := by
  have hc : calleeSide v.ctr.callee.code 0 = true := calleeSide_of_eq v.ctr.stack v.ctr.scrub
  have hk : calleeSide v.ctr.expand.code 0 = true := calleeSide_of_eq v.ctr.expandStack v.ctr.expandScrub
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  by_cases h1 : hardware v.callees = true <;> by_cases h2 : shuffles v.callees = true
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) sealNiPc_side
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) sealNi_side
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) sealPc_side
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) seal_side

/-- `scrubFSide` of `vg_aes_gcm_siv_open`, whatever the implementations. -/
theorem open_scrub (v : GcmImpl) :
    scrubFSide (withStackScratch 2856 8 («open» v.callees)) [] 2888 = true := by
  have hc : calleeSide v.ctr.callee.code 0 = true := calleeSide_of_eq v.ctr.stack v.ctr.scrub
  have hk : calleeSide v.ctr.expand.code 0 = true := calleeSide_of_eq v.ctr.expandStack v.ctr.expandScrub
  have hg : calleeSide v.gh.fn.code 0 = true := calleeSide_of_eq v.gh.stack v.gh.scrub
  by_cases h1 : hardware v.callees = true <;> by_cases h2 : shuffles v.callees = true
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) openNiPc_side
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) openNi_side
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) openPc_side
  · exact scrubFSide_of_fill (n := 0) (by fill_calls) open_side

end VG.Proof.AesGcmSiv.X86.Scrub
