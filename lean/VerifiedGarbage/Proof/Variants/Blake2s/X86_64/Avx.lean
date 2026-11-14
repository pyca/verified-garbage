module

public import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Stream
public import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Compress
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Stream
public meta import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Compress
public meta import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub

/-!
# BLAKE2s on x86-64 with AVX: the variant's code and proofs

The variant `VG.Variants.Blake2s.X86_64.Avx.variant`
(`Variants/Blake2s/X86_64/Avx.lean`), with the proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Blake2s.X86_64.Avx

section Scrub

open VG.X86_64

/-! ## Without secret residue

`vg_blake2s_update` and `vg_blake2s_finalize` over this backend, followed by
`Impl.Scrub.X86_64.scrubTail`, which wipes the registers and the granules of
their stack that the residue analysis of their code (`X86_64.RTaint`) finds
may hold secrets (`Blake2.X86_64.updateSReg`). -/

/-- `vg_blake2s_update`'s code. -/
abbrev updateCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 584 .r8 (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx)

def updateKs : List Nat := keep_for% Spec.Blake2.updateSApi.sig (8 + 584) updateCode []

theorem updateOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blake2.updateSApi.sig (8 + 584) []) updateCode
      h).any (RScrub.resOkB · (8 + 584) updateKs (Impl.Scrub.X86_64.chunks (8 + 584))) = true :=
  RScrub.Analysed.ok_of updateKs (by taint_decide)

/-- `vg_blake2s_finalize`'s code. -/
abbrev finalizeCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 584 .rcx (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx)

def finalizeKs : List Nat := keep_for% Spec.Blake2.finalizeSApi.sig (8 + 584) finalizeCode []

theorem finalizeOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Blake2.finalizeSApi.sig (8 + 584) []) finalizeCode
      h).any (RScrub.resOkB · (8 + 584) finalizeKs (Impl.Scrub.X86_64.chunks (8 + 584))) = true :=
  RScrub.Analysed.ok_of finalizeKs (by taint_decide)

end Scrub

/-- Never chosen on Zen 5, whose vector integer instructions have twice the
latency of its scalar ones: this compression function is one chain of
them, and on a Ryzen 9 9950X hashes 16 KiB in 26.7 µs, the baseline's in
15.4 µs. (On Zen 3 this one is the faster.) -/
def variant : Proof.Blake2.X86_64.BackendS where
  suffix := "_avx"
  features := ["avx"]
  notWith := ["zen5"]
  code := Impl.Blake2.X86_64.Avx.compress
  callee := Proof.Blake2.X86_64.Avx.callee
  verified := Proof.Blake2.X86_64.Avx.compress_verified
  spSafe := Code.all_of_allInstrs (by lit_decide)
  updateCT := Proof.Blake2.X86_64.Avx.update_ct
  finalizeCT := Proof.Blake2.X86_64.Avx.finalize_ct
  updateMxcsr := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ = true
    lit_decide
  finalizeMxcsr := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ =
      true
    lit_decide
  updateSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ = true
    lit_decide)
  finalizeSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ =
      true
    lit_decide)
  updateDepth := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).x86_64Depth ≤ 8
    lit_decide
  finalizeDepth := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).x86_64Depth ≤ 8
    lit_decide
  updateRes := some ⟨updateKs, updateOk⟩
  finalizeRes := some ⟨finalizeKs, finalizeOk⟩

end VG.Proof.Variants.Blake2s.X86_64.Avx
