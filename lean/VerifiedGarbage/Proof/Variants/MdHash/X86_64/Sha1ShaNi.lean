module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1Scrub
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.AddrArith
public meta import VerifiedGarbage.Proof.Framework.Cold
public meta import VerifiedGarbage.Proof.Framework.EntryBranch
public meta import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Proof.Framework.OffsetBelow
public meta import VerifiedGarbage.Proof.Framework.OmegaLit
public meta import VerifiedGarbage.Proof.Framework.RegSetOrder
public meta import VerifiedGarbage.Proof.Framework.RegionsSub
public meta import VerifiedGarbage.Proof.Framework.TaintBatch
public meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
public meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
public meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
public meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public meta import VerifiedGarbage.Proof.Hmac.AnyKey
public meta import VerifiedGarbage.Proof.Hmac.Common
public meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
public meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
public meta import VerifiedGarbage.Proof.Pbkdf2.Scratch
public meta import VerifiedGarbage.Proof.Sha1.X86_64.Shared
public meta import VerifiedGarbage.Proof.Sha256.StateMem
public meta import VerifiedGarbage.Proof.Sha256.Stream
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide

/-!
# SHA-1 on x86-64 with the SHA extensions: the variant's code and proofs

The variant `VG.Variants.MdHash.X86_64.Sha1ShaNi.variant`
(`Variants/MdHash/X86_64/Sha1ShaNi.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha1ShaNi

/-- The compression function with the SHA extensions. -/
def compress : Proof.Sha1.X86_64.Compress where
  callee := .shani
  ok := Proof.Sha1.X86_64.Stream.shani_ok
  okS := Proof.Sha1.X86_64.Stream.shani_ok0
  mxcsr := by decide +kernel
  spSafe := Code.all_of_spTest (by lit_decide)
  suffix := "_shani"
  features := ["sha", "ssse3"]

section Scrub

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha1 VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## The functions with the working space this compression function uses

It uses none: `update`, `finalize` and `digest` give it none
(`Sha1.updFn0`). -/

abbrev updF : StreamFn := updFn0 compress Proof.Sha1.X86_64.Stream.shani_ok0
abbrev finF : StreamFn := finFn0 compress Proof.Sha1.X86_64.Stream.shani_ok0
abbrev digF : StreamFn := digFn0 compress Proof.Sha1.X86_64.Stream.shani_ok0

/-! ## Without secret residue

Each function, followed by its cleanup (`StreamFnS.scrubbed`): what the cleanup
needs of its code, evaluated here once, the runs of granules of its stack
that the residue analysis (`X86_64.RTaint`) finds may hold secrets, and its
other conditions (`X86_64.Scrub.SelScrub`). -/

theorem update_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init updF.api.sig updF.stack []) updF.code h).any
      (VG.X86_64.RScrub.resOkB · updF.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA updF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem update_side : VG.X86_64.Scrub.scrubSideG updF.code updF.stack updF.retBits .sse true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA updF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def update : Proof.Pbkdf2.Md.X86_64.StreamFnS updF.api := ⟨updF, (updOut0 compress Proof.Sha1.X86_64.Stream.shani_ok0), ⟨.sse, [], update_ok, update_side⟩, rfl⟩

theorem finalize_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init finF.api.sig finF.stack []) finF.code h).any
      (VG.X86_64.RScrub.resOkB · finF.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA finF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem finalize_side : VG.X86_64.Scrub.scrubSideG finF.code finF.stack finF.retBits .sse true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA finF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def finalize : Proof.Pbkdf2.Md.X86_64.StreamFnS finF.api := ⟨finF, (finOut0 compress Proof.Sha1.X86_64.Stream.shani_ok0), ⟨.sse, [], finalize_ok, finalize_side⟩, rfl⟩

theorem digest_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init digF.api.sig digF.stack []) digF.code h).any
      (VG.X86_64.RScrub.resOkB · digF.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA digF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem digest_side : VG.X86_64.Scrub.scrubSideG digF.code digF.stack digF.retBits .sse true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA digF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def digest : Proof.Pbkdf2.Md.X86_64.StreamFnS digF.api := ⟨digF, (digOut0 compress Proof.Sha1.X86_64.Stream.shani_ok0), ⟨.sse, [], digest_ok, digest_side⟩, rfl⟩

end Scrub

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha1.variant compress

/-- The streaming functions made with this compression function, with their
cleanup, for its registration file. -/
def streams : Proof.Pbkdf2.Md.X86_64.StreamFns Spec.Sha1.updateApi Spec.Sha1.finalizeApi Spec.Sha1.digestApi :=
  ⟨variant.suffix, update, finalize, digest⟩

theorem fin_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) (Impl.Scrub.X86_64.runKs [(120, 2)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(120, 2)] (by taint_decide_lit)

theorem fin_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) ((Spec.Hmac.finalizeSig variant.I.S).retBits 64) .sse true
    (Impl.Scrub.X86_64.runKs [(120, 2)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(120, 2)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant`, with what its cleanup needs. -/
def fin : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant, by decide, ⟨.sse, [(120, 2)], fin_ok, fin_side⟩⟩

end VG.Proof.Variants.MdHash.X86_64.Sha1ShaNi
