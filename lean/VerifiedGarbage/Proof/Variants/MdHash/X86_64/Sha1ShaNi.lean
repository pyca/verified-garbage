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
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_shani"
  features := ["sha", "ssse3"]

section Scrub

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha1 VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## Without secret residue

Each function, followed by `Impl.Scrub.X86_64.scrubTail`, which wipes the
registers and the granules of its stack that the residue analysis of its
code (`X86_64.RTaint`) finds may hold secrets. -/

def updateKs : List Nat := keep_for% Spec.Sha1.updateApi.sig (updFn compress).stack (updFn compress).code

theorem updateRes : ResOk (updFn compress).code (updFn compress).contract (updFn compress).stack updateKs (chunks (updFn compress).stack) :=
  RScrub.resOk_reg0 (updFn compress).reg updateKs (by taint_decide)

def update : StreamFn := (updFn compress).scrub .sse updateKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (updOut compress) updateRes

theorem update_noResidue : NoResidue update.code (updFn compress).contract (updFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalizeKs : List Nat := keep_for% Spec.Sha1.finalizeApi.sig (finFn compress).stack (finFn compress).code

theorem finalizeRes : ResOk (finFn compress).code (finFn compress).contract (finFn compress).stack finalizeKs (chunks (finFn compress).stack) :=
  RScrub.resOk_reg0 (finFn compress).reg finalizeKs (by taint_decide)

def finalize : StreamFn := (finFn compress).scrub .sse finalizeKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (finOut compress) finalizeRes

theorem finalize_noResidue : NoResidue finalize.code (finFn compress).contract (finFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digestKs : List Nat := keep_for% Spec.Sha1.digestApi.sig (digFn compress).stack (digFn compress).code

theorem digestRes : ResOk (digFn compress).code (digFn compress).contract (digFn compress).stack digestKs (chunks (digFn compress).stack) :=
  RScrub.resOk_reg0 (digFn compress).reg digestKs (by taint_decide)

def digest : StreamFn := (digFn compress).scrub .sse digestKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (digOut compress) digestRes

theorem digest_noResidue : NoResidue digest.code (digFn compress).contract (digFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

end Scrub

/-- `variant` before the residue analysis of HMAC's `init` and `finalize`. -/
def unscrubbed : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha1.variant compress with stream := [update, finalize, digest] }

/-- HMAC's `finalize` over `unscrubbed`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacFinReg`). -/
def hmacFinKs : List Nat := keep_for% unscrubbed.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.I)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.I) .r8
      unscrubbed.H.hmacFin) []

theorem hmacFinOk : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.I) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.I) .r8
      unscrubbed.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.I) hmacFinKs (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.I))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFinKs (by taint_decide)

/-- HMAC's `init` over `unscrubbed`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacInitReg`). -/
def hmacInitKs : List Nat := keep_for% unscrubbed.I.initAnyKeyApi.sig (24 + Proof.Pbkdf2.Md.X86_64.anyFrame unscrubbed.I)
  (Proof.Pbkdf2.Md.X86_64.initCode unscrubbed.H unscrubbed.I) []

theorem hmacInitOk : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed.I.initAnyKeyApi.sig (24 + Proof.Pbkdf2.Md.X86_64.anyFrame unscrubbed.I) [])
      (Proof.Pbkdf2.Md.X86_64.initCode unscrubbed.H unscrubbed.I) h).any
      (VG.X86_64.RScrub.resOkB · (24 + Proof.Pbkdf2.Md.X86_64.anyFrame unscrubbed.I) hmacInitKs (Impl.Scrub.X86_64.chunks (24 + Proof.Pbkdf2.Md.X86_64.anyFrame unscrubbed.I))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacInitKs (by taint_decide)

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed with
    hmacFinRes := some ⟨hmacFinKs, hmacFinOk⟩
    hmacInitRes := some ⟨hmacInitKs, hmacInitOk⟩ }

end VG.Proof.Variants.MdHash.X86_64.Sha1ShaNi
