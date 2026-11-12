module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
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
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256Scrub
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Lit
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
public meta import VerifiedGarbage.Proof.Sha256.StateMem
public meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256Scrub
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224

/-!
# SHA-256 on x86-64: the scalar compression function: the variant's code and proofs

The variant `VG.Variants.MdHash.X86_64.Sha256.variant`
(`Variants/MdHash/X86_64/Sha256.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha256

/-- The scalar compression function. -/
def compress : Proof.Sha256.X86_64.Compress where
  callee := .scalar
  ok := Proof.Sha256.X86_64.Stream.scalar_ok
  mxcsr := by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide)
  suffix := ""
  features := []

section Scrub

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha256 VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## The functions with the working space this compression function uses

The compression function uses 112 bytes of scratch space: `update`,
`finalize` and `digest` give it only those (`Sha256.updFnS`). -/

abbrev updF : StreamFn := updFnS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112
abbrev finF : StreamFn := finFnS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112
abbrev digF : StreamFn := digFnS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112
abbrev fin224F : StreamFn := Sha224.finFnS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112
abbrev dig224F : StreamFn := Sha224.digFnS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112

/-! ## Without secret residue

Each function, followed by `Impl.Scrub.X86_64.scrubTail`, which wipes the
registers and the granules of its stack that the residue analysis of its
code (`X86_64.RTaint`) finds may hold secrets. -/

def updKs : List Nat := keep_for% Spec.Sha256.updateApi.sig updF.stack updF.code
def finKs : List Nat := keep_for% Spec.Sha256.finalizeApi.sig finF.stack finF.code
def digKs : List Nat := keep_for% Spec.Sha256.digest256Api.sig digF.stack digF.code

theorem updRes : ResOk updF.code updF.contract updF.stack updKs
    (chunks updF.stack) := RScrub.resOk_reg0 updF.reg updKs (by taint_decide)
theorem finRes : ResOk finF.code finF.contract finF.stack finKs
    (chunks finF.stack) := RScrub.resOk_reg0 finF.reg finKs (by taint_decide)
theorem digRes : ResOk digF.code digF.contract digF.stack digKs
    (chunks digF.stack) := RScrub.resOk_reg0 digF.reg digKs (by taint_decide)

def update : StreamFn := updF.scrub .sse updKs (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (updOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112) updRes
def finalize : StreamFn := finF.scrub .sse finKs (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (finOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112) finRes
def digest : StreamFn := digF.scrub .sse digKs (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (digOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112) digRes

theorem update_noResidue : NoResidue update.code updF.contract updF.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _
theorem finalize_noResidue : NoResidue finalize.code finF.contract finF.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _
theorem digest_noResidue : NoResidue digest.code digF.contract digF.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

/-! SHA-224's `finalize` and `digest`, with the same compression function. -/

def fin224Ks : List Nat :=
  keep_for% Spec.Sha256.finalize224Api.sig fin224F.stack fin224F.code
def dig224Ks : List Nat :=
  keep_for% Spec.Sha256.digest224Api.sig dig224F.stack dig224F.code

theorem fin224Res : ResOk fin224F.code fin224F.contract
    fin224F.stack fin224Ks (chunks fin224F.stack) :=
  RScrub.resOk_reg0 fin224F.reg fin224Ks (by taint_decide)
theorem dig224Res : ResOk dig224F.code dig224F.contract
    dig224F.stack dig224Ks (chunks dig224F.stack) :=
  RScrub.resOk_reg0 dig224F.reg dig224Ks (by taint_decide)

def finalize224 : StreamFn := fin224F.scrub .sse fin224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (Sha224.finOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112) fin224Res
def digest224 : StreamFn := dig224F.scrub .sse dig224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (Sha224.digOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112) dig224Res

theorem finalize224_noResidue :
    NoResidue finalize224.code fin224F.contract fin224F.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _
theorem digest224_noResidue :
    NoResidue digest224.code dig224F.contract dig224F.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

end Scrub

/-- `variant` before the residue analysis of HMAC's `finalize`. -/
def unscrubbed : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha256.variant compress
      (Proof.Pbkdf2.Md.X86_64.Sha256.ownS compress 112 (Or.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112 26
        Proof.Pbkdf2.Md.X86_64.Sha256.satW112) with
    stream := [update, finalize, digest] }

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

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed with hmacFinRes := some ⟨hmacFinKs, hmacFinOk⟩ }

/-- `variant224` before the residue analysis of HMAC's `finalize`. -/
def unscrubbed224 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha224.variant compress
      (Proof.Pbkdf2.Md.X86_64.Sha224.ownS compress 112 (Or.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112 26
        Proof.Pbkdf2.Md.X86_64.Sha224.satW112) with
    stream := [finalize224, digest224] }

/-- HMAC's `finalize` over `unscrubbed224`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacFinReg`). -/
def hmacFin224Ks : List Nat := keep_for% unscrubbed224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed224.I)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed224.I) .r8
      unscrubbed224.H.hmacFin) []

theorem hmacFin224Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed224.I) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed224.I) .r8
      unscrubbed224.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed224.I) hmacFin224Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed224.I))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFin224Ks (by taint_decide)

/-- SHA-224 with this compression function, its `finalize` and `digest`
without secret residue. -/
def variant224 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed224 with hmacFinRes := some ⟨hmacFin224Ks, hmacFin224Ok⟩ }

end VG.Proof.Variants.MdHash.X86_64.Sha256
