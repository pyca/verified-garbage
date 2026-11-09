module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.Avx
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
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Schedule
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256Scrub
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
public meta import VerifiedGarbage.Proof.Framework.AddrArith
public meta import VerifiedGarbage.Proof.Framework.Cold
public meta import VerifiedGarbage.Proof.Framework.EntryBranch
public meta import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Proof.Framework.OffsetBelow
public meta import VerifiedGarbage.Proof.Framework.OmegaLit
public meta import VerifiedGarbage.Proof.Framework.RegSetOrder
public meta import VerifiedGarbage.Proof.Framework.RegionsSub
public meta import VerifiedGarbage.Proof.Framework.TaintBatch
public meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
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
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Schedule
public meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256Scrub

/-!
# SHA-256 on x86-64 with AVX2 and BMI: the variant's code and proofs

The variant `VG.Variants.MdHash.X86_64.Sha256Avx2.variant`
(`Variants/MdHash/X86_64/Sha256Avx2.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha256Avx2

open VG.Impl.Sha256.X86_64.Stream (Callee)

theorem ok : Callee.avx2.Ok :=
  .of_verified Proof.Sha256.X86_64.Avx2.compress_verified.1
    Proof.Sha256.X86_64.Avx2.compress_verified.2.1
    (by change (instrs Impl.Sha256.X86_64.Avx2.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha256.X86_64.Avx2.compress.depth = 0; lit_decide)

/-- The compression function with AVX2 and BMI. -/
def compress : Proof.Sha256.X86_64.Compress where
  callee := .avx2
  ok := ok
  mxcsr := by change Impl.Sha256.X86_64.Avx2.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_allInstrs (by change Impl.Sha256.X86_64.Avx2.compress.allInstrs _ = true; lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2", "bmi1", "bmi2"]

section Scrub

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha256 VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## Without secret residue

Each function, followed by `Impl.Scrub.X86_64.scrubTail`, which wipes the
registers and the granules of its stack that the residue analysis of its
code (`X86_64.RTaint`) finds may hold secrets. -/

def updKs : List Nat := keep_for% Spec.Sha256.updateApi.sig (updFn compress).stack (updFn compress).code
def finKs : List Nat := keep_for% Spec.Sha256.finalizeApi.sig (finFn compress).stack (finFn compress).code
def digKs : List Nat := keep_for% Spec.Sha256.digest256Api.sig (digFn compress).stack (digFn compress).code

theorem updRes : ResOk (updFn compress).code (updFn compress).contract (updFn compress).stack updKs
    (chunks (updFn compress).stack) := RScrub.resOk_reg0 (updFn compress).reg updKs (by taint_decide)
theorem finRes : ResOk (finFn compress).code (finFn compress).contract (finFn compress).stack finKs
    (chunks (finFn compress).stack) := RScrub.resOk_reg0 (finFn compress).reg finKs (by taint_decide)
theorem digRes : ResOk (digFn compress).code (digFn compress).contract (digFn compress).stack digKs
    (chunks (digFn compress).stack) := RScrub.resOk_reg0 (digFn compress).reg digKs (by taint_decide)

def update : StreamFn := (updFn compress).scrub .avx updKs (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (updOut compress) updRes
def finalize : StreamFn := (finFn compress).scrub .avx finKs (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (finOut compress) finRes
def digest : StreamFn := (digFn compress).scrub .avx digKs (by lit_decide) (by decide) (by decide) (by lit_decide)
  (by decide) (digOut compress) digRes

theorem update_noResidue : NoResidue update.code (updFn compress).contract (updFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _
theorem finalize_noResidue : NoResidue finalize.code (finFn compress).contract (finFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _
theorem digest_noResidue : NoResidue digest.code (digFn compress).contract (digFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

end Scrub

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha256.variant compress with stream := [update, finalize, digest] }

end VG.Proof.Variants.MdHash.X86_64.Sha256Avx2
