module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1Scrub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1Scrub
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SHA-1 on x86-64: the scalar compression function: the variant without secret residue

The variant `VG.Proof.Variants.MdHash.X86_64.sha1`
(`Variants/MdHash/X86_64.lean`): SHA-1's functions with the scalar
compression function (`Proof.Sha1.X86_64.scalar`), scrubbed.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha1

/-- The scalar compression function. -/
abbrev compress : Proof.Sha1.X86_64.Compress := .scalar

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

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha1.variant compress with stream := [update, finalize, digest] }

end VG.Proof.Variants.MdHash.X86_64.Sha1
