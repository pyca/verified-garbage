module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512Scrub
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512Scrub
public meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on x86-64 with the SHA-512 extensions, without secret residue

Their streaming and one-shot functions with this compression function,
scrubbed: the variants `sha384`, `sha512`, `sha512_224` and `sha512_256` of
`Proof/Variants/MdHash/X86_64.lean` with it take their functions from here.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha512ShaNi

abbrev compress : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.shani

section Scrub

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha512 VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## Without secret residue

Each function, followed by `Impl.Scrub.X86_64.scrubTail`, which wipes the
registers and the granules of its stack that the residue analysis of its
code (`X86_64.RTaint`) finds may hold secrets. -/

def updateKs : List Nat := keep_for% Spec.Sha512.updateApi.sig (updFn compress).stack (updFn compress).code

theorem updateRes : ResOk (updFn compress).code (updFn compress).contract (updFn compress).stack updateKs (chunks (updFn compress).stack) :=
  RScrub.resOk_reg0 (updFn compress).reg updateKs (by taint_decide)

def update : StreamFn := (updFn compress).scrub .avx updateKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (updOut compress) updateRes

theorem update_noResidue : NoResidue update.code (updFn compress).contract (updFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalizeKs : List Nat := keep_for% Spec.Sha512.finalizeApi.sig (finFn compress).stack (finFn compress).code

theorem finalizeRes : ResOk (finFn compress).code (finFn compress).contract (finFn compress).stack finalizeKs (chunks (finFn compress).stack) :=
  RScrub.resOk_reg0 (finFn compress).reg finalizeKs (by taint_decide)

def finalize : StreamFn := (finFn compress).scrub .avx finalizeKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (finOut compress) finalizeRes

theorem finalize_noResidue : NoResidue finalize.code (finFn compress).contract (finFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digestKs : List Nat := keep_for% Spec.Sha512.digest512Api.sig (digFn compress).stack (digFn compress).code

theorem digestRes : ResOk (digFn compress).code (digFn compress).contract (digFn compress).stack digestKs (chunks (digFn compress).stack) :=
  RScrub.resOk_reg0 (digFn compress).reg digestKs (by taint_decide)

def digest : StreamFn := (digFn compress).scrub .avx digestKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (digOut compress) digestRes

theorem digest_noResidue : NoResidue digest.code (digFn compress).contract (digFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize384Ks : List Nat := keep_for% Spec.Sha512.finalize384Api.sig (fin384Fn compress).stack (fin384Fn compress).code

theorem finalize384Res : ResOk (fin384Fn compress).code (fin384Fn compress).contract (fin384Fn compress).stack finalize384Ks (chunks (fin384Fn compress).stack) :=
  RScrub.resOk_reg0 (fin384Fn compress).reg finalize384Ks (by taint_decide)

def finalize384 : StreamFn := (fin384Fn compress).scrub .avx finalize384Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin384Out compress) finalize384Res

theorem finalize384_noResidue : NoResidue finalize384.code (fin384Fn compress).contract (fin384Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest384Ks : List Nat := keep_for% Spec.Sha512.digest384Api.sig (dig384Fn compress).stack (dig384Fn compress).code

theorem digest384Res : ResOk (dig384Fn compress).code (dig384Fn compress).contract (dig384Fn compress).stack digest384Ks (chunks (dig384Fn compress).stack) :=
  RScrub.resOk_reg0 (dig384Fn compress).reg digest384Ks (by taint_decide)

def digest384 : StreamFn := (dig384Fn compress).scrub .avx digest384Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig384Out compress) digest384Res

theorem digest384_noResidue : NoResidue digest384.code (dig384Fn compress).contract (dig384Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize512_256Ks : List Nat := keep_for% Spec.Sha512.finalize512_256Api.sig (fin512_256Fn compress).stack (fin512_256Fn compress).code

theorem finalize512_256Res : ResOk (fin512_256Fn compress).code (fin512_256Fn compress).contract (fin512_256Fn compress).stack finalize512_256Ks (chunks (fin512_256Fn compress).stack) :=
  RScrub.resOk_reg0 (fin512_256Fn compress).reg finalize512_256Ks (by taint_decide)

def finalize512_256 : StreamFn := (fin512_256Fn compress).scrub .avx finalize512_256Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin512_256Out compress) finalize512_256Res

theorem finalize512_256_noResidue : NoResidue finalize512_256.code (fin512_256Fn compress).contract (fin512_256Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest512_256Ks : List Nat := keep_for% Spec.Sha512.digest512_256Api.sig (dig512_256Fn compress).stack (dig512_256Fn compress).code

theorem digest512_256Res : ResOk (dig512_256Fn compress).code (dig512_256Fn compress).contract (dig512_256Fn compress).stack digest512_256Ks (chunks (dig512_256Fn compress).stack) :=
  RScrub.resOk_reg0 (dig512_256Fn compress).reg digest512_256Ks (by taint_decide)

def digest512_256 : StreamFn := (dig512_256Fn compress).scrub .avx digest512_256Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig512_256Out compress) digest512_256Res

theorem digest512_256_noResidue : NoResidue digest512_256.code (dig512_256Fn compress).contract (dig512_256Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize512_224Ks : List Nat := keep_for% Spec.Sha512.finalize512_224Api.sig (fin512_224Fn compress).stack (fin512_224Fn compress).code

theorem finalize512_224Res : ResOk (fin512_224Fn compress).code (fin512_224Fn compress).contract (fin512_224Fn compress).stack finalize512_224Ks (chunks (fin512_224Fn compress).stack) :=
  RScrub.resOk_reg0 (fin512_224Fn compress).reg finalize512_224Ks (by taint_decide)

def finalize512_224 : StreamFn := (fin512_224Fn compress).scrub .avx finalize512_224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin512_224Out compress) finalize512_224Res

theorem finalize512_224_noResidue : NoResidue finalize512_224.code (fin512_224Fn compress).contract (fin512_224Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest512_224Ks : List Nat := keep_for% Spec.Sha512.digest512_224Api.sig (dig512_224Fn compress).stack (dig512_224Fn compress).code

theorem digest512_224Res : ResOk (dig512_224Fn compress).code (dig512_224Fn compress).contract (dig512_224Fn compress).stack digest512_224Ks (chunks (dig512_224Fn compress).stack) :=
  RScrub.resOk_reg0 (dig512_224Fn compress).reg digest512_224Ks (by taint_decide)

def digest512_224 : StreamFn := (dig512_224Fn compress).scrub .avx digest512_224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig512_224Out compress) digest512_224Res

theorem digest512_224_noResidue : NoResidue digest512_224.code (dig512_224Fn compress).contract (dig512_224Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

end Scrub

/-- The streaming `update` and `finalize`, and SHA-512's one-shot `digest`. -/
def stream : List Proof.Pbkdf2.Md.X86_64.StreamFn := [update, finalize, digest]

/-- SHA-384's `finalize` and one-shot `digest`. -/
def stream384 : List Proof.Pbkdf2.Md.X86_64.StreamFn := [finalize384, digest384]

/-- SHA-512/256's `finalize` and one-shot `digest`. -/
def stream512_256 : List Proof.Pbkdf2.Md.X86_64.StreamFn := [finalize512_256, digest512_256]

/-- SHA-512/224's `finalize` and one-shot `digest`. -/
def stream512_224 : List Proof.Pbkdf2.Md.X86_64.StreamFn := [finalize512_224, digest512_224]

end VG.Proof.Variants.MdHash.X86_64.Sha512ShaNi
