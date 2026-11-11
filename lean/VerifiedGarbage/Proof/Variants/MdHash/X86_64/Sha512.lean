module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512Scrub
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512Scrub
public meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on x86-64 with the scalar compression function, without secret residue

Their streaming and one-shot functions with this compression function,
scrubbed: the variants `sha384`, `sha512`, `sha512_224` and `sha512_256` of
`Proof/Variants/MdHash/X86_64.lean` with it take their functions from here.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha512

abbrev compress : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.scalar

section Scrub

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha512 VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## Without secret residue

Each function, followed by `Impl.Scrub.X86_64.scrubTail`, which wipes the
registers and the granules of its stack that the residue analysis of its
code (`X86_64.RTaint`) finds may hold secrets. -/

def updateKs : List Nat := keep_for% Spec.Sha512.updateApi.sig (updFn compress).stack (updFn compress).code

theorem updateRes : ResOk (updFn compress).code (updFn compress).contract (updFn compress).stack updateKs (chunks (updFn compress).stack) :=
  RScrub.resOk_reg0 (updFn compress).reg updateKs (by taint_decide)

def update : StreamFn := (updFn compress).scrub .sse updateKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (updOut compress) updateRes

theorem update_noResidue : NoResidue update.code (updFn compress).contract (updFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalizeKs : List Nat := keep_for% Spec.Sha512.finalizeApi.sig (finFn compress).stack (finFn compress).code

theorem finalizeRes : ResOk (finFn compress).code (finFn compress).contract (finFn compress).stack finalizeKs (chunks (finFn compress).stack) :=
  RScrub.resOk_reg0 (finFn compress).reg finalizeKs (by taint_decide)

def finalize : StreamFn := (finFn compress).scrub .sse finalizeKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (finOut compress) finalizeRes

theorem finalize_noResidue : NoResidue finalize.code (finFn compress).contract (finFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digestKs : List Nat := keep_for% Spec.Sha512.digest512Api.sig (digFn compress).stack (digFn compress).code

theorem digestRes : ResOk (digFn compress).code (digFn compress).contract (digFn compress).stack digestKs (chunks (digFn compress).stack) :=
  RScrub.resOk_reg0 (digFn compress).reg digestKs (by taint_decide)

def digest : StreamFn := (digFn compress).scrub .sse digestKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (digOut compress) digestRes

theorem digest_noResidue : NoResidue digest.code (digFn compress).contract (digFn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize384Ks : List Nat := keep_for% Spec.Sha512.finalize384Api.sig (fin384Fn compress).stack (fin384Fn compress).code

theorem finalize384Res : ResOk (fin384Fn compress).code (fin384Fn compress).contract (fin384Fn compress).stack finalize384Ks (chunks (fin384Fn compress).stack) :=
  RScrub.resOk_reg0 (fin384Fn compress).reg finalize384Ks (by taint_decide)

def finalize384 : StreamFn := (fin384Fn compress).scrub .sse finalize384Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin384Out compress) finalize384Res

theorem finalize384_noResidue : NoResidue finalize384.code (fin384Fn compress).contract (fin384Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest384Ks : List Nat := keep_for% Spec.Sha512.digest384Api.sig (dig384Fn compress).stack (dig384Fn compress).code

theorem digest384Res : ResOk (dig384Fn compress).code (dig384Fn compress).contract (dig384Fn compress).stack digest384Ks (chunks (dig384Fn compress).stack) :=
  RScrub.resOk_reg0 (dig384Fn compress).reg digest384Ks (by taint_decide)

def digest384 : StreamFn := (dig384Fn compress).scrub .sse digest384Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig384Out compress) digest384Res

theorem digest384_noResidue : NoResidue digest384.code (dig384Fn compress).contract (dig384Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize512_256Ks : List Nat := keep_for% Spec.Sha512.finalize512_256Api.sig (fin512_256Fn compress).stack (fin512_256Fn compress).code

theorem finalize512_256Res : ResOk (fin512_256Fn compress).code (fin512_256Fn compress).contract (fin512_256Fn compress).stack finalize512_256Ks (chunks (fin512_256Fn compress).stack) :=
  RScrub.resOk_reg0 (fin512_256Fn compress).reg finalize512_256Ks (by taint_decide)

def finalize512_256 : StreamFn := (fin512_256Fn compress).scrub .sse finalize512_256Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin512_256Out compress) finalize512_256Res

theorem finalize512_256_noResidue : NoResidue finalize512_256.code (fin512_256Fn compress).contract (fin512_256Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest512_256Ks : List Nat := keep_for% Spec.Sha512.digest512_256Api.sig (dig512_256Fn compress).stack (dig512_256Fn compress).code

theorem digest512_256Res : ResOk (dig512_256Fn compress).code (dig512_256Fn compress).contract (dig512_256Fn compress).stack digest512_256Ks (chunks (dig512_256Fn compress).stack) :=
  RScrub.resOk_reg0 (dig512_256Fn compress).reg digest512_256Ks (by taint_decide)

def digest512_256 : StreamFn := (dig512_256Fn compress).scrub .sse digest512_256Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig512_256Out compress) digest512_256Res

theorem digest512_256_noResidue : NoResidue digest512_256.code (dig512_256Fn compress).contract (dig512_256Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize512_224Ks : List Nat := keep_for% Spec.Sha512.finalize512_224Api.sig (fin512_224Fn compress).stack (fin512_224Fn compress).code

theorem finalize512_224Res : ResOk (fin512_224Fn compress).code (fin512_224Fn compress).contract (fin512_224Fn compress).stack finalize512_224Ks (chunks (fin512_224Fn compress).stack) :=
  RScrub.resOk_reg0 (fin512_224Fn compress).reg finalize512_224Ks (by taint_decide)

def finalize512_224 : StreamFn := (fin512_224Fn compress).scrub .sse finalize512_224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin512_224Out compress) finalize512_224Res

theorem finalize512_224_noResidue : NoResidue finalize512_224.code (fin512_224Fn compress).contract (fin512_224Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest512_224Ks : List Nat := keep_for% Spec.Sha512.digest512_224Api.sig (dig512_224Fn compress).stack (dig512_224Fn compress).code

theorem digest512_224Res : ResOk (dig512_224Fn compress).code (dig512_224Fn compress).contract (dig512_224Fn compress).stack digest512_224Ks (chunks (dig512_224Fn compress).stack) :=
  RScrub.resOk_reg0 (dig512_224Fn compress).reg digest512_224Ks (by taint_decide)

def digest512_224 : StreamFn := (dig512_224Fn compress).scrub .sse digest512_224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig512_224Out compress) digest512_224Res

theorem digest512_224_noResidue : NoResidue digest512_224.code (dig512_224Fn compress).contract (dig512_224Fn compress).retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

end Scrub

/-- The streaming `update` and `finalize`, and SHA-512's one-shot `digest`.
Ed25519's key-pair generation calls the digest's code as the internal
`vg_sha512_digest<suffix>_core`. -/
def stream : List Proof.Pbkdf2.Md.X86_64.StreamFn := [update, finalize, digest]

/-- SHA-384's `finalize` and one-shot `digest`. -/
def stream384 : List Proof.Pbkdf2.Md.X86_64.StreamFn := [finalize384, digest384]

/-- SHA-512/256's `finalize` and one-shot `digest`. -/
def stream512_256 : List Proof.Pbkdf2.Md.X86_64.StreamFn := [finalize512_256, digest512_256]

/-- SHA-512/224's `finalize` and one-shot `digest`. -/
def stream512_224 : List Proof.Pbkdf2.Md.X86_64.StreamFn := [finalize512_224, digest512_224]

/-- SHA-384 with this compression function, before the residue analysis of
HMAC's `finalize`. -/
def unscrubbed384 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha384 compress stream384

/-- HMAC's `finalize` over `unscrubbed384`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacFinReg`). -/
def hmacFin384Ks : List Nat := keep_for% unscrubbed384.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.I)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.I) .r8
      unscrubbed384.H.hmacFin) []

theorem hmacFin384Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed384.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.I) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.I) .r8
      unscrubbed384.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.I) hmacFin384Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.I))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFin384Ks (by taint_decide)

def variant384 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed384 with hmacFinRes := some ⟨hmacFin384Ks, hmacFin384Ok⟩ }

/-- SHA-512 with this compression function, before the residue analysis of
HMAC's `finalize`. -/
def unscrubbed512 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 compress stream

/-- HMAC's `finalize` over `unscrubbed512`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacFinReg`). -/
def hmacFin512Ks : List Nat := keep_for% unscrubbed512.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.I)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.I) .r8
      unscrubbed512.H.hmacFin) []

theorem hmacFin512Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed512.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.I) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.I) .r8
      unscrubbed512.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.I) hmacFin512Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.I))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFin512Ks (by taint_decide)

def variant512 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed512 with hmacFinRes := some ⟨hmacFin512Ks, hmacFin512Ok⟩ }

/-- SHA-512/224 with this compression function, before the residue analysis of
HMAC's `finalize`. -/
def unscrubbed512_224 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_224 compress stream512_224

/-- HMAC's `finalize` over `unscrubbed512_224`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacFinReg`). -/
def hmacFin512_224Ks : List Nat := keep_for% unscrubbed512_224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.I)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.I) .r8
      unscrubbed512_224.H.hmacFin) []

theorem hmacFin512_224Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed512_224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.I) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.I) .r8
      unscrubbed512_224.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.I) hmacFin512_224Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.I))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFin512_224Ks (by taint_decide)

def variant512_224 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed512_224 with hmacFinRes := some ⟨hmacFin512_224Ks, hmacFin512_224Ok⟩ }

/-- SHA-512/256 with this compression function, before the residue analysis of
HMAC's `finalize`. -/
def unscrubbed512_256 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 compress stream512_256

/-- HMAC's `finalize` over `unscrubbed512_256`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacFinReg`). -/
def hmacFin512_256Ks : List Nat := keep_for% unscrubbed512_256.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.I)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.I) .r8
      unscrubbed512_256.H.hmacFin) []

theorem hmacFin512_256Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed512_256.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.I) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.I) .r8
      unscrubbed512_256.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.I) hmacFin512_256Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.I))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFin512_256Ks (by taint_decide)

def variant512_256 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed512_256 with hmacFinRes := some ⟨hmacFin512_256Ks, hmacFin512_256Ok⟩ }

end VG.Proof.Variants.MdHash.X86_64.Sha512
