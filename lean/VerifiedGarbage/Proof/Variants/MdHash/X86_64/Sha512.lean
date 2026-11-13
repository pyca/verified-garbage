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

/-! ## The functions with the working space this compression function uses

The compression function uses 192 bytes of scratch space: the streaming and
one-shot functions give it only those (`Sha512.updFnS`). -/

abbrev updF : StreamFn := updFnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev finF : StreamFn := finFnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev digF : StreamFn := digFnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev fin384F : StreamFn := fin384FnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev dig384F : StreamFn := dig384FnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev fin512_256F : StreamFn := fin512_256FnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev dig512_256F : StreamFn := dig512_256FnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev fin512_224F : StreamFn := fin512_224FnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192
abbrev dig512_224F : StreamFn := dig512_224FnS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192

/-! ## Without secret residue

Each function, followed by `Impl.Scrub.X86_64.scrubTail`, which wipes the
registers and the granules of its stack that the residue analysis of its
code (`X86_64.RTaint`) finds may hold secrets. -/

def updateKs : List Nat := keep_for% Spec.Sha512.updateApi.sig updF.stack updF.code

theorem updateRes : ResOk updF.code updF.contract updF.stack updateKs (chunks updF.stack) :=
  RScrub.resOk_reg0 updF.reg updateKs (by taint_decide)

def update : StreamFn := updF.scrub .sse updateKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (updOutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) updateRes

theorem update_noResidue : NoResidue update.code updF.contract updF.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalizeKs : List Nat := keep_for% Spec.Sha512.finalizeApi.sig finF.stack finF.code

theorem finalizeRes : ResOk finF.code finF.contract finF.stack finalizeKs (chunks finF.stack) :=
  RScrub.resOk_reg0 finF.reg finalizeKs (by taint_decide)

def finalize : StreamFn := finF.scrub .sse finalizeKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (finOutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) finalizeRes

theorem finalize_noResidue : NoResidue finalize.code finF.contract finF.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digestKs : List Nat := keep_for% Spec.Sha512.digest512Api.sig digF.stack digF.code

theorem digestRes : ResOk digF.code digF.contract digF.stack digestKs (chunks digF.stack) :=
  RScrub.resOk_reg0 digF.reg digestKs (by taint_decide)

def digest : StreamFn := digF.scrub .sse digestKs (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (digOutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) digestRes

theorem digest_noResidue : NoResidue digest.code digF.contract digF.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize384Ks : List Nat := keep_for% Spec.Sha512.finalize384Api.sig fin384F.stack fin384F.code

theorem finalize384Res : ResOk fin384F.code fin384F.contract fin384F.stack finalize384Ks (chunks fin384F.stack) :=
  RScrub.resOk_reg0 fin384F.reg finalize384Ks (by taint_decide)

def finalize384 : StreamFn := fin384F.scrub .sse finalize384Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin384OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) finalize384Res

theorem finalize384_noResidue : NoResidue finalize384.code fin384F.contract fin384F.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest384Ks : List Nat := keep_for% Spec.Sha512.digest384Api.sig dig384F.stack dig384F.code

theorem digest384Res : ResOk dig384F.code dig384F.contract dig384F.stack digest384Ks (chunks dig384F.stack) :=
  RScrub.resOk_reg0 dig384F.reg digest384Ks (by taint_decide)

def digest384 : StreamFn := dig384F.scrub .sse digest384Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig384OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) digest384Res

theorem digest384_noResidue : NoResidue digest384.code dig384F.contract dig384F.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize512_256Ks : List Nat := keep_for% Spec.Sha512.finalize512_256Api.sig fin512_256F.stack fin512_256F.code

theorem finalize512_256Res : ResOk fin512_256F.code fin512_256F.contract fin512_256F.stack finalize512_256Ks (chunks fin512_256F.stack) :=
  RScrub.resOk_reg0 fin512_256F.reg finalize512_256Ks (by taint_decide)

def finalize512_256 : StreamFn := fin512_256F.scrub .sse finalize512_256Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin512_256OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) finalize512_256Res

theorem finalize512_256_noResidue : NoResidue finalize512_256.code fin512_256F.contract fin512_256F.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest512_256Ks : List Nat := keep_for% Spec.Sha512.digest512_256Api.sig dig512_256F.stack dig512_256F.code

theorem digest512_256Res : ResOk dig512_256F.code dig512_256F.contract dig512_256F.stack digest512_256Ks (chunks dig512_256F.stack) :=
  RScrub.resOk_reg0 dig512_256F.reg digest512_256Ks (by taint_decide)

def digest512_256 : StreamFn := dig512_256F.scrub .sse digest512_256Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig512_256OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) digest512_256Res

theorem digest512_256_noResidue : NoResidue digest512_256.code dig512_256F.contract dig512_256F.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def finalize512_224Ks : List Nat := keep_for% Spec.Sha512.finalize512_224Api.sig fin512_224F.stack fin512_224F.code

theorem finalize512_224Res : ResOk fin512_224F.code fin512_224F.contract fin512_224F.stack finalize512_224Ks (chunks fin512_224F.stack) :=
  RScrub.resOk_reg0 fin512_224F.reg finalize512_224Ks (by taint_decide)

def finalize512_224 : StreamFn := fin512_224F.scrub .sse finalize512_224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (fin512_224OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) finalize512_224Res

theorem finalize512_224_noResidue : NoResidue finalize512_224.code fin512_224F.contract fin512_224F.retBits :=
  StreamFn.scrub_noResidue _ _ _ _ _ _ _ _ _ _

def digest512_224Ks : List Nat := keep_for% Spec.Sha512.digest512_224Api.sig dig512_224F.stack dig512_224F.code

theorem digest512_224Res : ResOk dig512_224F.code dig512_224F.contract dig512_224F.stack digest512_224Ks (chunks dig512_224F.stack) :=
  RScrub.resOk_reg0 dig512_224F.reg digest512_224Ks (by taint_decide)

def digest512_224 : StreamFn := dig512_224F.scrub .sse digest512_224Ks (by lit_decide) (by decide) (by decide)
  (by lit_decide) (by decide) (dig512_224OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192) digest512_224Res

theorem digest512_224_noResidue : NoResidue digest512_224.code dig512_224F.contract dig512_224F.retBits :=
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
def hmacFin384Ks : List Nat := keep_for% unscrubbed384.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.H)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.H) .r8
      unscrubbed384.H.hmacFin) []

theorem hmacFin384Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed384.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.H) .r8
      unscrubbed384.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.H) hmacFin384Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed384.H))) = true :=
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
def hmacFin512Ks : List Nat := keep_for% unscrubbed512.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.H)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.H) .r8
      unscrubbed512.H.hmacFin) []

theorem hmacFin512Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed512.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.H) .r8
      unscrubbed512.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.H) hmacFin512Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512.H))) = true :=
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
def hmacFin512_224Ks : List Nat := keep_for% unscrubbed512_224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.H)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.H) .r8
      unscrubbed512_224.H.hmacFin) []

theorem hmacFin512_224Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed512_224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.H) .r8
      unscrubbed512_224.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.H) hmacFin512_224Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_224.H))) = true :=
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
def hmacFin512_256Ks : List Nat := keep_for% unscrubbed512_256.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.H)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.H) .r8
      unscrubbed512_256.H.hmacFin) []

theorem hmacFin512_256Ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed512_256.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.H) .r8
      unscrubbed512_256.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.H) hmacFin512_256Ks (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed512_256.H))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFin512_256Ks (by taint_decide)

def variant512_256 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed512_256 with hmacFinRes := some ⟨hmacFin512_256Ks, hmacFin512_256Ok⟩ }

end VG.Proof.Variants.MdHash.X86_64.Sha512
