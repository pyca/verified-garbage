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

Each function, followed by its cleanup (`StreamFnS.scrubbed`): what the cleanup
needs of its code, evaluated here once, the runs of granules of its stack
that the residue analysis (`X86_64.RTaint`) finds may hold secrets, and its
other conditions (`X86_64.Scrub.SelScrub`). -/

theorem update_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init updF.api.sig updF.stack []) updF.code h).any
      (VG.X86_64.RScrub.resOkB · updF.stack (Impl.Scrub.X86_64.runKs [(8, 9)])
        (Impl.Scrub.X86_64.chunksA updF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 9)] (by taint_decide_lit)

theorem update_side : VG.X86_64.Scrub.scrubSideG updF.code updF.stack updF.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 9)]) (Impl.Scrub.X86_64.chunksA updF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 9)])) [] = true := by
  lit_decide

def update : Proof.Pbkdf2.Md.X86_64.StreamFnS updF.api := ⟨updF, (updOutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(8, 9)], update_ok, update_side⟩, rfl⟩

theorem finalize_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init finF.api.sig finF.stack []) finF.code h).any
      (VG.X86_64.RScrub.resOkB · finF.stack (Impl.Scrub.X86_64.runKs [(8, 9)])
        (Impl.Scrub.X86_64.chunksA finF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 9)] (by taint_decide_lit)

theorem finalize_side : VG.X86_64.Scrub.scrubSideG finF.code finF.stack finF.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 9)]) (Impl.Scrub.X86_64.chunksA finF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 9)])) [] = true := by
  lit_decide

def finalize : Proof.Pbkdf2.Md.X86_64.StreamFnS finF.api := ⟨finF, (finOutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(8, 9)], finalize_ok, finalize_side⟩, rfl⟩

theorem digest_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init digF.api.sig digF.stack []) digF.code h).any
      (VG.X86_64.RScrub.resOkB · digF.stack (Impl.Scrub.X86_64.runKs [(200, 9)])
        (Impl.Scrub.X86_64.chunksA digF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(200, 9)] (by taint_decide_lit)

theorem digest_side : VG.X86_64.Scrub.scrubSideG digF.code digF.stack digF.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(200, 9)]) (Impl.Scrub.X86_64.chunksA digF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(200, 9)])) [] = true := by
  lit_decide

def digest : Proof.Pbkdf2.Md.X86_64.StreamFnS digF.api := ⟨digF, (digOutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(200, 9)], digest_ok, digest_side⟩, rfl⟩

theorem finalize384_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init fin384F.api.sig fin384F.stack []) fin384F.code h).any
      (VG.X86_64.RScrub.resOkB · fin384F.stack (Impl.Scrub.X86_64.runKs [(8, 9)])
        (Impl.Scrub.X86_64.chunksA fin384F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 9)] (by taint_decide_lit)

theorem finalize384_side : VG.X86_64.Scrub.scrubSideG fin384F.code fin384F.stack fin384F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 9)]) (Impl.Scrub.X86_64.chunksA fin384F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 9)])) [] = true := by
  lit_decide

def finalize384 : Proof.Pbkdf2.Md.X86_64.StreamFnS fin384F.api := ⟨fin384F, (fin384OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(8, 9)], finalize384_ok, finalize384_side⟩, rfl⟩

theorem digest384_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init dig384F.api.sig dig384F.stack []) dig384F.code h).any
      (VG.X86_64.RScrub.resOkB · dig384F.stack (Impl.Scrub.X86_64.runKs [(200, 9)])
        (Impl.Scrub.X86_64.chunksA dig384F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(200, 9)] (by taint_decide_lit)

theorem digest384_side : VG.X86_64.Scrub.scrubSideG dig384F.code dig384F.stack dig384F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(200, 9)]) (Impl.Scrub.X86_64.chunksA dig384F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(200, 9)])) [] = true := by
  lit_decide

def digest384 : Proof.Pbkdf2.Md.X86_64.StreamFnS dig384F.api := ⟨dig384F, (dig384OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(200, 9)], digest384_ok, digest384_side⟩, rfl⟩

theorem finalize512_256_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init fin512_256F.api.sig fin512_256F.stack []) fin512_256F.code h).any
      (VG.X86_64.RScrub.resOkB · fin512_256F.stack (Impl.Scrub.X86_64.runKs [(8, 9)])
        (Impl.Scrub.X86_64.chunksA fin512_256F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 9)] (by taint_decide_lit)

theorem finalize512_256_side : VG.X86_64.Scrub.scrubSideG fin512_256F.code fin512_256F.stack fin512_256F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 9)]) (Impl.Scrub.X86_64.chunksA fin512_256F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 9)])) [] = true := by
  lit_decide

def finalize512_256 : Proof.Pbkdf2.Md.X86_64.StreamFnS fin512_256F.api := ⟨fin512_256F, (fin512_256OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(8, 9)], finalize512_256_ok, finalize512_256_side⟩, rfl⟩

theorem digest512_256_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init dig512_256F.api.sig dig512_256F.stack []) dig512_256F.code h).any
      (VG.X86_64.RScrub.resOkB · dig512_256F.stack (Impl.Scrub.X86_64.runKs [(200, 9)])
        (Impl.Scrub.X86_64.chunksA dig512_256F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(200, 9)] (by taint_decide_lit)

theorem digest512_256_side : VG.X86_64.Scrub.scrubSideG dig512_256F.code dig512_256F.stack dig512_256F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(200, 9)]) (Impl.Scrub.X86_64.chunksA dig512_256F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(200, 9)])) [] = true := by
  lit_decide

def digest512_256 : Proof.Pbkdf2.Md.X86_64.StreamFnS dig512_256F.api := ⟨dig512_256F, (dig512_256OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(200, 9)], digest512_256_ok, digest512_256_side⟩, rfl⟩

theorem finalize512_224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init fin512_224F.api.sig fin512_224F.stack []) fin512_224F.code h).any
      (VG.X86_64.RScrub.resOkB · fin512_224F.stack (Impl.Scrub.X86_64.runKs [(8, 9)])
        (Impl.Scrub.X86_64.chunksA fin512_224F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 9)] (by taint_decide_lit)

theorem finalize512_224_side : VG.X86_64.Scrub.scrubSideG fin512_224F.code fin512_224F.stack fin512_224F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 9)]) (Impl.Scrub.X86_64.chunksA fin512_224F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 9)])) [] = true := by
  lit_decide

def finalize512_224 : Proof.Pbkdf2.Md.X86_64.StreamFnS fin512_224F.api := ⟨fin512_224F, (fin512_224OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(8, 9)], finalize512_224_ok, finalize512_224_side⟩, rfl⟩

theorem digest512_224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init dig512_224F.api.sig dig512_224F.stack []) dig512_224F.code h).any
      (VG.X86_64.RScrub.resOkB · dig512_224F.stack (Impl.Scrub.X86_64.runKs [(200, 9)])
        (Impl.Scrub.X86_64.chunksA dig512_224F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(200, 9)] (by taint_decide_lit)

theorem digest512_224_side : VG.X86_64.Scrub.scrubSideG dig512_224F.code dig512_224F.stack dig512_224F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(200, 9)]) (Impl.Scrub.X86_64.chunksA dig512_224F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(200, 9)])) [] = true := by
  lit_decide

def digest512_224 : Proof.Pbkdf2.Md.X86_64.StreamFnS dig512_224F.api := ⟨dig512_224F, (dig512_224OutS compress (.inr rfl) Proof.Sha512.X86_64.Stream.scalar_verified192), ⟨.sse, [(200, 9)], digest512_224_ok, digest512_224_side⟩, rfl⟩

end Scrub

/-- SHA-384 with this compression function. -/
def variant384 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha384 compress

/-- SHA-384's `finalize` and one-shot `digest` with this compression function,
with their cleanup, for its registration file. -/
def streams384 : Proof.Pbkdf2.Md.X86_64.StreamFns2 Spec.Sha512.finalize384Api Spec.Sha512.digest384Api :=
  ⟨variant384.suffix, finalize384, digest384⟩

theorem fin384_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant384.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant384.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant384.H) .r8 variant384.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant384.H) (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant384.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 9), (304, 5)] (by taint_decide_lit)

theorem fin384_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant384.H) .r8 variant384.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant384.H) ((Spec.Hmac.finalizeSig variant384.I.S).retBits 64) .sse true
    (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant384.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant384`, with what its cleanup needs. -/
def fin384 : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant384, by decide, ⟨.sse, [(16, 9), (304, 5)], fin384_ok, fin384_side⟩⟩

/-- SHA-512 with this compression function. -/
def variant512 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 compress

/-- The streaming `update` and `finalize`, and SHA-512's one-shot `digest`, made
with this compression function, with their cleanup, for its registration file.
Ed25519's key-pair generation calls the digest's code as the internal
`vg_sha512_digest<suffix>_core`. -/
def streams512 : Proof.Pbkdf2.Md.X86_64.StreamFns Spec.Sha512.updateApi Spec.Sha512.finalizeApi Spec.Sha512.digest512Api :=
  ⟨variant512.suffix, update, finalize, digest⟩

theorem fin512_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant512.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant512.H) .r8 variant512.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512.H) (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 9), (304, 5)] (by taint_decide_lit)

theorem fin512_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant512.H) .r8 variant512.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512.H) ((Spec.Hmac.finalizeSig variant512.I.S).retBits 64) .sse true
    (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant512`, with what its cleanup needs. -/
def fin512 : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant512, by decide, ⟨.sse, [(16, 9), (304, 5)], fin512_ok, fin512_side⟩⟩

/-- SHA-512/224 with this compression function. -/
def variant512_224 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_224 compress

/-- SHA-512/224's `finalize` and one-shot `digest` with this compression function,
with their cleanup, for its registration file. -/
def streams512_224 : Proof.Pbkdf2.Md.X86_64.StreamFns2 Spec.Sha512.finalize512_224Api Spec.Sha512.digest512_224Api :=
  ⟨variant512_224.suffix, finalize512_224, digest512_224⟩

theorem fin512_224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant512_224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_224.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_224.H) .r8 variant512_224.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_224.H) (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_224.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 9), (304, 5)] (by taint_decide_lit)

theorem fin512_224_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_224.H) .r8 variant512_224.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_224.H) ((Spec.Hmac.finalizeSig variant512_224.I.S).retBits 64) .sse true
    (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_224.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant512_224`, with what its cleanup needs. -/
def fin512_224 : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant512_224, by decide, ⟨.sse, [(16, 9), (304, 5)], fin512_224_ok, fin512_224_side⟩⟩

/-- SHA-512/256 with this compression function. -/
def variant512_256 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 compress

/-- SHA-512/256's `finalize` and one-shot `digest` with this compression function,
with their cleanup, for its registration file. -/
def streams512_256 : Proof.Pbkdf2.Md.X86_64.StreamFns2 Spec.Sha512.finalize512_256Api Spec.Sha512.digest512_256Api :=
  ⟨variant512_256.suffix, finalize512_256, digest512_256⟩

theorem fin512_256_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant512_256.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_256.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_256.H) .r8 variant512_256.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_256.H) (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_256.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 9), (304, 5)] (by taint_decide_lit)

theorem fin512_256_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_256.H) .r8 variant512_256.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_256.H) ((Spec.Hmac.finalizeSig variant512_256.I.S).retBits 64) .sse true
    (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant512_256.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 9), (304, 5)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant512_256`, with what its cleanup needs. -/
def fin512_256 : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant512_256, by decide, ⟨.sse, [(16, 9), (304, 5)], fin512_256_ok, fin512_256_side⟩⟩

end VG.Proof.Variants.MdHash.X86_64.Sha512
