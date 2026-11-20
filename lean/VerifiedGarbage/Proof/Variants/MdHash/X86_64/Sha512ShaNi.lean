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

/-! ## The functions with the working space this compression function uses

The compression function uses no scratch space: the streaming and one-shot
functions give it none (`Sha512.updFnS`). -/

abbrev updF : StreamFn := updFnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev finF : StreamFn := finFnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev digF : StreamFn := digFnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev fin384F : StreamFn := fin384FnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev dig384F : StreamFn := dig384FnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev fin512_256F : StreamFn := fin512_256FnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev dig512_256F : StreamFn := dig512_256FnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev fin512_224F : StreamFn := fin512_224FnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0
abbrev dig512_224F : StreamFn := dig512_224FnS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0

/-! ## Without secret residue

Each function, followed by its cleanup (`StreamFnS.reg`): what the cleanup
needs of its code, evaluated here once, the runs of granules of its stack
that the residue analysis (`X86_64.RTaint`) finds may hold secrets, and its
other conditions (`X86_64.Scrub.SelScrub`). -/

theorem update_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init updF.api.sig updF.stack []) updF.code h).any
      (VG.X86_64.RScrub.resOkB · updF.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA updF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem update_side : VG.X86_64.Scrub.scrubSideG updF.code updF.stack updF.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA updF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def update : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨updF, (updOutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], update_ok, update_side⟩⟩

theorem finalize_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init finF.api.sig finF.stack []) finF.code h).any
      (VG.X86_64.RScrub.resOkB · finF.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA finF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem finalize_side : VG.X86_64.Scrub.scrubSideG finF.code finF.stack finF.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA finF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def finalize : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨finF, (finOutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], finalize_ok, finalize_side⟩⟩

theorem digest_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init digF.api.sig digF.stack []) digF.code h).any
      (VG.X86_64.RScrub.resOkB · digF.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA digF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem digest_side : VG.X86_64.Scrub.scrubSideG digF.code digF.stack digF.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA digF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def digest : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨digF, (digOutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], digest_ok, digest_side⟩⟩

theorem finalize384_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init fin384F.api.sig fin384F.stack []) fin384F.code h).any
      (VG.X86_64.RScrub.resOkB · fin384F.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA fin384F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem finalize384_side : VG.X86_64.Scrub.scrubSideG fin384F.code fin384F.stack fin384F.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA fin384F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def finalize384 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨fin384F, (fin384OutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], finalize384_ok, finalize384_side⟩⟩

theorem digest384_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init dig384F.api.sig dig384F.stack []) dig384F.code h).any
      (VG.X86_64.RScrub.resOkB · dig384F.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA dig384F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem digest384_side : VG.X86_64.Scrub.scrubSideG dig384F.code dig384F.stack dig384F.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA dig384F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def digest384 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨dig384F, (dig384OutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], digest384_ok, digest384_side⟩⟩

theorem finalize512_256_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init fin512_256F.api.sig fin512_256F.stack []) fin512_256F.code h).any
      (VG.X86_64.RScrub.resOkB · fin512_256F.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA fin512_256F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem finalize512_256_side : VG.X86_64.Scrub.scrubSideG fin512_256F.code fin512_256F.stack fin512_256F.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA fin512_256F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def finalize512_256 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨fin512_256F, (fin512_256OutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], finalize512_256_ok, finalize512_256_side⟩⟩

theorem digest512_256_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init dig512_256F.api.sig dig512_256F.stack []) dig512_256F.code h).any
      (VG.X86_64.RScrub.resOkB · dig512_256F.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA dig512_256F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem digest512_256_side : VG.X86_64.Scrub.scrubSideG dig512_256F.code dig512_256F.stack dig512_256F.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA dig512_256F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def digest512_256 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨dig512_256F, (dig512_256OutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], digest512_256_ok, digest512_256_side⟩⟩

theorem finalize512_224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init fin512_224F.api.sig fin512_224F.stack []) fin512_224F.code h).any
      (VG.X86_64.RScrub.resOkB · fin512_224F.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA fin512_224F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem finalize512_224_side : VG.X86_64.Scrub.scrubSideG fin512_224F.code fin512_224F.stack fin512_224F.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA fin512_224F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def finalize512_224 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨fin512_224F, (fin512_224OutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], finalize512_224_ok, finalize512_224_side⟩⟩

theorem digest512_224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init dig512_224F.api.sig dig512_224F.stack []) dig512_224F.code h).any
      (VG.X86_64.RScrub.resOkB · dig512_224F.stack (Impl.Scrub.X86_64.runKs [])
        (Impl.Scrub.X86_64.chunksA dig512_224F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [] (by taint_decide_lit)

theorem digest512_224_side : VG.X86_64.Scrub.scrubSideG dig512_224F.code dig512_224F.stack dig512_224F.retBits .avx true
    (Impl.Scrub.X86_64.runKs []) (Impl.Scrub.X86_64.chunksA dig512_224F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [])) [] = true := by
  lit_decide

def digest512_224 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨dig512_224F, (dig512_224OutS compress (.inl rfl) Proof.Sha512.X86_64.Stream.shani_verified0), ⟨.avx, [], digest512_224_ok, digest512_224_side⟩⟩

end Scrub

/-- The streaming `update` and `finalize`, and SHA-512's one-shot `digest`.
Ed25519's key-pair generation calls the digest's code as the internal
`vg_sha512_digest<suffix>_core`. -/
def stream : List Proof.Pbkdf2.Md.X86_64.StreamFnS := [update, finalize, digest]

/-- SHA-384's `finalize` and one-shot `digest`. -/
def stream384 : List Proof.Pbkdf2.Md.X86_64.StreamFnS := [finalize384, digest384]

/-- SHA-512/256's `finalize` and one-shot `digest`. -/
def stream512_256 : List Proof.Pbkdf2.Md.X86_64.StreamFnS := [finalize512_256, digest512_256]

/-- SHA-512/224's `finalize` and one-shot `digest`. -/
def stream512_224 : List Proof.Pbkdf2.Md.X86_64.StreamFnS := [finalize512_224, digest512_224]

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

end VG.Proof.Variants.MdHash.X86_64.Sha512ShaNi
