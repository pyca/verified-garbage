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

Each function, followed by its cleanup (`StreamFnS.reg`): what the cleanup
needs of its code, evaluated here once, the runs of granules of its stack
that the residue analysis (`X86_64.RTaint`) finds may hold secrets, and its
other conditions (`X86_64.Scrub.SelScrub`). -/

theorem update_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (updFn compress).api.sig (updFn compress).stack []) (updFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (updFn compress).stack (Impl.Scrub.X86_64.runKs [(8, 5)])
        (Impl.Scrub.X86_64.chunksA (updFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 5)] (by taint_decide_lit)

theorem update_side : VG.X86_64.Scrub.scrubSideG (updFn compress).code (updFn compress).stack (updFn compress).retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 5)]) (Impl.Scrub.X86_64.chunksA (updFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 5)])) [] = true := by
  lit_decide

def update : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(updFn compress), (updOut compress), ⟨.sse, [(8, 5)], update_ok, update_side⟩⟩

theorem finalize_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (finFn compress).api.sig (finFn compress).stack []) (finFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (finFn compress).stack (Impl.Scrub.X86_64.runKs [(8, 5)])
        (Impl.Scrub.X86_64.chunksA (finFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 5)] (by taint_decide_lit)

theorem finalize_side : VG.X86_64.Scrub.scrubSideG (finFn compress).code (finFn compress).stack (finFn compress).retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 5)]) (Impl.Scrub.X86_64.chunksA (finFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 5)])) [] = true := by
  lit_decide

def finalize : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(finFn compress), (finOut compress), ⟨.sse, [(8, 5)], finalize_ok, finalize_side⟩⟩

theorem digest_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (digFn compress).api.sig (digFn compress).stack []) (digFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (digFn compress).stack (Impl.Scrub.X86_64.runKs [(104, 5)])
        (Impl.Scrub.X86_64.chunksA (digFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(104, 5)] (by taint_decide_lit)

theorem digest_side : VG.X86_64.Scrub.scrubSideG (digFn compress).code (digFn compress).stack (digFn compress).retBits .sse true
    (Impl.Scrub.X86_64.runKs [(104, 5)]) (Impl.Scrub.X86_64.chunksA (digFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(104, 5)])) [] = true := by
  lit_decide

def digest : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(digFn compress), (digOut compress), ⟨.sse, [(104, 5)], digest_ok, digest_side⟩⟩

end Scrub

/-- `variant` before the residue analysis of HMAC's `finalize`. -/
def unscrubbed : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha1.variant compress [update, finalize, digest]

/-- HMAC's `finalize` over `unscrubbed`, followed by `Impl.Scrub.X86_64.scrubTail`,
which wipes the registers and the granules of its stack that the residue
analysis of its code finds may hold secrets (`MdHash.hmacFinReg`). -/
def hmacFinKs : List Nat := keep_for% unscrubbed.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.H)
  (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.H) .r8
      unscrubbed.H.hmacFin) []

theorem hmacFinOk : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init unscrubbed.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.H) .r8
      unscrubbed.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.H) hmacFinKs (Impl.Scrub.X86_64.chunks (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame unscrubbed.H))) = true :=
  VG.X86_64.RScrub.Analysed.ok_of hmacFinKs (by taint_decide_lit)

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { unscrubbed with hmacFinRes := some ⟨hmacFinKs, hmacFinOk⟩ }

end VG.Proof.Variants.MdHash.X86_64.Sha1
