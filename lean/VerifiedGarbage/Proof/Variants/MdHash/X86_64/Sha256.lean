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
  okS := Proof.Sha256.X86_64.Stream.calleeS Proof.Sha256.X86_64.Stream.scalar_ok
    Proof.Sha256.X86_64.Stream.scalar_verified112
  mxcsr := by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_spTest (by change Impl.Sha256.X86_64.compress.allInstrs _ = true; lit_decide)
  level := .sse
  side := by change X86_64.Scrub.calleeSide Impl.Sha256.X86_64.compress _ 0 = true; lit_decide
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

Each function, followed by its cleanup (`StreamFnS.reg`): what the cleanup
needs of its code, evaluated here once, the runs of granules of its stack
that the residue analysis (`X86_64.RTaint`) finds may hold secrets, and its
other conditions (`X86_64.Scrub.SelScrub`). -/

theorem update_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init updF.api.sig updF.stack []) updF.code h).any
      (VG.X86_64.RScrub.resOkB · updF.stack (Impl.Scrub.X86_64.runKs [(8, 5)])
        (Impl.Scrub.X86_64.chunksA updF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 5)] (by taint_decide_lit)

theorem update_side : VG.X86_64.Scrub.scrubSideG updF.code updF.stack updF.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 5)]) (Impl.Scrub.X86_64.chunksA updF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 5)])) [] = true := by
  lit_decide

def update : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨updF, (updOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112), ⟨.sse, [(8, 5)], update_ok, update_side⟩⟩
theorem finalize_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init finF.api.sig finF.stack []) finF.code h).any
      (VG.X86_64.RScrub.resOkB · finF.stack (Impl.Scrub.X86_64.runKs [(8, 5)])
        (Impl.Scrub.X86_64.chunksA finF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 5)] (by taint_decide_lit)

theorem finalize_side : VG.X86_64.Scrub.scrubSideG finF.code finF.stack finF.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 5)]) (Impl.Scrub.X86_64.chunksA finF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 5)])) [] = true := by
  lit_decide

def finalize : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨finF, (finOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112), ⟨.sse, [(8, 5)], finalize_ok, finalize_side⟩⟩
theorem digest_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init digF.api.sig digF.stack []) digF.code h).any
      (VG.X86_64.RScrub.resOkB · digF.stack (Impl.Scrub.X86_64.runKs [(104, 5)])
        (Impl.Scrub.X86_64.chunksA digF.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(104, 5)] (by taint_decide_lit)

theorem digest_side : VG.X86_64.Scrub.scrubSideG digF.code digF.stack digF.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(104, 5)]) (Impl.Scrub.X86_64.chunksA digF.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(104, 5)])) [] = true := by
  lit_decide

def digest : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨digF, (digOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112), ⟨.sse, [(104, 5)], digest_ok, digest_side⟩⟩

/-! SHA-224's `finalize` and `digest`, with the same compression function. -/

theorem finalize224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init fin224F.api.sig fin224F.stack []) fin224F.code h).any
      (VG.X86_64.RScrub.resOkB · fin224F.stack (Impl.Scrub.X86_64.runKs [(8, 5)])
        (Impl.Scrub.X86_64.chunksA fin224F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 5)] (by taint_decide_lit)

theorem finalize224_side : VG.X86_64.Scrub.scrubSideG fin224F.code fin224F.stack fin224F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(8, 5)]) (Impl.Scrub.X86_64.chunksA fin224F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 5)])) [] = true := by
  lit_decide

def finalize224 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨fin224F, (Sha224.finOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112), ⟨.sse, [(8, 5)], finalize224_ok, finalize224_side⟩⟩
theorem digest224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init dig224F.api.sig dig224F.stack []) dig224F.code h).any
      (VG.X86_64.RScrub.resOkB · dig224F.stack (Impl.Scrub.X86_64.runKs [(104, 5)])
        (Impl.Scrub.X86_64.chunksA dig224F.stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(104, 5)] (by taint_decide_lit)

theorem digest224_side : VG.X86_64.Scrub.scrubSideG dig224F.code dig224F.stack dig224F.retBits .sse true
    (Impl.Scrub.X86_64.runKs [(104, 5)]) (Impl.Scrub.X86_64.chunksA dig224F.stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(104, 5)])) [] = true := by
  lit_decide

def digest224 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨dig224F, (Sha224.digOutS compress (.inr rfl) Proof.Sha256.X86_64.Stream.scalar_verified112), ⟨.sse, [(104, 5)], digest224_ok, digest224_side⟩⟩

end Scrub

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha256.variant compress [update, finalize, digest]

theorem fin_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) (Impl.Scrub.X86_64.runKs [(16, 5), (224, 3)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 5), (224, 3)] (by taint_decide_lit)

theorem fin_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) ((Spec.Hmac.finalizeSig variant.I.S).retBits 64) .sse true
    (Impl.Scrub.X86_64.runKs [(16, 5), (224, 3)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 5), (224, 3)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant`, with what its cleanup needs. -/
def fin : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant, by decide, ⟨.sse, [(16, 5), (224, 3)], fin_ok, fin_side⟩⟩

/-- SHA-224 with this compression function, its `finalize` and `digest`
without secret residue. -/
def variant224 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha224.variant compress [finalize224, digest224]

theorem fin224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) .r8 variant224.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) (Impl.Scrub.X86_64.runKs [(16, 5), (224, 3)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 5), (224, 3)] (by taint_decide_lit)

theorem fin224_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) .r8 variant224.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) ((Spec.Hmac.finalizeSig variant224.I.S).retBits 64) .sse true
    (Impl.Scrub.X86_64.runKs [(16, 5), (224, 3)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 5), (224, 3)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant224`, with what its cleanup needs. -/
def fin224 : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant224, by decide, ⟨.sse, [(16, 5), (224, 3)], fin224_ok, fin224_side⟩⟩

end VG.Proof.Variants.MdHash.X86_64.Sha256
