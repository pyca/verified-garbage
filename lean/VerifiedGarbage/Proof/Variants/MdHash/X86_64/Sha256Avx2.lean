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
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Rounds
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
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Rounds
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
  okS := Proof.Sha256.X86_64.Stream.callee ok
  mxcsr := by change Impl.Sha256.X86_64.Avx2.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_spTest (by change Impl.Sha256.X86_64.Avx2.compress.allInstrs _ = true; lit_decide)
  suffix := "_avx2"
  features := ["avx", "avx2", "bmi1", "bmi2"]

section Scrub

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha256 VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## Without secret residue

Each function, followed by its cleanup (`StreamFnS.reg`): what the cleanup
needs of its code, evaluated here once, the runs of granules of its stack
that the residue analysis (`X86_64.RTaint`) finds may hold secrets, and its
other conditions (`X86_64.Scrub.SelScrub`). -/

theorem update_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (updFn compress).api.sig (updFn compress).stack []) (updFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (updFn compress).stack (Impl.Scrub.X86_64.runKs [(8, 33)])
        (Impl.Scrub.X86_64.chunksA (updFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 33)] (by taint_decide_lit)

theorem update_side : VG.X86_64.Scrub.scrubSideG (updFn compress).code (updFn compress).stack (updFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(8, 33)]) (Impl.Scrub.X86_64.chunksA (updFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 33)])) [] = true := by
  lit_decide

def update : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(updFn compress), (updOut compress), ⟨.avx, [(8, 33)], update_ok, update_side⟩⟩
theorem finalize_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (finFn compress).api.sig (finFn compress).stack []) (finFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (finFn compress).stack (Impl.Scrub.X86_64.runKs [(8, 33)])
        (Impl.Scrub.X86_64.chunksA (finFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 33)] (by taint_decide_lit)

theorem finalize_side : VG.X86_64.Scrub.scrubSideG (finFn compress).code (finFn compress).stack (finFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(8, 33)]) (Impl.Scrub.X86_64.chunksA (finFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 33)])) [] = true := by
  lit_decide

def finalize : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(finFn compress), (finOut compress), ⟨.avx, [(8, 33)], finalize_ok, finalize_side⟩⟩
theorem digest_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (digFn compress).api.sig (digFn compress).stack []) (digFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (digFn compress).stack (Impl.Scrub.X86_64.runKs [(104, 33)])
        (Impl.Scrub.X86_64.chunksA (digFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(104, 33)] (by taint_decide_lit)

theorem digest_side : VG.X86_64.Scrub.scrubSideG (digFn compress).code (digFn compress).stack (digFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(104, 33)]) (Impl.Scrub.X86_64.chunksA (digFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(104, 33)])) [] = true := by
  lit_decide

def digest : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(digFn compress), (digOut compress), ⟨.avx, [(104, 33)], digest_ok, digest_side⟩⟩

/-! SHA-224's `finalize` and `digest`, with the same compression function. -/

theorem finalize224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (Sha224.finFn compress).api.sig (Sha224.finFn compress).stack []) (Sha224.finFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (Sha224.finFn compress).stack (Impl.Scrub.X86_64.runKs [(8, 33)])
        (Impl.Scrub.X86_64.chunksA (Sha224.finFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 33)] (by taint_decide_lit)

theorem finalize224_side : VG.X86_64.Scrub.scrubSideG (Sha224.finFn compress).code (Sha224.finFn compress).stack (Sha224.finFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(8, 33)]) (Impl.Scrub.X86_64.chunksA (Sha224.finFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 33)])) [] = true := by
  lit_decide

def finalize224 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(Sha224.finFn compress), (Sha224.finOut compress), ⟨.avx, [(8, 33)], finalize224_ok, finalize224_side⟩⟩
theorem digest224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (Sha224.digFn compress).api.sig (Sha224.digFn compress).stack []) (Sha224.digFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (Sha224.digFn compress).stack (Impl.Scrub.X86_64.runKs [(104, 33)])
        (Impl.Scrub.X86_64.chunksA (Sha224.digFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(104, 33)] (by taint_decide_lit)

theorem digest224_side : VG.X86_64.Scrub.scrubSideG (Sha224.digFn compress).code (Sha224.digFn compress).stack (Sha224.digFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(104, 33)]) (Impl.Scrub.X86_64.chunksA (Sha224.digFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(104, 33)])) [] = true := by
  lit_decide

def digest224 : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(Sha224.digFn compress), (Sha224.digOut compress), ⟨.avx, [(104, 33)], digest224_ok, digest224_side⟩⟩

end Scrub

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha256.variant compress [update, finalize, digest]

theorem fin_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) (Impl.Scrub.X86_64.runKs [(16, 33), (672, 3)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 33), (672, 3)] (by taint_decide_lit)

theorem fin_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) ((Spec.Hmac.finalizeSig variant.I.S).retBits 64) .avx true
    (Impl.Scrub.X86_64.runKs [(16, 33), (672, 3)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 33), (672, 3)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant`, with what its cleanup needs. -/
def fin : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant, by decide, ⟨.avx, [(16, 33), (672, 3)], fin_ok, fin_side⟩⟩

/-- SHA-224 with this compression function, its `finalize` and `digest`
without secret residue. -/
def variant224 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha224.variant compress [finalize224, digest224]

theorem fin224_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant224.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) .r8 variant224.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) (Impl.Scrub.X86_64.runKs [(16, 33), (672, 3)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(16, 33), (672, 3)] (by taint_decide_lit)

theorem fin224_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) .r8 variant224.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H) ((Spec.Hmac.finalizeSig variant224.I.S).retBits 64) .avx true
    (Impl.Scrub.X86_64.runKs [(16, 33), (672, 3)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant224.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(16, 33), (672, 3)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant224`, with what its cleanup needs. -/
def fin224 : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant224, by decide, ⟨.avx, [(16, 33), (672, 3)], fin224_ok, fin224_side⟩⟩

end VG.Proof.Variants.MdHash.X86_64.Sha256Avx2
