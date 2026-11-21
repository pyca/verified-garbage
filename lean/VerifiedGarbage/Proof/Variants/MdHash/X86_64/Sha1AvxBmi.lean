module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1Scrub
import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1Scrub
public meta import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Compress
public meta import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SHA-1 on x86-64 with AVX and BMI: the variant's code and proofs

The variant `VG.Variants.MdHash.X86_64.Sha1AvxBmi.variant`
(`Variants/MdHash/X86_64/Sha1AvxBmi.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha1AvxBmi

open VG.Impl.Sha1.X86_64.Stream (Callee)

theorem ok : MdStream.X86_64.CalleeOk (P := Proof.Sha1.X86_64.Stream.params) Proof.Sha1.md
    Callee.avxBmi.code :=
  .of_verified Proof.Sha1.X86_64.AvxBmi.compress_verified.1
    Proof.Sha1.X86_64.AvxBmi.compress_verified.2.1
    (by change (instrs Impl.Sha1.X86_64.AvxBmi.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha1.X86_64.AvxBmi.compress.depth = 0; lit_decide)

/-- The compression function with AVX and BMI. -/
def compress : Proof.Sha1.X86_64.Compress where
  callee := .avxBmi
  ok := ok
  okS := ok
  mxcsr := by change Impl.Sha1.X86_64.AvxBmi.compress.allInstrs _ = true; lit_decide
  spSafe := Code.all_of_spTest (by change Impl.Sha1.X86_64.AvxBmi.compress.allInstrs _ = true; lit_decide)
  noStack := by change Impl.Sha1.X86_64.AvxBmi.compress.x86_64Depth = 0; lit_decide
  suffix := "_avx_bmi"
  features := ["avx", "bmi1", "bmi2"]

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

theorem update_side : VG.X86_64.Scrub.scrubSideG (updFn compress).code (updFn compress).stack (updFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(8, 5)]) (Impl.Scrub.X86_64.chunksA (updFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 5)])) [] = true := by
  lit_decide

def update : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(updFn compress), (updOut compress), ⟨.avx, [(8, 5)], update_ok, update_side⟩⟩

theorem finalize_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (finFn compress).api.sig (finFn compress).stack []) (finFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (finFn compress).stack (Impl.Scrub.X86_64.runKs [(8, 5)])
        (Impl.Scrub.X86_64.chunksA (finFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(8, 5)] (by taint_decide_lit)

theorem finalize_side : VG.X86_64.Scrub.scrubSideG (finFn compress).code (finFn compress).stack (finFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(8, 5)]) (Impl.Scrub.X86_64.chunksA (finFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(8, 5)])) [] = true := by
  lit_decide

def finalize : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(finFn compress), (finOut compress), ⟨.avx, [(8, 5)], finalize_ok, finalize_side⟩⟩

theorem digest_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init (digFn compress).api.sig (digFn compress).stack []) (digFn compress).code h).any
      (VG.X86_64.RScrub.resOkB · (digFn compress).stack (Impl.Scrub.X86_64.runKs [(104, 5)])
        (Impl.Scrub.X86_64.chunksA (digFn compress).stack)) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(104, 5)] (by taint_decide_lit)

theorem digest_side : VG.X86_64.Scrub.scrubSideG (digFn compress).code (digFn compress).stack (digFn compress).retBits .avx true
    (Impl.Scrub.X86_64.runKs [(104, 5)]) (Impl.Scrub.X86_64.chunksA (digFn compress).stack)
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(104, 5)])) [] = true := by
  lit_decide

def digest : Proof.Pbkdf2.Md.X86_64.StreamFnS := ⟨(digFn compress), (digOut compress), ⟨.avx, [(104, 5)], digest_ok, digest_side⟩⟩

end Scrub

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha1.variant compress [update, finalize, digest]

theorem fin_ok : ∃ h : VG.Taint.Hint VG.X86_64.RTaint.FT,
    (VG.Taint.check VG.X86_64.RTaint.rtaint (VG.X86_64.RScrub.init variant.I.finalizeApi.sig (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) [])
      (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin) h).any
      (VG.X86_64.RScrub.resOkB · (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) (Impl.Scrub.X86_64.runKs [(24, 4), (232, 2)])
        (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))) = true :=
  VG.X86_64.Scrub.SelScrub.ok_of [(24, 4), (232, 2)] (by taint_decide_lit)

theorem fin_side : VG.X86_64.Scrub.scrubSideG
    (Impl.StackScratch.X86_64.withStackScratch (Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) .r8 variant.H.hmacFin)
    (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H) ((Spec.Hmac.finalizeSig variant.I.S).retBits 64) .avx true
    (Impl.Scrub.X86_64.runKs [(24, 4), (232, 2)]) (Impl.Scrub.X86_64.chunksA (16 + Proof.Pbkdf2.Md.X86_64.hmacFrame variant.H))
    (Impl.Scrub.X86_64.gsAll (Impl.Scrub.X86_64.runKs [(24, 4), (232, 2)])) [] = true := by
  lit_decide

/-- HMAC's `finalize` over `variant`, with what its cleanup needs. -/
def fin : Proof.Pbkdf2.Md.X86_64.FinImpl := ⟨variant, by decide, ⟨.avx, [(24, 4), (232, 2)], fin_ok, fin_side⟩⟩

end VG.Proof.Variants.MdHash.X86_64.Sha1AvxBmi
