module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Pbkdf2.Scratch
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Pbkdf2.Scratch
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit

/-!
# PBKDF2-HMAC on x86 (32-bit), without secret residue

`vg_pbkdf2_hmac_<hash>` runs in a frame that holds its working space
(`Frame.lean`), and the functions it calls use the stack below it, all
within the `76 + pbkFrame I` bytes its contract reserves. Each is followed by
the zeroing of those bytes below `esp` and the clearing of the registers a
callee may change (`X86.Scrub.scrubFOf`). Its postcondition reads the memory
on return only within `out` (`pbkdf2Out`, from
`Proof.Pbkdf2.pbkdf2PostOut_local`).

MD5 and the SHA-512 family have one implementation each, whose code the
kernel evaluates here. SHA-1, SHA-224 and SHA-256 are generic over their
backends (`Proof/Variants/Sha1/X86.lean`, `Proof/Variants/Sha256/X86.lean`):
their code with a stub backend, whose compression, `update` and `finalize`
are `.block []`, is evaluated once (`sha1_side`, …), and `Fill` gives the
same of every backend from its own facts (`Backend.cmpScrub`, `updScrub`,
`finScrub` and its stacks), with no evaluation of its code
(`Proof/Framework/X86/ScrubCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86.Scrub

open VG.X86 VG.X86.Scrub
open Impl.StackScratch.X86 (withStackScratch)

/-- PBKDF2's postcondition reads the memory on return only within `out`, the
derived key's bytes. -/
theorem pbkdf2Out (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.pbkdf2Contract X86.abi stack) (Spec.Pbkdf2.pbkdf2Sig.retBits 32) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact postOut_of_local ScrubAbi.plain (Proof.Pbkdf2.pbkdf2PostOut_local I.S 32)

/-! ## MD5 and the SHA-512 family -/

/-- `Spec.Hmac.md5I.pbkdf2Api`. -/
def md5Reg : Registration Spec.Hmac.md5I.pbkdf2Api X86.target :=
  scrubFOf {
      code := withStackScratch (pbkFrame Spec.Hmac.md5I) 7 md5F.pbkdf2
      verified := pbkFramed md5 md5_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.md5I _)

/-- `Spec.Hmac.sha384I.pbkdf2Api`. -/
def sha384Reg : Registration Spec.Hmac.sha384I.pbkdf2Api X86.target :=
  scrubFOf {
      code := withStackScratch (pbkFrame Spec.Hmac.sha384I) 7 sha384F.pbkdf2
      verified := pbkFramed sha384 sha384_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.sha384I _)

/-- `Spec.Hmac.sha512I.pbkdf2Api`. -/
def sha512Reg : Registration Spec.Hmac.sha512I.pbkdf2Api X86.target :=
  scrubFOf {
      code := withStackScratch (pbkFrame Spec.Hmac.sha512I) 7 sha512F.pbkdf2
      verified := pbkFramed sha512 sha512_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.sha512I _)

/-- `Spec.Hmac.sha512_224I.pbkdf2Api`. -/
def sha512_224Reg : Registration Spec.Hmac.sha512_224I.pbkdf2Api X86.target :=
  scrubFOf {
      code := withStackScratch (pbkFrame Spec.Hmac.sha512_224I) 7 sha512_224F.pbkdf2
      verified := pbkFramed sha512_224 sha512_224_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.sha512_224I _)

/-- `Spec.Hmac.sha512_256I.pbkdf2Api`. -/
def sha512_256Reg : Registration Spec.Hmac.sha512_256I.pbkdf2Api X86.target :=
  scrubFOf {
      code := withStackScratch (pbkFrame Spec.Hmac.sha512_256I) 7 sha512_256F.pbkdf2
      verified := pbkFramed sha512_256 sha512_256_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.sha512_256I _)

/-! ## SHA-1, SHA-224 and SHA-256, generic over their backends -/

/-- The functions PBKDF2-HMAC-SHA1 calls, with a stub backend. -/
def sha1Stub : Impl.Pbkdf2.Whole.X86.Fns := Proof.Sha1.X86.Variants.fns "" "" (.block []) (.block []) (.block [])

/-- The functions PBKDF2-HMAC-SHA256 calls, with a stub backend. -/
def sha256Stub : Impl.Pbkdf2.Whole.X86.Fns :=
  Proof.Sha256.X86.Variants.fns "" "" (.block []) (.block []) (.block [])

/-- The functions PBKDF2-HMAC-SHA224 calls, with a stub backend. -/
def sha224Stub : Impl.Pbkdf2.Whole.X86.Fns :=
  Proof.Sha256.X86.Variants.fns224 "" "" (.block []) (.block []) (.block [])

materialize_code sha1StubLit := withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 sha1Stub.pbkdf2
materialize_code sha224StubLit := withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 sha224Stub.pbkdf2
materialize_code sha256StubLit := withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 sha256Stub.pbkdf2

theorem sha1_side :
    scrubFSide (withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 sha1Stub.pbkdf2) [] (56 + pbkFrame Spec.Hmac.sha1I) = true := by
  lit_decide

theorem sha224_side :
    scrubFSide (withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 sha224Stub.pbkdf2) [] (56 + pbkFrame Spec.Hmac.sha224I) = true := by
  lit_decide

theorem sha256_side :
    scrubFSide (withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 sha256Stub.pbkdf2) [] (56 + pbkFrame Spec.Hmac.sha256I) = true := by
  lit_decide

theorem sha1_fill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 sha1Stub.pbkdf2)
      (withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 (Proof.Sha1.X86.Variants.fns sfx cN c u f).pbkdf2) := by
  fill_calls

theorem sha224_fill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 sha224Stub.pbkdf2)
      (withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 (Proof.Sha256.X86.Variants.fns224 sfx cN c u f).pbkdf2) := by
  fill_calls

theorem sha256_fill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 sha256Stub.pbkdf2)
      (withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 (Proof.Sha256.X86.Variants.fns sfx cN c u f).pbkdf2) := by
  fill_calls

/-- `scrubFSide` of PBKDF2-HMAC-SHA1, whatever the backend. -/
theorem sha1_scrub (v : Proof.Sha1.X86.Variants.Backend) :
    scrubFSide (withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 v.F.pbkdf2) [] (76 + pbkFrame Spec.Hmac.sha1I) = true :=
  scrubFSide_of_fill (sha1_fill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
    (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)) sha1_side

/-- `scrubFSide` of PBKDF2-HMAC-SHA224, whatever the backend. -/
theorem sha224_scrub (v : Proof.Sha256.X86.Variants.Backend) :
    scrubFSide (withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 v.F224.pbkdf2) [] (76 + pbkFrame Spec.Hmac.sha224I) = true :=
  scrubFSide_of_fill (sha224_fill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
    (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)) sha224_side

/-- `scrubFSide` of PBKDF2-HMAC-SHA256, whatever the backend. -/
theorem sha256_scrub (v : Proof.Sha256.X86.Variants.Backend) :
    scrubFSide (withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 v.F.pbkdf2) [] (76 + pbkFrame Spec.Hmac.sha256I) = true :=
  scrubFSide_of_fill (sha256_fill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
    (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)) sha256_side

/-- `Spec.Hmac.sha1I.pbkdf2Api` with the backend `v`. -/
def sha1Reg (v : Proof.Sha1.X86.Variants.Backend) : Registration Spec.Hmac.sha1I.pbkdf2Api X86.target :=
  scrubFOf {
      suffix := v.suffix
      code := withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 v.F.pbkdf2
      verified := pbkFramed (sha1_verified v) sha1_pbkFrameSat (noEsp_of_all v.pbkdf2Sp) (sha1_stack v)
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2Sp }
    (pbkdf2Out Spec.Hmac.sha1I _) (W := 76 + pbkFrame Spec.Hmac.sha1I) (hs := sha1_scrub v)

/-- `Spec.Hmac.sha224I.pbkdf2Api` with the backend `v`. -/
def sha224Reg (v : Proof.Sha256.X86.Variants.Backend) : Registration Spec.Hmac.sha224I.pbkdf2Api X86.target :=
  scrubFOf {
      suffix := v.suffix
      code := withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 v.F224.pbkdf2
      verified := pbkFramed (sha224_verified v) sha224_pbkFrameSat (noEsp_of_all v.pbkdf2_224Sp)
        (sha224_stack v)
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2_224Sp }
    (pbkdf2Out Spec.Hmac.sha224I _) (W := 76 + pbkFrame Spec.Hmac.sha224I) (hs := sha224_scrub v)

/-- `Spec.Hmac.sha256I.pbkdf2Api` with the backend `v`. -/
def sha256Reg (v : Proof.Sha256.X86.Variants.Backend) : Registration Spec.Hmac.sha256I.pbkdf2Api X86.target :=
  scrubFOf {
      suffix := v.suffix
      code := withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 v.F.pbkdf2
      verified := pbkFramed (sha256_verified v) sha256_pbkFrameSat (noEsp_of_all v.pbkdf2Sp) (sha256_stack v)
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2Sp }
    (pbkdf2Out Spec.Hmac.sha256I _) (W := 76 + pbkFrame Spec.Hmac.sha256I) (hs := sha256_scrub v)

end VG.Proof.Pbkdf2.Whole.X86.Scrub
