module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
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
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
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
within the `76 + pbkFrame I` bytes its contract reserves. As emitted
(`Impl.Pbkdf2.Whole.X86.Fn`), each is followed by the zeroing of those bytes
below `esp` and the clearing of the registers a callee may change
(`X86.Scrub.verifiedScrubbedAll`). Its postcondition reads the memory
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

/-- `vg_pbkdf2_hmac_md5` as emitted (`Impl.Pbkdf2.Whole.X86.Fn.md5`) meets its contract
in constant time and returns without secret residue. -/
theorem md5_scrubbed :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.md5 md5F)
      (Spec.Hmac.md5I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.md5I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.md5I.pbkdf2Api)
    { code := withStackScratch (pbkFrame Spec.Hmac.md5I) 7 md5F.pbkdf2
      verified := pbkFramed md5 md5_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.md5I _)

/-- `vg_pbkdf2_hmac_sha384` as emitted (`Impl.Pbkdf2.Whole.X86.Fn.sha512`) meets its contract
in constant time and returns without secret residue. -/
theorem sha384_scrubbed :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.sha512 sha384F)
      (Spec.Hmac.sha384I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha384I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha384I.pbkdf2Api)
    { code := withStackScratch (pbkFrame Spec.Hmac.sha384I) 7 sha384F.pbkdf2
      verified := pbkFramed sha384 sha384_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.sha384I _)

/-- `vg_pbkdf2_hmac_sha512` as emitted (`Impl.Pbkdf2.Whole.X86.Fn.sha512`) meets its contract
in constant time and returns without secret residue. -/
theorem sha512_scrubbed :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.sha512 sha512F)
      (Spec.Hmac.sha512I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha512I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512I.pbkdf2Api)
    { code := withStackScratch (pbkFrame Spec.Hmac.sha512I) 7 sha512F.pbkdf2
      verified := pbkFramed sha512 sha512_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.sha512I _)

/-- `vg_pbkdf2_hmac_sha512_224` as emitted (`Impl.Pbkdf2.Whole.X86.Fn.sha512`) meets its contract
in constant time and returns without secret residue. -/
theorem sha512_224_scrubbed :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.sha512 sha512_224F)
      (Spec.Hmac.sha512_224I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha512_224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_224I.pbkdf2Api)
    { code := withStackScratch (pbkFrame Spec.Hmac.sha512_224I) 7 sha512_224F.pbkdf2
      verified := pbkFramed sha512_224 sha512_224_pbkFrameSat }
    (pbkdf2Out Spec.Hmac.sha512_224I _)

/-- `vg_pbkdf2_hmac_sha512_256` as emitted (`Impl.Pbkdf2.Whole.X86.Fn.sha512`) meets its contract
in constant time and returns without secret residue. -/
theorem sha512_256_scrubbed :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.sha512 sha512_256F)
      (Spec.Hmac.sha512_256I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha512_256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_256I.pbkdf2Api)
    { code := withStackScratch (pbkFrame Spec.Hmac.sha512_256I) 7 sha512_256F.pbkdf2
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

private def backendFns (F : Impl.Pbkdf2.Whole.X86.Fns) (M : Impl.Pbkdf2.Md.X86.Hash)
    (cn un fn : String) (c u f : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns :=
  let H := { M.st with updN := un, updC := u, finN := fn, finC := f }
  let md := { M with st := H, compN := cn, compC := c }
  { F with H := H, hiC := md.hmacInit, hfC := md.hmacFin, itC := md.iterate }

/-- All three hashes have the same PBKDF2 and HMAC code shape. Walk it once
with the hash sizes, instruction lists and backend functions abstract. -/
private theorem backend_fill (F : Impl.Pbkdf2.Whole.X86.Fns) (M : Impl.Pbkdf2.Md.X86.Hash)
    (bytes : Nat) (cn un fn hin hfn itn : String) (c u f : Prog isa)
    (hc : calleeSide c 20 = true) (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true)
    (hinit : Fill 20 M.st.initC M.st.initC) :
    Fill 20 (withStackScratch bytes 7
      (backendFns F M M.compN M.st.updN M.st.finN (.block []) (.block []) (.block [])).pbkdf2)
      (withStackScratch bytes 7
        (backendFns { F with hiN := hin, hfN := hfn, itN := itn } M cn un fn c u f).pbkdf2) := by
  fill_calls <;> exact hinit

theorem sha1_fill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 sha1Stub.pbkdf2)
      (withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 (Proof.Sha1.X86.Variants.fns sfx cN c u f).pbkdf2) := by
  let F := (Proof.Sha1.X86.Variants.fns sfx cN c u f)
  exact backend_fill sha1Stub (Proof.Sha1.X86.Variants.mdHash "" "" (.block []) (.block []) (.block []))
    (pbkFrame Spec.Hmac.sha1I) cN F.H.updN F.H.finN F.hiN F.hfN F.itN c u f hc hu hf (by fill_calls)

theorem sha224_fill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 sha224Stub.pbkdf2)
      (withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 (Proof.Sha256.X86.Variants.fns224 sfx cN c u f).pbkdf2) := by
  let F := (Proof.Sha256.X86.Variants.fns224 sfx cN c u f)
  exact backend_fill sha224Stub (Proof.Sha256.X86.Variants.mdHash224 "" "" (.block []) (.block []) (.block []))
    (pbkFrame Spec.Hmac.sha224I) cN F.H.updN F.H.finN F.hiN F.hfN F.itN c u f hc hu hf (by fill_calls)

theorem sha256_fill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 sha256Stub.pbkdf2)
      (withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 (Proof.Sha256.X86.Variants.fns sfx cN c u f).pbkdf2) := by
  let F := (Proof.Sha256.X86.Variants.fns sfx cN c u f)
  exact backend_fill sha256Stub (Proof.Sha256.X86.Variants.mdHash "" "" (.block []) (.block []) (.block []))
    (pbkFrame Spec.Hmac.sha256I) cN F.H.updN F.H.finN F.hiN F.hfN F.itN c u f hc hu hf (by fill_calls)

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

/-- `vg_pbkdf2_hmac_sha1` with the backend `v`, as emitted (`Impl.Pbkdf2.Whole.X86.Fn.sha1`),
meets its contract in constant time and returns without secret residue. -/
theorem sha1_scrubbed (v : Proof.Sha1.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.sha1 v.F)
      (Spec.Hmac.sha1I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha1I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha1I.pbkdf2Api)
    { suffix := v.suffix
      code := withStackScratch (pbkFrame Spec.Hmac.sha1I) 7 v.F.pbkdf2
      verified := pbkFramed (sha1_verified v) sha1_pbkFrameSat (noEsp_of_all v.pbkdf2Sp) (sha1_stack v)
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2Sp }
    (pbkdf2Out Spec.Hmac.sha1I _) (hs := sha1_scrub v)

/-- No instruction of `vg_pbkdf2_hmac_sha1` with the backend `v`, as emitted, writes `esp`
but in its frames and calls. -/
theorem sha1_spSafe (v : Proof.Sha1.X86.Variants.Backend) :
    (Impl.Pbkdf2.Whole.X86.Fn.sha1 v.F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2Sp)

/-- `vg_pbkdf2_hmac_sha224` with the backend `v`, as emitted (`Impl.Pbkdf2.Whole.X86.Fn.sha256`),
meets its contract in constant time and returns without secret residue. -/
theorem sha224_scrubbed (v : Proof.Sha256.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.sha256 v.F224)
      (Spec.Hmac.sha224I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha224I.pbkdf2Api)
    { suffix := v.suffix
      code := withStackScratch (pbkFrame Spec.Hmac.sha224I) 7 v.F224.pbkdf2
      verified := pbkFramed (sha224_verified v) sha224_pbkFrameSat (noEsp_of_all v.pbkdf2_224Sp)
        (sha224_stack v)
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2_224Sp }
    (pbkdf2Out Spec.Hmac.sha224I _) (hs := sha224_scrub v)

/-- No instruction of `vg_pbkdf2_hmac_sha224` with the backend `v`, as emitted, writes `esp`
but in its frames and calls. -/
theorem sha224_spSafe (v : Proof.Sha256.X86.Variants.Backend) :
    (Impl.Pbkdf2.Whole.X86.Fn.sha256 v.F224).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2_224Sp)

/-- `vg_pbkdf2_hmac_sha256` with the backend `v`, as emitted (`Impl.Pbkdf2.Whole.X86.Fn.sha256`),
meets its contract in constant time and returns without secret residue. -/
theorem sha256_scrubbed (v : Proof.Sha256.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Pbkdf2.Whole.X86.Fn.sha256 v.F)
      (Spec.Hmac.sha256I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha256I.pbkdf2Api)
    { suffix := v.suffix
      code := withStackScratch (pbkFrame Spec.Hmac.sha256I) 7 v.F.pbkdf2
      verified := pbkFramed (sha256_verified v) sha256_pbkFrameSat (noEsp_of_all v.pbkdf2Sp) (sha256_stack v)
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2Sp }
    (pbkdf2Out Spec.Hmac.sha256I _) (hs := sha256_scrub v)

/-- No instruction of `vg_pbkdf2_hmac_sha256` with the backend `v`, as emitted, writes `esp`
but in its frames and calls. -/
theorem sha256_spSafe (v : Proof.Sha256.X86.Variants.Backend) :
    (Impl.Pbkdf2.Whole.X86.Fn.sha256 v.F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2Sp)

end VG.Proof.Pbkdf2.Whole.X86.Scrub
