module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Hmac.X86
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha384
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_224
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha256
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.Hmac.X86
meta import VerifiedGarbage.Proof.Hmac.AnyKey
meta import VerifiedGarbage.Proof.Hmac.Scratch
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Md5
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha384
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_224
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512_256
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyInstances
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha1
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeySha256
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
meta import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit

/-!
# HMAC on x86 (32-bit), without secret residue

`vg_hmac_<hash>_init` and `vg_hmac_<hash>_finalize` as emitted
(`Impl.Hmac.X86.Fn`): PBKDF2's HMAC functions in frames holding their
working space (`Proof.Pbkdf2.Whole.X86.initCode`,
`Proof.Pbkdf2.Md.X86.finFramed`), followed by the zeroing of the stack their
contracts reserve and the clearing of the registers a callee may change
(`X86.Scrub.verifiedScrubbedAll`). Their postconditions read the memory on
return only within their buffers (`initOut`, `finOut`, from
`Proof.Hmac.initPostOut_local` and `finalizePostOut_local`).

MD5 and the SHA-512 family have one implementation each, whose code the
kernel evaluates here. SHA-1, SHA-224 and SHA-256 are generic over their
backends (`Proof/Variants/Sha1/X86.lean`, `Proof/Variants/Sha256/X86.lean`),
as PBKDF2 is (`Proof/Pbkdf2/Whole/X86/Scrub.lean`): their code with a stub
backend, whose compression, `update` and `finalize` are `.block []`, is
evaluated once (`sha1InitSide`, …), and `Fill` gives the same of every
backend from its own facts (`Backend.cmpScrub`, `updScrub`, `finScrub` and
its stacks), with no evaluation of its code
(`Proof/Framework/X86/ScrubCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Hmac.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Impl.StackScratch.X86 (withStackScratch)
open VG.Proof.Pbkdf2.Whole.X86 (initCode md5F sha384F sha512F sha512_224F sha512_256F)
open VG.Proof.Pbkdf2.Md.X86 (finFrame finFramed md5M sha384M sha512M' sha512_224M sha512_256M)
open VG.Proof.Pbkdf2.Whole.X86.Any (anyFrame)

/-- HMAC's `init`'s postcondition reads the memory on return only within the
two states it writes. -/
theorem initOut (I : Spec.Hmac.Instance) (hR : Proof.Hmac.ReprLocal I.S) (stack : Nat)
    (hS : I.S.stateBytes < 2 ^ 64 := by decide) :
    PostOut (I.initAnyKeyContract X86.abi stack) ((Spec.Hmac.initSig I.S).retBits 32) := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  exact postOut_of_local ScrubAbi.plain (Proof.Hmac.initPostOut_local I.S _ hR hS)

/-- HMAC's `finalize`'s postcondition reads the memory on return only within
`out`, the MAC's bytes. -/
theorem finOut (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.finalizeContract X86.abi stack) ((Spec.Hmac.finalizeSig I.S).retBits 32) := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  exact postOut_of_local ScrubAbi.plain (Proof.Hmac.finalizePostOut_local I.S _)

/-! ## MD5 and the SHA-512 family -/

theorem md5_init_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.md5Init md5M md5F)
      (Spec.Hmac.md5I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.md5I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.md5I.initAnyKeyApi)
    { code := initCode Spec.Hmac.md5I md5M.hmacInit md5F
      verified := Proof.Pbkdf2.Whole.X86.Any.md5_initF
      spSafe := Proof.Pbkdf2.Whole.X86.Any.md5_initSp }
    (initOut Spec.Hmac.md5I Proof.Hmac.md5_local _)

theorem md5_initSp : (Impl.Hmac.X86.Fn.md5Init md5M md5F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe Proof.Pbkdf2.Whole.X86.Any.md5_initSp

theorem md5_fin_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.md5Finalize md5M)
      (Spec.Hmac.md5I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.md5I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.md5I.finalizeApi)
    { code := withStackScratch (finFrame Spec.Hmac.md5I) 5 md5M.hmacFin
      verified := finFramed Proof.Pbkdf2.Md.X86.Instances.md5_finalize Proof.Hmac.md5_local
        Proof.Pbkdf2.Md.X86.md5_finFrameSat }
    (finOut Spec.Hmac.md5I _)

theorem md5_finSp : (Impl.Hmac.X86.Fn.md5Finalize md5M).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Code.all_of_spTest (by lit_decide))

theorem sha384_init_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Init sha384M sha384F)
      (Spec.Hmac.sha384I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha384I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha384I.initAnyKeyApi)
    { code := initCode Spec.Hmac.sha384I sha384M.hmacInit sha384F
      verified := Proof.Pbkdf2.Whole.X86.Any.sha384_initF
      spSafe := Proof.Pbkdf2.Whole.X86.Any.sha384_initSp }
    (initOut Spec.Hmac.sha384I Proof.Hmac.sha384_local _)

theorem sha384_initSp : (Impl.Hmac.X86.Fn.sha512Init sha384M sha384F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe Proof.Pbkdf2.Whole.X86.Any.sha384_initSp

theorem sha384_fin_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Finalize sha384M)
      (Spec.Hmac.sha384I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha384I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha384I.finalizeApi)
    { code := withStackScratch (finFrame Spec.Hmac.sha384I) 5 sha384M.hmacFin
      verified := finFramed Proof.Pbkdf2.Md.X86.Instances.sha384_finalize Proof.Hmac.sha384_local
        Proof.Pbkdf2.Md.X86.sha384_finFrameSat }
    (finOut Spec.Hmac.sha384I _)

theorem sha384_finSp : (Impl.Hmac.X86.Fn.sha512Finalize sha384M).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Code.all_of_spTest (by lit_decide))

theorem sha512_init_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Init sha512M' sha512F)
      (Spec.Hmac.sha512I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512I.initAnyKeyApi)
    { code := initCode Spec.Hmac.sha512I sha512M'.hmacInit sha512F
      verified := Proof.Pbkdf2.Whole.X86.Any.sha512_initF
      spSafe := Proof.Pbkdf2.Whole.X86.Any.sha512_initSp }
    (initOut Spec.Hmac.sha512I Proof.Hmac.sha512_local _)

theorem sha512_initSp : (Impl.Hmac.X86.Fn.sha512Init sha512M' sha512F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe Proof.Pbkdf2.Whole.X86.Any.sha512_initSp

theorem sha512_fin_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Finalize sha512M')
      (Spec.Hmac.sha512I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512I.finalizeApi)
    { code := withStackScratch (finFrame Spec.Hmac.sha512I) 5 sha512M'.hmacFin
      verified := finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_finalize Proof.Hmac.sha512_local
        Proof.Pbkdf2.Md.X86.sha512_finFrameSat }
    (finOut Spec.Hmac.sha512I _)

theorem sha512_finSp : (Impl.Hmac.X86.Fn.sha512Finalize sha512M').all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Code.all_of_spTest (by lit_decide))

theorem sha512_224_init_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Init sha512_224M sha512_224F)
      (Spec.Hmac.sha512_224I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_224I.initAnyKeyApi)
    { code := initCode Spec.Hmac.sha512_224I sha512_224M.hmacInit sha512_224F
      verified := Proof.Pbkdf2.Whole.X86.Any.sha512_224_initF
      spSafe := Proof.Pbkdf2.Whole.X86.Any.sha512_224_initSp }
    (initOut Spec.Hmac.sha512_224I Proof.Hmac.sha512_224_local _)

theorem sha512_224_initSp :
    (Impl.Hmac.X86.Fn.sha512Init sha512_224M sha512_224F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe Proof.Pbkdf2.Whole.X86.Any.sha512_224_initSp

theorem sha512_224_fin_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Finalize sha512_224M)
      (Spec.Hmac.sha512_224I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512_224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_224I.finalizeApi)
    { code := withStackScratch (finFrame Spec.Hmac.sha512_224I) 5 sha512_224M.hmacFin
      verified := finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_224_finalize Proof.Hmac.sha512_224_local
        Proof.Pbkdf2.Md.X86.sha512_224_finFrameSat }
    (finOut Spec.Hmac.sha512_224I _)

theorem sha512_224_finSp : (Impl.Hmac.X86.Fn.sha512Finalize sha512_224M).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Code.all_of_spTest (by lit_decide))

theorem sha512_256_init_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Init sha512_256M sha512_256F)
      (Spec.Hmac.sha512_256I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha512_256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_256I.initAnyKeyApi)
    { code := initCode Spec.Hmac.sha512_256I sha512_256M.hmacInit sha512_256F
      verified := Proof.Pbkdf2.Whole.X86.Any.sha512_256_initF
      spSafe := Proof.Pbkdf2.Whole.X86.Any.sha512_256_initSp }
    (initOut Spec.Hmac.sha512_256I Proof.Hmac.sha512_256_local _)

theorem sha512_256_initSp :
    (Impl.Hmac.X86.Fn.sha512Init sha512_256M sha512_256F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe Proof.Pbkdf2.Whole.X86.Any.sha512_256_initSp

theorem sha512_256_fin_scrubbed :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha512Finalize sha512_256M)
      (Spec.Hmac.sha512_256I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512_256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_256I.finalizeApi)
    { code := withStackScratch (finFrame Spec.Hmac.sha512_256I) 5 sha512_256M.hmacFin
      verified := finFramed Proof.Pbkdf2.Md.X86.Instances.sha512_256_finalize Proof.Hmac.sha512_256_local
        Proof.Pbkdf2.Md.X86.sha512_256_finFrameSat }
    (finOut Spec.Hmac.sha512_256I _)

theorem sha512_256_finSp : (Impl.Hmac.X86.Fn.sha512Finalize sha512_256M).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Code.all_of_spTest (by lit_decide))

/-! ## SHA-1, SHA-224 and SHA-256, generic over their backends

Each function's code with a stub backend, whose compression, `update` and
`finalize` are `.block []`, at 20 bytes less stack than its contract
reserves: the most any backend's functions use (`Backend.cmpStack`,
`updSU`, `finSU`). -/

/-- SHA-1's hash function, with a stub backend. -/
def sha1MStub : Impl.Pbkdf2.Md.X86.Hash := Proof.Sha1.X86.Variants.mdHash "" "" (.block []) (.block []) (.block [])
/-- The functions SHA-1's `init` calls, with a stub backend. -/
def sha1FStub : Impl.Pbkdf2.Whole.X86.Fns := Proof.Sha1.X86.Variants.fns "" "" (.block []) (.block []) (.block [])
/-- SHA-224's hash function, with a stub backend. -/
def sha224MStub : Impl.Pbkdf2.Md.X86.Hash :=
  Proof.Sha256.X86.Variants.mdHash224 "" "" (.block []) (.block []) (.block [])
/-- The functions SHA-224's `init` calls, with a stub backend. -/
def sha224FStub : Impl.Pbkdf2.Whole.X86.Fns :=
  Proof.Sha256.X86.Variants.fns224 "" "" (.block []) (.block []) (.block [])
/-- SHA-256's hash function, with a stub backend. -/
def sha256MStub : Impl.Pbkdf2.Md.X86.Hash :=
  Proof.Sha256.X86.Variants.mdHash "" "" (.block []) (.block []) (.block [])
/-- The functions SHA-256's `init` calls, with a stub backend. -/
def sha256FStub : Impl.Pbkdf2.Whole.X86.Fns :=
  Proof.Sha256.X86.Variants.fns "" "" (.block []) (.block []) (.block [])

materialize_code sha1InitStubLit := initCode Spec.Hmac.sha1I sha1MStub.hmacInit sha1FStub
materialize_code sha1FinStubLit := withStackScratch (finFrame Spec.Hmac.sha1I) 5 sha1MStub.hmacFin
materialize_code sha224InitStubLit := initCode Spec.Hmac.sha224I sha224MStub.hmacInit sha224FStub
materialize_code sha224FinStubLit := withStackScratch (finFrame Spec.Hmac.sha224I) 5 sha224MStub.hmacFin
materialize_code sha256InitStubLit := initCode Spec.Hmac.sha256I sha256MStub.hmacInit sha256FStub
materialize_code sha256FinStubLit := withStackScratch (finFrame Spec.Hmac.sha256I) 5 sha256MStub.hmacFin

theorem sha1InitSide :
    scrubFSide (initCode Spec.Hmac.sha1I sha1MStub.hmacInit sha1FStub) [] (56 + anyFrame Spec.Hmac.sha1I) = true := by
  lit_decide

theorem sha1FinSide :
    scrubFSide (withStackScratch (finFrame Spec.Hmac.sha1I) 5 sha1MStub.hmacFin) [] (28 + finFrame Spec.Hmac.sha1I) = true := by
  lit_decide

theorem sha224InitSide :
    scrubFSide (initCode Spec.Hmac.sha224I sha224MStub.hmacInit sha224FStub) [] (56 + anyFrame Spec.Hmac.sha224I) = true := by
  lit_decide

theorem sha224FinSide :
    scrubFSide (withStackScratch (finFrame Spec.Hmac.sha224I) 5 sha224MStub.hmacFin) [] (28 + finFrame Spec.Hmac.sha224I) = true := by
  lit_decide

theorem sha256InitSide :
    scrubFSide (initCode Spec.Hmac.sha256I sha256MStub.hmacInit sha256FStub) [] (56 + anyFrame Spec.Hmac.sha256I) = true := by
  lit_decide

theorem sha256FinSide :
    scrubFSide (withStackScratch (finFrame Spec.Hmac.sha256I) 5 sha256MStub.hmacFin) [] (28 + finFrame Spec.Hmac.sha256I) = true := by
  lit_decide

/-- The Merkle–Damgård hash with a backend's compression and streaming functions. -/
private def withBackend (M : Impl.Pbkdf2.Md.X86.Hash) (cn un fn : String) (c u f : Prog isa) :=
  { M with compN := cn, compC := c, st := { M.st with updN := un, updC := u, finN := fn, finC := f } }

/-- Both branches of HMAC initialization have the same code shape across
the three hashes, including the long-key path's calls. -/
private theorem init_fill (I : Spec.Hmac.Instance) (M : Impl.Pbkdf2.Md.X86.Hash)
    (F : Impl.Pbkdf2.Whole.X86.Fns) (cn un fn hin : String) (c u f : Prog isa)
    (hc : calleeSide c 20 = true) (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true)
    (hinit : Fill 20 M.st.initC M.st.initC) :
    let stub := withBackend M M.compN M.st.updN M.st.finN (.block []) (.block []) (.block [])
    let md := withBackend M cn un fn c u f
    Fill 20 (initCode I stub.hmacInit { F with H := stub.st, hiC := stub.hmacInit })
      (initCode I md.hmacInit { F with H := md.st, hiN := hin, hiC := md.hmacInit }) := by
  dsimp only
  fill_calls <;> exact hinit

/-- Finalization calls the compression and streaming finalize functions. -/
private theorem fin_fill (M : Impl.Pbkdf2.Md.X86.Hash) (bytes : Nat)
    (cn un fn : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch bytes 5
      (withBackend M M.compN M.st.updN M.st.finN (.block []) (.block []) (.block [])).hmacFin)
      (withStackScratch bytes 5 (withBackend M cn un fn c u f).hmacFin) := by
  fill_calls

theorem sha1InitFill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (initCode Spec.Hmac.sha1I sha1MStub.hmacInit sha1FStub)
      (initCode Spec.Hmac.sha1I (Proof.Sha1.X86.Variants.mdHash sfx cN c u f).hmacInit
        (Proof.Sha1.X86.Variants.fns sfx cN c u f)) := by
  let F := Proof.Sha1.X86.Variants.fns sfx cN c u f
  exact init_fill Spec.Hmac.sha1I sha1MStub sha1FStub cN F.H.updN F.H.finN F.hiN
    c u f hc hu hf (by fill_calls)

theorem sha1FinFill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (finFrame Spec.Hmac.sha1I) 5 sha1MStub.hmacFin)
      (withStackScratch (finFrame Spec.Hmac.sha1I) 5 (Proof.Sha1.X86.Variants.mdHash sfx cN c u f).hmacFin) := by
  let M := Proof.Sha1.X86.Variants.mdHash sfx cN c u f
  exact fin_fill sha1MStub (finFrame Spec.Hmac.sha1I) cN M.st.updN M.st.finN c u f hc hf

theorem sha224InitFill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (initCode Spec.Hmac.sha224I sha224MStub.hmacInit sha224FStub)
      (initCode Spec.Hmac.sha224I (Proof.Sha256.X86.Variants.mdHash224 sfx cN c u f).hmacInit
        (Proof.Sha256.X86.Variants.fns224 sfx cN c u f)) := by
  let F := Proof.Sha256.X86.Variants.fns224 sfx cN c u f
  exact init_fill Spec.Hmac.sha224I sha224MStub sha224FStub cN F.H.updN F.H.finN F.hiN
    c u f hc hu hf (by fill_calls)

theorem sha224FinFill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (finFrame Spec.Hmac.sha224I) 5 sha224MStub.hmacFin)
      (withStackScratch (finFrame Spec.Hmac.sha224I) 5
        (Proof.Sha256.X86.Variants.mdHash224 sfx cN c u f).hmacFin) := by
  let M := Proof.Sha256.X86.Variants.mdHash224 sfx cN c u f
  exact fin_fill sha224MStub (finFrame Spec.Hmac.sha224I) cN M.st.updN M.st.finN c u f hc hf

theorem sha256InitFill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hu : calleeSide u 20 = true) (hf : calleeSide f 20 = true) :
    Fill 20 (initCode Spec.Hmac.sha256I sha256MStub.hmacInit sha256FStub)
      (initCode Spec.Hmac.sha256I (Proof.Sha256.X86.Variants.mdHash sfx cN c u f).hmacInit
        (Proof.Sha256.X86.Variants.fns sfx cN c u f)) := by
  let F := Proof.Sha256.X86.Variants.fns sfx cN c u f
  exact init_fill Spec.Hmac.sha256I sha256MStub sha256FStub cN F.H.updN F.H.finN F.hiN
    c u f hc hu hf (by fill_calls)

theorem sha256FinFill (sfx cN : String) (c u f : Prog isa) (hc : calleeSide c 20 = true)
    (hf : calleeSide f 20 = true) :
    Fill 20 (withStackScratch (finFrame Spec.Hmac.sha256I) 5 sha256MStub.hmacFin)
      (withStackScratch (finFrame Spec.Hmac.sha256I) 5 (Proof.Sha256.X86.Variants.mdHash sfx cN c u f).hmacFin) := by
  let M := Proof.Sha256.X86.Variants.mdHash sfx cN c u f
  exact fin_fill sha256MStub (finFrame Spec.Hmac.sha256I) cN M.st.updN M.st.finN c u f hc hf

/-! ### SHA-1 -/

theorem sha1_init_scrubbed (v : Proof.Sha1.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha1Init v.M v.F)
      (Spec.Hmac.sha1I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha1I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha1I.initAnyKeyApi)
    { suffix := v.suffix
      code := initCode Spec.Hmac.sha1I v.M.hmacInit v.F
      verified := Proof.Pbkdf2.Whole.X86.Any.sha1_initF v
      spSafe := Proof.Pbkdf2.Whole.X86.Any.sha1_initSp v }
    (initOut Spec.Hmac.sha1I Proof.Hmac.sha1_local _) (W := 76 + anyFrame Spec.Hmac.sha1I)
    (hs := scrubFSide_of_fill (sha1InitFill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
      (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)) sha1InitSide)

theorem sha1_initSp (v : Proof.Sha1.X86.Variants.Backend) :
    (Impl.Hmac.X86.Fn.sha1Init v.M v.F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Whole.X86.Any.sha1_initSp v)

theorem sha1_fin_scrubbed (v : Proof.Sha1.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha1Finalize v.M)
      (Spec.Hmac.sha1I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha1I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha1I.finalizeApi)
    { suffix := v.suffix
      code := withStackScratch (finFrame Spec.Hmac.sha1I) 5 v.M.hmacFin
      verified := finFramed v.hmacFin Proof.Hmac.sha1_local Proof.Pbkdf2.Md.X86.sha1_finFrameSat
        (Proof.Pbkdf2.Md.X86.noEsp_of v.finalizeNoSp) v.finalizeStack
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.finSp }
    (finOut Spec.Hmac.sha1I _) (W := 48 + finFrame Spec.Hmac.sha1I)
    (hs := scrubFSide_of_fill (sha1FinFill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
      (calleeSide_of_le v.stream.finSU v.finScrub)) sha1FinSide)

theorem sha1_finSp (v : Proof.Sha1.X86.Variants.Backend) :
    (Impl.Hmac.X86.Fn.sha1Finalize v.M).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.finSp)

/-! ### SHA-224 -/

theorem sha224_init_scrubbed (v : Proof.Sha256.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha256Init v.M224 v.F224)
      (Spec.Hmac.sha224I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha224I.initAnyKeyApi)
    { suffix := v.suffix
      code := initCode Spec.Hmac.sha224I v.M224.hmacInit v.F224
      verified := Proof.Pbkdf2.Whole.X86.Any.sha224_initF v
      spSafe := Proof.Pbkdf2.Whole.X86.Any.sha224_initSp v }
    (initOut Spec.Hmac.sha224I Proof.Hmac.sha224_local _) (W := 76 + anyFrame Spec.Hmac.sha224I)
    (hs := scrubFSide_of_fill (sha224InitFill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
      (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)) sha224InitSide)

theorem sha224_initSp (v : Proof.Sha256.X86.Variants.Backend) :
    (Impl.Hmac.X86.Fn.sha256Init v.M224 v.F224).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Whole.X86.Any.sha224_initSp v)

theorem sha224_fin_scrubbed (v : Proof.Sha256.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha256Finalize v.M224)
      (Spec.Hmac.sha224I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha224I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha224I.finalizeApi)
    { suffix := v.suffix
      code := withStackScratch (finFrame Spec.Hmac.sha224I) 5 v.M224.hmacFin
      verified := finFramed v.hmacFin224 Proof.Hmac.sha224_local Proof.Pbkdf2.Md.X86.sha224_finFrameSat
        (Proof.Pbkdf2.Md.X86.noEsp_of v.finalize224NoSp) v.finalize224Stack
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.fin224Sp }
    (finOut Spec.Hmac.sha224I _) (W := 48 + finFrame Spec.Hmac.sha224I)
    (hs := scrubFSide_of_fill (sha224FinFill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
      (calleeSide_of_le v.stream.finSU v.finScrub)) sha224FinSide)

theorem sha224_finSp (v : Proof.Sha256.X86.Variants.Backend) :
    (Impl.Hmac.X86.Fn.sha256Finalize v.M224).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.fin224Sp)

/-! ### SHA-256 -/

theorem sha256_init_scrubbed (v : Proof.Sha256.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha256Init v.M v.F)
      (Spec.Hmac.sha256I.initAnyKeyContract X86.abi (76 + anyFrame Spec.Hmac.sha256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha256I.initAnyKeyApi)
    { suffix := v.suffix
      code := initCode Spec.Hmac.sha256I v.M.hmacInit v.F
      verified := Proof.Pbkdf2.Whole.X86.Any.sha256_initF v
      spSafe := Proof.Pbkdf2.Whole.X86.Any.sha256_initSp v }
    (initOut Spec.Hmac.sha256I Proof.Hmac.sha256_local _) (W := 76 + anyFrame Spec.Hmac.sha256I)
    (hs := scrubFSide_of_fill (sha256InitFill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
      (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)) sha256InitSide)

theorem sha256_initSp (v : Proof.Sha256.X86.Variants.Backend) :
    (Impl.Hmac.X86.Fn.sha256Init v.M v.F).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Whole.X86.Any.sha256_initSp v)

theorem sha256_fin_scrubbed (v : Proof.Sha256.X86.Variants.Backend) :
    VerifiedScrubbed X86.target (Impl.Hmac.X86.Fn.sha256Finalize v.M)
      (Spec.Hmac.sha256I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha256I)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha256I.finalizeApi)
    { suffix := v.suffix
      code := withStackScratch (finFrame Spec.Hmac.sha256I) 5 v.M.hmacFin
      verified := finFramed v.hmacFin Proof.Hmac.sha256_local Proof.Pbkdf2.Md.X86.sha256_finFrameSat
        (Proof.Pbkdf2.Md.X86.noEsp_of v.finalizeNoSp) v.finalizeStack
      spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.finSp }
    (finOut Spec.Hmac.sha256I _) (W := 48 + finFrame Spec.Hmac.sha256I)
    (hs := scrubFSide_of_fill (sha256FinFill _ _ _ _ _ (calleeSide_of_eq v.cmpStack v.cmpScrub)
      (calleeSide_of_le v.stream.finSU v.finScrub)) sha256FinSide)

theorem sha256_finSp (v : Proof.Sha256.X86.Variants.Backend) :
    (Impl.Hmac.X86.Fn.sha256Finalize v.M).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.finSp)

end VG.Proof.Hmac.X86.Scrub
