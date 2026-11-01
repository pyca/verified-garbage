module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Md5
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Md5
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# PBKDF2-HMAC-MD5 on PPC64LE: the whole derivation

`pbkdf2` over MD5's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` over a Merkle–Damgård hash function (`fnsOf`); the taint checks of its pieces, which the
kernel evaluates; and `pbkdf2` against the shared contracts of
`Spec.Hmac.md5I`, with its working space as an argument (`scratch`) and in
a frame of its own (`pbkdf2`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE.Md5

open VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Md5 (hash ok)

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.PPC64LE.Fns :=
  fnsOf hash Spec.Hmac.md5I 6 Pbkdf2.PPC64LE.Md5.code (8 * Spec.Hmac.md5I.scratch)

/-- What the proofs need of them. -/
def okF : FnsOK F :=
  okOf ok rfl Proof.Hmac.Stream.PPC64LE.Md5.initAny Proof.Hmac.Stream.PPC64LE.Md5.fin_ct
    (Pbkdf2.PPC64LE.correctG Pbkdf2.PPC64LE.Md5.hashOk Proof.Md5.PPC64LE.Stream.callee 96)
    (Pbkdf2.PPC64LE.ctG Pbkdf2.PPC64LE.Md5.iterate_ct 96) Pbkdf2.PPC64LE.Md5.fdepth Pbkdf2.PPC64LE.Md5.pushFrames
    (by decide) (Nat.le_refl _) (by decide) (by decide) (by decide)

theorem checks : Checks F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem scratch : Verified PPC64LE.target F.pbkdf2
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.md5I PPC64LE.abi (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I + 144)) :=
  VG.Proof.Pbkdf2.Whole.PPC64LE.scratch okF checks rfl (by decide) (by
    inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchContract,
      Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5,
      Proof.Hmac.Stream.PPC64LE.hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat (8 * Spec.Hmac.md5I.pbkdf2Scratch))

theorem pbkdf2 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.md5I) .r10 F.pbkdf2)
    (Spec.Hmac.md5I.pbkdf2Contract PPC64LE.abi (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.md5I + 144 + pbkFrame Spec.Hmac.md5I)) :=
  framed scratch (by decide) (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, Proof.Hmac.Stream.PPC64LE.hmacFrame, pbkFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat0)

end VG.Proof.Pbkdf2.Whole.PPC64LE.Md5
