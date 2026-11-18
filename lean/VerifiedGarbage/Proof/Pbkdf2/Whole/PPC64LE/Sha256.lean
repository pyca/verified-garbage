module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Impl.Sha256.PPC64LE
public import VerifiedGarbage.Impl.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Impl.Sha256.PPC64LE
meta import VerifiedGarbage.Impl.Sha256.PPC64LE.Md
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `Pbkdf2.PPC64LE.Sha256`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-256 on PPC64LE: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/PPC64LE.lean`)
for SHA-256's parameters (`Impl/Sha256/PPC64LE/Md.lean`) and compression function: what its proof
needs of SHA-256 (`hashOk`), its constant time, which the kernel checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.PPC64LE.Sha256

open VG.PPC64LE

/-- `iterate`'s code. -/
abbrev code : Prog isa :=
  Impl.Pbkdf2.PPC64LE.iterate Impl.Sha256.PPC64LE.mdParams 32 "vg_sha256_compress" Impl.Sha256.PPC64LE.compress

theorem hashOk : HashOk Impl.Sha256.PPC64LE.mdParams 32 (8 * Spec.Hmac.sha256I.scratch) Spec.Hmac.sha256S
    Proof.Sha256.md Spec.Sha256.H0 where
  sizes := ⟨Proof.Sha256.PPC64LE.Md.dims, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Sha256.PPC64LE.Md.shape
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  lenOk := trivial
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    by decide, by decide⟩

theorem fdepth : code.fdepth ≤ 2 := by
  rw [fdepth_of_noFrames (iterate_noFrames _ _ _ Proof.Sha256.PPC64LE.Md.callee.noFrames)]; decide

theorem pushFrames : VG.PPC64LE.pushFrames code = true :=
  pushFrames_of_noFrames (iterate_noFrames _ _ _ Proof.Sha256.PPC64LE.Md.callee.noFrames)

/-- `iterate`'s constant time, which the kernel checks. -/
theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.sha256S (8 * Spec.Hmac.sha256I.scratch)).pre
    (iterK Spec.Hmac.sha256S (8 * Spec.Hmac.sha256I.scratch)).pub code :=
  ct _ _ _ _ _ _ (by taint_decide)

end VG.Proof.Pbkdf2.PPC64LE.Sha256

end

end

/-!
# PBKDF2-HMAC-SHA-256 on PPC64LE: the whole derivation

`pbkdf2` over SHA-256's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` over a Merkle–Damgård hash function (`fnsOf`); the taint checks of its pieces, which the
kernel evaluates; and `pbkdf2` against the shared contracts of
`Spec.Hmac.sha256I`, with its working space as an argument (`scratch`) and in
a frame of its own (`pbkdf2`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE.Sha256

open VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Sha256 (hash ok)

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.PPC64LE.Fns :=
  fnsOf hash Spec.Hmac.sha256I 6 Pbkdf2.PPC64LE.Sha256.code (8 * Spec.Hmac.sha256I.scratch)

/-- What the proofs need of them. -/
def okF : FnsOK F :=
  okOf ok rfl Proof.Hmac.Stream.PPC64LE.Sha256.initAny Proof.Hmac.Stream.PPC64LE.Sha256.fin_ct
    (Pbkdf2.PPC64LE.correctG Pbkdf2.PPC64LE.Sha256.hashOk Proof.Sha256.PPC64LE.Md.callee 96)
    (Pbkdf2.PPC64LE.ctG Pbkdf2.PPC64LE.Sha256.iterate_ct 96) Pbkdf2.PPC64LE.Sha256.fdepth Pbkdf2.PPC64LE.Sha256.pushFrames
    (by decide) (Nat.le_refl _) (by decide) (by decide) (by decide)

theorem checks : Checks F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem scratch : Verified PPC64LE.target F.pbkdf2
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha256I + 144)) :=
  VG.Proof.Pbkdf2.Whole.PPC64LE.scratch okF checks rfl (by decide) (by
    inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchContract,
      Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256,
      Proof.Hmac.Stream.PPC64LE.hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat (8 * Spec.Hmac.sha256I.pbkdf2Scratch))

theorem pbkdf2 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha256I) .r10 F.pbkdf2)
    (Spec.Hmac.sha256I.pbkdf2Contract PPC64LE.abi (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha256I + 144 + pbkFrame Spec.Hmac.sha256I)) :=
  framed scratch (by decide) (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Proof.Hmac.Stream.PPC64LE.hmacFrame, pbkFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat0)

end VG.Proof.Pbkdf2.Whole.PPC64LE.Sha256
