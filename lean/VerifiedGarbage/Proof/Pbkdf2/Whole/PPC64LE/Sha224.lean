module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
meta import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
import VerifiedGarbage.Proof.Sha256.Digest
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
meta import VerifiedGarbage.Proof.Sha256.Digest
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Impl.Sha256.PPC64LE
meta import VerifiedGarbage.Impl.Sha256.PPC64LE.Md
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `Pbkdf2.PPC64LE.Sha224`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-224 on PPC64LE: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/PPC64LE.lean`)
for SHA-224's parameters (`Impl/Sha256/PPC64LE/Md.lean`) and compression function: what its proof
needs of SHA-224 (`hashOk`), its constant time, which the kernel checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.PPC64LE.Sha224

open VG.PPC64LE

/-- `iterate`'s code. -/
abbrev code : Prog isa :=
  Impl.Pbkdf2.PPC64LE.iterate Impl.Sha256.PPC64LE.mdParams224 28 "vg_sha256_compress" Impl.Sha256.PPC64LE.compress

theorem hashOk : HashOk Impl.Sha256.PPC64LE.mdParams224 28 (8 * Spec.Hmac.sha224I.scratch) Spec.Hmac.sha224S
    Proof.Sha256.md Spec.Sha256.H0_224 where
  sizes := ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Sha256.PPC64LE.Md.shape224
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  lenOk := trivial
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => (Proof.Sha256.sha224_eq m).symm,
    by decide, by decide⟩

theorem fdepth : code.fdepth ≤ 2 := by
  rw [fdepth_of_noFrames (iterate_noFrames _ _ _ Proof.Sha256.PPC64LE.Md.callee224.noFrames)]; decide

theorem pushFrames : VG.PPC64LE.pushFrames code = true :=
  pushFrames_of_noFrames (iterate_noFrames _ _ _ Proof.Sha256.PPC64LE.Md.callee224.noFrames)

/-- `iterate`'s constant time, which the kernel checks. -/
theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.sha224S (8 * Spec.Hmac.sha224I.scratch)).pre
    (iterK Spec.Hmac.sha224S (8 * Spec.Hmac.sha224I.scratch)).pub code :=
  ct _ _ _ _ _ _ (by taint_decide)

end VG.Proof.Pbkdf2.PPC64LE.Sha224

end

end

/-!
# PBKDF2-HMAC-SHA-224 on PPC64LE: the whole derivation

`pbkdf2` over SHA-224's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` over a Merkle–Damgård hash function (`fnsOf`); the taint checks of its pieces, which the
kernel evaluates; and `pbkdf2` against the shared contracts of
`Spec.Hmac.sha224I`, with its working space as an argument (`scratch`) and in
a frame of its own (`pbkdf2`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE.Sha224

open VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Sha224 (ok)
open VG.Impl.Hmac.Stream.PPC64LE (hmacFrame)
open VG.Impl.Pbkdf2.Whole.PPC64LE (sha224F pbkFrame)

/-- What the proofs need of them. -/
def okF : FnsOK sha224F :=
  okOf ok rfl Proof.Hmac.Stream.PPC64LE.Sha224.initAny Proof.Hmac.Stream.PPC64LE.Sha224.fin_ct
    (Pbkdf2.PPC64LE.correctG Pbkdf2.PPC64LE.Sha224.hashOk Proof.Sha256.PPC64LE.Md.callee224 96)
    (Pbkdf2.PPC64LE.ctG Pbkdf2.PPC64LE.Sha224.iterate_ct 96) Pbkdf2.PPC64LE.Sha224.fdepth Pbkdf2.PPC64LE.Sha224.pushFrames
    (by decide) (Nat.le_refl _) (by decide) (by decide) (by decide)

theorem checks : Checks sha224F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem scratch : Verified PPC64LE.target sha224F.pbkdf2
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha224I PPC64LE.abi (hmacFrame Spec.Hmac.sha224I + 144)) :=
  VG.Proof.Pbkdf2.Whole.PPC64LE.scratch okF checks rfl (by decide) (by
    inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchContract,
      Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224,
      hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat (8 * Spec.Hmac.sha224I.pbkdf2Scratch))

theorem pbkdf2 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha224I) .r10 sha224F.pbkdf2)
    (Spec.Hmac.sha224I.pbkdf2Contract PPC64LE.abi (hmacFrame Spec.Hmac.sha224I + 144 + pbkFrame Spec.Hmac.sha224I)) :=
  framed scratch (by decide) (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, hmacFrame, pbkFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat0)

end VG.Proof.Pbkdf2.Whole.PPC64LE.Sha224
