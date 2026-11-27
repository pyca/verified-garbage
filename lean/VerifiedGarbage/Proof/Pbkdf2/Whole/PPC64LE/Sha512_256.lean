module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
meta import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Md
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Impl.Sha512.PPC64LE.Md
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-! ### `Pbkdf2.PPC64LE.Sha512_256`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-512/256 on PPC64LE: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/PPC64LE.lean`)
for SHA-512/256's parameters (`Impl/Sha512/PPC64LE/Md.lean`) and compression function: what its proof
needs of SHA-512/256 (`hashOk`), its constant time, which the kernel checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.PPC64LE.Sha512_256

open VG.PPC64LE

/-- `iterate`'s code. -/
abbrev code : Prog isa :=
  Impl.Pbkdf2.PPC64LE.iterate Impl.Sha512.PPC64LE.mdParams512_256 32 "vg_sha512_compress" Impl.Sha512.PPC64LE.compress

theorem hashOk : HashOk Impl.Sha512.PPC64LE.mdParams512_256 32 (8 * Spec.Hmac.sha512_256I.scratch) Spec.Hmac.sha512_256S
    Proof.Sha512.md Spec.Sha512.H0_512_256 where
  sizes := ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Sha512.PPC64LE.Md.shape512_256
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  lenOk := show _ < 2 ^ 64 by decide
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

theorem fdepth : code.fdepth ≤ 2 := by
  rw [fdepth_of_noFrames (iterate_noFrames _ _ _ Proof.Sha512.PPC64LE.Md.callee512_256.noFrames)]; decide

theorem pushFrames : VG.PPC64LE.pushFrames code = true :=
  pushFrames_of_noFrames (iterate_noFrames _ _ _ Proof.Sha512.PPC64LE.Md.callee512_256.noFrames)

/-- `iterate`'s constant time, which the kernel checks. -/
theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.sha512_256S (8 * Spec.Hmac.sha512_256I.scratch)).pre
    (iterK Spec.Hmac.sha512_256S (8 * Spec.Hmac.sha512_256I.scratch)).pub code :=
  ct _ _ _ _ _ _ (by taint_decide)

end VG.Proof.Pbkdf2.PPC64LE.Sha512_256

end

end

/-!
# PBKDF2-HMAC-SHA-512/256 on PPC64LE: the whole derivation

`pbkdf2` over SHA-512/256's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` over a Merkle–Damgård hash function (`fnsOf`); the taint checks of its pieces, which the
kernel evaluates; and `pbkdf2` against the shared contracts of
`Spec.Hmac.sha512_256I`, with its working space as an argument (`scratch`) and in
a frame of its own (`pbkdf2`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE.Sha512_256

open VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Sha512_256 (ok)
open VG.Impl.Hmac.Stream.PPC64LE (hmacFrame)
open VG.Impl.Pbkdf2.Whole.PPC64LE (sha512_256F pbkFrame)

/-- What the proofs need of them. -/
def okF : FnsOK sha512_256F :=
  okOf ok rfl Proof.Hmac.Stream.PPC64LE.Sha512_256.initAny Proof.Hmac.Stream.PPC64LE.Sha512_256.fin_ct
    (Pbkdf2.PPC64LE.correctG Pbkdf2.PPC64LE.Sha512_256.hashOk Proof.Sha512.PPC64LE.Md.callee512_256 96)
    (Pbkdf2.PPC64LE.ctG Pbkdf2.PPC64LE.Sha512_256.iterate_ct 96) Pbkdf2.PPC64LE.Sha512_256.fdepth Pbkdf2.PPC64LE.Sha512_256.pushFrames
    (by decide) (Nat.le_refl _) (by decide) (by decide) (by decide)

theorem checks : Checks sha512_256F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem scratch : Verified PPC64LE.target sha512_256F.pbkdf2
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha512_256I PPC64LE.abi (hmacFrame Spec.Hmac.sha512_256I + 144)) :=
  VG.Proof.Pbkdf2.Whole.PPC64LE.scratch okF checks rfl (by decide) (by
    inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchContract,
      Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256,
      hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat (8 * Spec.Hmac.sha512_256I.pbkdf2Scratch))

theorem pbkdf2 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha512_256I) .r10 sha512_256F.pbkdf2)
    (Spec.Hmac.sha512_256I.pbkdf2Contract PPC64LE.abi (hmacFrame Spec.Hmac.sha512_256I + 144 + pbkFrame Spec.Hmac.sha512_256I)) :=
  framed scratch (by decide) (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, hmacFrame, pbkFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat0)

end VG.Proof.Pbkdf2.Whole.PPC64LE.Sha512_256
