module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Impl.Sha1.PPC64LE.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Impl.Sha1.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Sha1.Md
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress

/-! ### `Pbkdf2.PPC64LE.Sha1`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-1 on PPC64LE: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/PPC64LE.lean`)
for SHA-1's streaming parameters and compression function: what its proof
needs of SHA-1 (`hashOk`), its constant time, which the kernel checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.PPC64LE.Sha1

open VG.PPC64LE

/-- `iterate`'s code. -/
abbrev code : Prog isa :=
  Impl.Pbkdf2.PPC64LE.iterate Impl.Sha1.PPC64LE.Stream.params 20 "vg_sha1_compress" Impl.Sha1.PPC64LE.compress

theorem hashOk : HashOk Impl.Sha1.PPC64LE.Stream.params 20 (8 * Spec.Hmac.sha1I.scratch) Spec.Hmac.sha1S
    Proof.Sha1.md Spec.Sha1.H0 where
  sizes := ⟨Proof.Sha1.PPC64LE.Stream.dims, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Sha1.PPC64LE.Stream.shape
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega_using [hj])
  lenOk := trivial
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    by decide, by decide⟩

theorem fdepth : code.fdepth ≤ 2 := by
  rw [fdepth_of_noFrames (iterate_noFrames _ _ _ Proof.Sha1.PPC64LE.Stream.callee.noFrames)]; decide

theorem pushFrames : VG.PPC64LE.pushFrames code = true :=
  pushFrames_of_noFrames (iterate_noFrames _ _ _ Proof.Sha1.PPC64LE.Stream.callee.noFrames)

/-- `iterate`'s constant time, which the kernel checks. -/
theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.sha1S (8 * Spec.Hmac.sha1I.scratch)).pre
    (iterK Spec.Hmac.sha1S (8 * Spec.Hmac.sha1I.scratch)).pub code :=
  ct _ _ _ _ _ _ (by taint_decide)

end VG.Proof.Pbkdf2.PPC64LE.Sha1

end

end

/-!
# PBKDF2-HMAC-SHA-1 on PPC64LE: the whole derivation

`pbkdf2` over SHA-1's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` over a Merkle–Damgård hash function (`fnsOf`); the taint checks of its pieces, which the
kernel evaluates; and `pbkdf2` against the shared contracts of
`Spec.Hmac.sha1I`, with its working space as an argument (`scratch`) and in
a frame of its own (`pbkdf2`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE.Sha1

open VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Sha1 (hash ok)

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.PPC64LE.Fns :=
  fnsOf hash Spec.Hmac.sha1I 6 Pbkdf2.PPC64LE.Sha1.code (8 * Spec.Hmac.sha1I.scratch)

/-- What the proofs need of them. -/
def okF : FnsOK F :=
  okOf ok rfl Proof.Hmac.Stream.PPC64LE.Sha1.initAny Proof.Hmac.Stream.PPC64LE.Sha1.fin_ct
    (Pbkdf2.PPC64LE.correctG Pbkdf2.PPC64LE.Sha1.hashOk Proof.Sha1.PPC64LE.Stream.callee 96)
    (Pbkdf2.PPC64LE.ctG Pbkdf2.PPC64LE.Sha1.iterate_ct 96) Pbkdf2.PPC64LE.Sha1.fdepth Pbkdf2.PPC64LE.Sha1.pushFrames
    (by decide) (Nat.le_refl _) (by decide) (by decide) (by decide)

theorem checks : Checks F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem scratch : Verified PPC64LE.target F.pbkdf2
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha1I PPC64LE.abi (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha1I + 144)) :=
  VG.Proof.Pbkdf2.Whole.PPC64LE.scratch okF checks rfl (by decide) (by
    inst_sat [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchContract,
      Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1,
      Proof.Hmac.Stream.PPC64LE.hmacFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat (8 * Spec.Hmac.sha1I.pbkdf2Scratch))

theorem pbkdf2 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch (pbkFrame Spec.Hmac.sha1I) .r10 F.pbkdf2)
    (Spec.Hmac.sha1I.pbkdf2Contract PPC64LE.abi (Proof.Hmac.Stream.PPC64LE.hmacFrame Spec.Hmac.sha1I + 144 + pbkFrame Spec.Hmac.sha1I)) :=
  framed scratch (by decide) (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Proof.Hmac.Stream.PPC64LE.hmacFrame, pbkFrame, PPC64LE.abi, PPC64LE.argRegs]
      using pbkSat0)

end VG.Proof.Pbkdf2.Whole.PPC64LE.Sha1
