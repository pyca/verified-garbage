module

public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Impl.Sha256.PPC64LE
public import VerifiedGarbage.Impl.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# PBKDF2-HMAC-SHA-256 on PPC64LE: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/PPC64LE.lean`)
for SHA-256's parameters (`Impl/Sha256/PPC64LE/Md.lean`) and compression function: what its proof
needs of SHA-256 (`hashOk`), its constant time, which the kernel checks, and
`iterate` against the shared contract of `Spec.Hmac.sha256I`.
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
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
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

theorem iterate : Verified PPC64LE.target code (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha256I PPC64LE.abi 0) :=
  verified (I := Spec.Hmac.sha256I) hashOk Proof.Sha256.PPC64LE.Md.callee (Nat.le_refl _) iterate_ct (by
    inst_sat [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
      Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi, PPC64LE.argRegs]
      using iterSat 96 32 832)

end VG.Proof.Pbkdf2.PPC64LE.Sha256
