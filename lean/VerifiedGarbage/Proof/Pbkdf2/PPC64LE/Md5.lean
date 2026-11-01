module

public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Correct
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Md5.PPC64LE.Compress

/-!
# PBKDF2-HMAC-MD5 on PPC64LE: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/PPC64LE.lean`)
for MD5's streaming parameters and compression function: what its proof
needs of MD5 (`hashOk`), its constant time, which the kernel checks, and
`iterate` against the shared contract of `Spec.Hmac.md5I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.PPC64LE.Md5

open VG.PPC64LE

/-- `iterate`'s code. -/
abbrev code : Prog isa :=
  Impl.Pbkdf2.PPC64LE.iterate Impl.Md5.PPC64LE.Stream.params 16 "vg_md5_compress" Impl.Md5.PPC64LE.compress

theorem hashOk : HashOk Impl.Md5.PPC64LE.Stream.params 16 (8 * Spec.Hmac.md5I.scratch) Spec.Hmac.md5S
    Proof.Md5.md Spec.Md5.H0 where
  sizes := ⟨Proof.Md5.PPC64LE.Stream.dims, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Md5.PPC64LE.Stream.shape
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  lenOk := trivial
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm,
    by decide, by decide⟩

theorem fdepth : code.fdepth ≤ 2 := by
  rw [fdepth_of_noFrames (iterate_noFrames _ _ _ Proof.Md5.PPC64LE.Stream.callee.noFrames)]; decide

theorem pushFrames : VG.PPC64LE.pushFrames code = true :=
  pushFrames_of_noFrames (iterate_noFrames _ _ _ Proof.Md5.PPC64LE.Stream.callee.noFrames)

/-- `iterate`'s constant time, which the kernel checks. -/
theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.md5S (8 * Spec.Hmac.md5I.scratch)).pre
    (iterK Spec.Hmac.md5S (8 * Spec.Hmac.md5I.scratch)).pub code :=
  ct _ _ _ _ _ _ (by taint_decide)

theorem iterate : Verified PPC64LE.target code (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.md5I PPC64LE.abi 0) :=
  verified (I := Spec.Hmac.md5I) hashOk Proof.Md5.PPC64LE.Stream.callee (Nat.le_refl _) iterate_ct (by
    inst_sat [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
      Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, PPC64LE.abi, PPC64LE.argRegs]
      using iterSat 80 16 384)

end VG.Proof.Pbkdf2.PPC64LE.Md5
