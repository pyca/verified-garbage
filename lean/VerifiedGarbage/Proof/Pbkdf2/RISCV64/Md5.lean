module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Impl.Md5.RISCV64
public import VerifiedGarbage.Impl.Md5.RISCV64.Stream
import VerifiedGarbage.Proof.Md5.RISCV64.Stream
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
meta import VerifiedGarbage.Impl.Md5.RISCV64
meta import VerifiedGarbage.Impl.Md5.RISCV64.Stream
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# PBKDF2-HMAC-MD5 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for MD5's sizes, compression function and digest code (`it`): what its
proof needs of MD5 (`hashOk`), its constant time, which the kernel
checks, and `iterate` against the shared contract of `Spec.Hmac.md5I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Md5

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padLE)

/-- MD5's parameters of the iteration. -/
def it : It where
  N := 16
  B := 64
  D := 16
  CW := 80
  cmpN := "vg_md5_compress"
  cmpC := Impl.Md5.RISCV64.compress
  out := Impl.Md5.RISCV64.Stream.params.out
  pad := padLE 64 16 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Md5.md 80 Impl.Md5.RISCV64.compress :=
  ⟨Proof.Md5.RISCV64.Stream.callee.verified, Proof.Md5.RISCV64.Stream.callee.noFrames⟩

/-- What the proof needs of MD5, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 223 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.md5S Proof.Md5.md Spec.Md5.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega, h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  out := fun s h₁ h₂ h₃ => (Proof.Md5.RISCV64.Stream.shape.out s h₁ h₂ h₃).mono fun _ ⟨g, a, b, c, d⟩ =>
    ⟨fun r x y _ => g r x y, a, b, c, d⟩
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm,
    by decide, by decide⟩

theorem hashOk : HashOk it (8 * Spec.Hmac.md5I.scratch) Spec.Hmac.md5S Proof.Md5.md Spec.Md5.H0 :=
  hashOkW _ (by decide) (by decide)

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  refine ⟨?_, ?_⟩
  taint_decide_all

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.md5S Wi).pre (iterK Spec.Hmac.md5S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.md5S (8 * Spec.Hmac.md5I.scratch)).pre
    (iterK Spec.Hmac.md5S (8 * Spec.Hmac.md5I.scratch)).pub code :=
  ctW _

theorem iterate : Verified RISCV64.target code (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.md5I RISCV64.abi 0) :=
  verified (I := Spec.Hmac.md5I) hashOk callee (Nat.le_refl _) iterate_ct (by
    inst_sat [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
      Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, RISCV64.abi, RISCV64.argRegs]
      using iterSat 80 16 384)

end VG.Proof.Pbkdf2.RISCV64.Md5
