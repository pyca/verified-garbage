module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Impl.Sha1.RISCV64
public import VerifiedGarbage.Impl.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
meta import VerifiedGarbage.Impl.Sha1.RISCV64
meta import VerifiedGarbage.Impl.Sha1.RISCV64.Stream
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# PBKDF2-HMAC-SHA-1 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-1's sizes, compression function and digest code (`it`): what its
proof needs of SHA-1 (`hashOk`), its constant time, which the kernel
checks, and `iterate` against the shared contract of `Spec.Hmac.sha1I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha1

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-1's parameters of the iteration. -/
def it : It where
  N := 20
  B := 64
  D := 20
  CW := 80
  cmpN := "vg_sha1_compress"
  cmpC := Impl.Sha1.RISCV64.compress
  out := Impl.Sha1.RISCV64.Stream.params.out
  pad := padBE 64 20 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha1.md 80 Impl.Sha1.RISCV64.compress :=
  ⟨Proof.Sha1.RISCV64.Stream.callee.verified, Proof.Sha1.RISCV64.Stream.callee.noFrames⟩

/-- What the proof needs of SHA-1, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 227 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha1S Proof.Sha1.md Spec.Sha1.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega, h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
  out := fun s h₁ h₂ h₃ => (Proof.Sha1.RISCV64.Stream.shape.out s h₁ h₂ h₃).mono fun _ ⟨g, a, b, c, d⟩ =>
    ⟨fun r x y _ => g r x y, a, b, c, d⟩
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    by decide, by decide⟩

theorem hashOk : HashOk it (8 * Spec.Hmac.sha1I.scratch) Spec.Hmac.sha1S Proof.Sha1.md Spec.Sha1.H0 :=
  hashOkW _ (by decide) (by decide)

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  refine ⟨?_, ?_⟩
  taint_decide_all

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha1S Wi).pre (iterK Spec.Hmac.sha1S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.sha1S (8 * Spec.Hmac.sha1I.scratch)).pre
    (iterK Spec.Hmac.sha1S (8 * Spec.Hmac.sha1I.scratch)).pub code :=
  ctW _

theorem iterate : Verified RISCV64.target code (Spec.Hmac.sha1I.iterateContract RISCV64.abi 0) :=
  verified (I := Spec.Hmac.sha1I) hashOk callee (Nat.le_refl _) iterate_ct (by
    inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
      Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, RISCV64.abi, RISCV64.argRegs]
      using iterSat 84 20 448)

end VG.Proof.Pbkdf2.RISCV64.Sha1
