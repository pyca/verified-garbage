module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Impl.Sha512.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha512Out
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
meta import VerifiedGarbage.Impl.Sha512.RISCV64
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha512Out
meta import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# PBKDF2-HMAC-SHA-512/224 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-512/224's sizes, compression function and digest code (`it`): what its
proof needs of SHA-512/224 (`hashOk`), its constant time, which the kernel
checks, and `iterate` against the shared contract of `Spec.Hmac.sha512_224I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512_224

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-512/224's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 28
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 3).flatMap Impl.Sha512.RISCV64.Stream.outW ++ Impl.Sha512.RISCV64.Stream.outHi 3
  pad := padBE 128 28 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨Proof.Sha512.RISCV64.compress_verified.1, Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-512/224, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha512_224S Proof.Sha512.md Spec.Sha512.H0_512_224 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega, h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  out := Sha512Out.out224_ok
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

theorem hashOk : HashOk it (8 * Spec.Hmac.sha512_224I.scratch) Spec.Hmac.sha512_224S Proof.Sha512.md Spec.Sha512.H0_512_224 :=
  hashOkW _ (by decide) (by decide)

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  refine ⟨?_, ?_⟩
  taint_decide_all

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha512_224S Wi).pre (iterK Spec.Hmac.sha512_224S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

theorem iterate_ct : ConstantTime isa (iterK Spec.Hmac.sha512_224S (8 * Spec.Hmac.sha512_224I.scratch)).pre
    (iterK Spec.Hmac.sha512_224S (8 * Spec.Hmac.sha512_224I.scratch)).pub code :=
  ctW _

theorem iterate : Verified RISCV64.target code (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha512_224I RISCV64.abi 0) :=
  verified (I := Spec.Hmac.sha512_224I) hashOk callee (Nat.le_refl _) iterate_ct (by
    inst_sat [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
      Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, RISCV64.abi, RISCV64.argRegs]
      using iterSat 192 28 1872)

end VG.Proof.Pbkdf2.RISCV64.Sha512_224
