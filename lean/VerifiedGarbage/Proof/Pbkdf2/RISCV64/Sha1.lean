module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Impl.Sha1.RISCV64
public import VerifiedGarbage.Impl.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# PBKDF2-HMAC-SHA-1 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-1's sizes, compression function and digest code (`it`), and what its
proof needs of SHA-1 (`hashOkW`): the sizes and the precondition that
SHA-1's own iteration (`Proof/Pbkdf2/Sha1/RISCV64/`) shares with it.
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

end VG.Proof.Pbkdf2.RISCV64.Sha1
