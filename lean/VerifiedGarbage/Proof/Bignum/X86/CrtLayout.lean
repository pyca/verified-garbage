module

public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Spec.Rsa.Contract
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The CRT workspace fits the existing shared RSA scratch contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Dynamic

theorem size_eq (n : Nat) : size n = 320 * n + 224 := by
  unfold size slot stride
  omega

theorem context_fits (n : Nat) : contextBytes n ≤ size n := by
  have := slot_le (n := n) (i := 9) (j := 20) (by decide)
  exact Nat.le_trans (Nat.le_add_right _ _) this

theorem slot_bound {n i : Nat} (hi : i < 20) : slot n i + stride n ≤ size n := slot_le hi

theorem shared_scratch {len : Nat} (lo : 64 ≤ len) :
    size (Spec.Rsa.modulusWords len) ≤ 8 * Spec.Rsa.scratchWords len := by
  rw [size_eq]
  unfold Spec.Rsa.modulusWords Spec.Rsa.scratchWords
  omega

end VG.Proof.Bignum.X86.Crt
