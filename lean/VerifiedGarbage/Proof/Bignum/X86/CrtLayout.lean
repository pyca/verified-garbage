module

public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The CRT workspace fits the existing shared RSA scratch contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Dynamic

theorem size_eq (n : Nat) : size n = 448 * n + 288 := by
  unfold size slot stride
  omega

theorem shared_scratch {len : Nat} (lo : 64 ≤ len) :
    size (Spec.Rsa.modulusWords len) ≤ 8 * Spec.Rsa.scratchWords len := by
  rw [size_eq]
  unfold Spec.Rsa.modulusWords Spec.Rsa.scratchWords
  omega

end VG.Proof.Bignum.X86.Crt
