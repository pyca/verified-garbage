module

public import VerifiedGarbage.Impl.P384.CombArithmetic
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
public import VerifiedGarbage.Spec.P384
import VerifiedGarbage.Proof.P384.EcdhDouble.Verified

/-!
# P-384's comb arithmetic on AArch64

`compiler_on`: a straight line of `Ops.op` (`Impl/P384/CombArithmetic.lean`)
computes a field program's values for P-384's modulus, as `fprogB` does
(`Ops.fprog_ok`), changing `x21`–`x25` besides `clob 6`.
-/

@[expose] public section

namespace VG.Proof.P384.CombArithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.P384.CombArithmetic
open VG.Proof.Weierstrass.AArch64

theorem compiler_on (size : Nat) :
    FieldCompilerOn Impl.P384.Ops.M Spec.P384.curve [.x21, .x22, .x23, .x24, .x25] program size := by
  intro base Sl hL hAl hm ops V E s hI hS _ hV
  exact WP.mono (Ops.fprog_ok P384.EcdhDouble.p384_C_p hL hAl hm ops hI hS hV)
    fun _ ⟨k, I⟩ => ⟨⟨k.gpr, k.rd, k.wr, k.sp, k.mem⟩, I⟩

end VG.Proof.P384.CombArithmetic
