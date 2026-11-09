module

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Top
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA signing on x86 (32-bit): verified

`vg_mldsa{44,65,87}_sign_core` (`sign prims p`) with the x86 primitives, verified
against `signCoreContract` (`verified`, with `prims_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlDsa.X86.Sign
open VG.Spec.MlDsa

theorem signCore44_verified : Verified X86.target (sign prims mlDsa44) (signCoreContract mlDsa44 X86.abi 96) :=
  verified prims_ok (.inl rfl) (NoSp.of_all (by lit_decide))

theorem signCore65_verified : Verified X86.target (sign prims mlDsa65) (signCoreContract mlDsa65 X86.abi 96) :=
  verified prims_ok (.inr (.inl rfl)) (NoSp.of_all (by lit_decide))

theorem signCore87_verified : Verified X86.target (sign prims mlDsa87) (signCoreContract mlDsa87 X86.abi 96) :=
  verified prims_ok (.inr (.inr rfl)) (NoSp.of_all (by lit_decide))

end VG.Proof.MlDsa.X86.Sign
