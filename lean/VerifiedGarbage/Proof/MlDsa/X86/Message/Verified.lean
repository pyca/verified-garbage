module
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall

import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlKem.X86.TopKem
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst
meta import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlKem.X86.TopKem
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the functions

Untrusted: everything here is checked by Lean. `vg_mldsa{44,65,87}_sign_message`
and `_verify_message`, calling `vg_mldsa{44,65,87}_sign` and `_verify`
(`sign44Fn`, `verify44Fn`, …), meet `signMessageContract p X86.abi 136` and
`verifyMessageContract p X86.abi 132` (`signMessage44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Spec.MlDsa

/-! ## The functions on `μ` -/

theorem sign44Fn : SignFn mlDsa44 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44) :=
  ⟨Sign.sign44_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
theorem sign65Fn : SignFn mlDsa65 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65) :=
  ⟨Sign.sign65_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
theorem sign87Fn : SignFn mlDsa87 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87) :=
  ⟨Sign.sign87_verified, NoSp.of_all (by lit_decide), by lit_decide⟩

theorem verify44Fn : VerifyFn mlDsa44 Impl.MlDsa.X86.Verify.verify44 :=
  ⟨Verify.verify44_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
theorem verify65Fn : VerifyFn mlDsa65 Impl.MlDsa.X86.Verify.verify65 :=
  ⟨Verify.verify65_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
theorem verify87Fn : VerifyFn mlDsa87 Impl.MlDsa.X86.Verify.verify87 :=
  ⟨Verify.verify87_verified, NoSp.of_all (by lit_decide), by lit_decide⟩

/-! ## The functions on messages -/

theorem signMessage44_verified :
    Verified X86.target (signMessage sign44Api.name (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa44) mlDsa44)
      (signMessageContract mlDsa44 X86.abi 136) :=
  signMessage_verified (List.mem_cons_self ..) sign44Fn (by native_taint_decide)
theorem signMessage65_verified :
    Verified X86.target (signMessage sign65Api.name (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65) mlDsa65)
      (signMessageContract mlDsa65 X86.abi 136) :=
  signMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_self ..)) sign65Fn (by native_taint_decide)
theorem signMessage87_verified :
    Verified X86.target (signMessage sign87Api.name (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87) mlDsa87)
      (signMessageContract mlDsa87 X86.abi 136) :=
  signMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) sign87Fn
    (by native_taint_decide)

theorem verifyMessage44_verified :
    Verified X86.target (verifyMessage verify44Api.name Impl.MlDsa.X86.Verify.verify44 mlDsa44)
      (verifyMessageContract mlDsa44 X86.abi 132) :=
  verifyMessage_verified (List.mem_cons_self ..) verify44Fn (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)
    (NoSp.of_all (by lit_decide))
theorem verifyMessage65_verified :
    Verified X86.target (verifyMessage verify65Api.name Impl.MlDsa.X86.Verify.verify65 mlDsa65)
      (verifyMessageContract mlDsa65 X86.abi 132) :=
  verifyMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_self ..)) verify65Fn (by native_taint_decide)
    (by native_taint_decide) (by native_taint_decide) (NoSp.of_all (by lit_decide))
theorem verifyMessage87_verified :
    Verified X86.target (verifyMessage verify87Api.name Impl.MlDsa.X86.Verify.verify87 mlDsa87)
      (verifyMessageContract mlDsa87 X86.abi 132) :=
  verifyMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) verify87Fn
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (NoSp.of_all (by lit_decide))

end VG.Proof.MlDsa.X86.Message
