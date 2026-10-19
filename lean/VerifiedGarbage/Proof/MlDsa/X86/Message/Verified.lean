module
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base
public import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall

import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Verify
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.MlDsa.Sample.Word
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Table
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimB
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Run
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
import VerifiedGarbage.Proof.MlKem.X86.EncV
import VerifiedGarbage.Proof.MlKem.X86.NttSetup
import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.MlKem.X86.Table
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.MlKem.X86.TopHash
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.TopPrim
import VerifiedGarbage.Proof.MlKem.X86.TopPrim2
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
meta import VerifiedGarbage.Proof.MlDsa.Sample.Signs
meta import VerifiedGarbage.Proof.MlDsa.Sample.Word
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Sign.Mem
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.Table
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop
meta import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimB
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Run
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Ball
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Final
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Row
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Top
meta import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
meta import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
meta import VerifiedGarbage.Proof.MlKem.X86.EncV
meta import VerifiedGarbage.Proof.MlKem.X86.NttSetup
meta import VerifiedGarbage.Proof.MlKem.X86.Red
meta import VerifiedGarbage.Proof.MlKem.X86.Table
meta import VerifiedGarbage.Proof.MlKem.X86.TopCall
meta import VerifiedGarbage.Proof.MlKem.X86.TopHash
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlKem.X86.TopPrim
meta import VerifiedGarbage.Proof.MlKem.X86.TopPrim2
meta import VerifiedGarbage.Proof.MlKem.X86.TopSeq
meta import VerifiedGarbage.Proof.Sha512.Spec

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
  ⟨Sign.sign44_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem sign65Fn : SignFn mlDsa65 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa65) :=
  ⟨Sign.sign65_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem sign87Fn : SignFn mlDsa87 (Impl.MlDsa.X86.Sign.sign Sign.prims mlDsa87) :=
  ⟨Sign.sign87_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩

theorem verify44Fn : VerifyFn mlDsa44 Impl.MlDsa.X86.Verify.verify44 :=
  ⟨Verify.verify44_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem verify65Fn : VerifyFn mlDsa65 Impl.MlDsa.X86.Verify.verify65 :=
  ⟨Verify.verify65_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩
theorem verify87Fn : VerifyFn mlDsa87 Impl.MlDsa.X86.Verify.verify87 :=
  ⟨Verify.verify87_verified, NoSp.of_all (by decide +kernel), by decide +kernel⟩

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
    (NoSp.of_all (by decide +kernel))
theorem verifyMessage65_verified :
    Verified X86.target (verifyMessage verify65Api.name Impl.MlDsa.X86.Verify.verify65 mlDsa65)
      (verifyMessageContract mlDsa65 X86.abi 132) :=
  verifyMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_self ..)) verify65Fn (by native_taint_decide)
    (by native_taint_decide) (by native_taint_decide) (NoSp.of_all (by decide +kernel))
theorem verifyMessage87_verified :
    Verified X86.target (verifyMessage verify87Api.name Impl.MlDsa.X86.Verify.verify87 mlDsa87)
      (verifyMessageContract mlDsa87 X86.abi 132) :=
  verifyMessage_verified (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) verify87Fn
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (NoSp.of_all (by decide +kernel))

end VG.Proof.MlDsa.X86.Message
