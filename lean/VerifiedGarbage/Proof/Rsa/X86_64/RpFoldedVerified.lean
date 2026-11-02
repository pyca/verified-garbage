module

import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTCode
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Rsa.X86_64.Calls
import VerifiedGarbage.Proof.Rsa.X86_64.Implies8
import VerifiedGarbage.Proof.Rsa.X86_64.CallPatch
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCode
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Folded recovery against the existing shared contract and call ABI -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Rsa.X86_64.Keys.Recover

theorem call_verified [InvLaw] (M : Mont) {c : Prog isa} (hc : c.InlineOk = true)
    (hin : c.inline = Folded.code M.mm)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Rsa.recoverPrimesContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ rpCode_correct M hmx) (hin ▸ rpCode_constantTime M) rp_implies8
    (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h) rp_patch

theorem base_verified [InvLaw] :
    Verified target (Folded.code CallMont.base.mm) (Spec.Rsa.recoverPrimesContract abi 8) :=
  call_verified VG.Proof.Bignum.X86_64.Mont.fnBase (by decide +kernel) rfl (by decide +kernel)

theorem adx_verified [InvLaw] :
    Verified target (Folded.code CallMont.adx.mm) (Spec.Rsa.recoverPrimesContract abi 8) :=
  call_verified VG.Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)

end VG.Proof.Rsa.X86_64.RecoveryFolded
