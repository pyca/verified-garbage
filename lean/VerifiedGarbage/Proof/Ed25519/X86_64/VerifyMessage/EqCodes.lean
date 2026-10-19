module

import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.CT
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyLit
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# The equations the verification over SHA-512 calls

`EqCode` of each registered `vg_ed25519_verify_equation`, which
`Generic/MdHash/X86_64/Ed25519.lean` passes to the verification it makes
with each SHA-512 backend.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.VerifyCode

open VG.Impl.Ed25519.X86_64

theorem baseline_eq :
    VerifyMessage.EqCode Impl.X25519.X86_64.baseline (windows Impl.X25519.X86_64.baseline) :=
  ⟨baseline_call, baseline_noSp, by lit_decide, baseline_spSafe⟩

theorem adx_eq : VerifyMessage.EqCode Impl.X25519.X86_64.adx (windows Impl.X25519.X86_64.adx) :=
  ⟨adx_call, adx_noSp, by lit_decide, adx_spSafe⟩

theorem ifma_eq : VerifyMessage.EqCode Impl.X25519.X86_64.adx Ifma.windows :=
  ⟨ifma_call, ifma_noSp, by lit_decide, ifma_spSafe⟩

end VG.Proof.Ed25519.X86_64.VerifyCode
