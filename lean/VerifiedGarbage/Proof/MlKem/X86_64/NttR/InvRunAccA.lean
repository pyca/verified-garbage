module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, pass A after reading an accumulator

The state after pass A, as a literal, from that after pass B, and the
check of its output (`checkI_acc`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stIAccA

theorem checkI_acc : checkI .acc passIBsAcc = true :=
  checkI_of (p₀ := passIBAcc0) (p₁ := passIBAcc1) (show stIAccA.any outOk = true by rw [stIAccA.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
