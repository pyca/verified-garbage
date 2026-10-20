module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

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
