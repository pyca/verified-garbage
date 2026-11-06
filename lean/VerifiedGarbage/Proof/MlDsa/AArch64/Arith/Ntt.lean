module

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Table
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
meta import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Table

/-!
# ML-DSA on AArch64: `vg_mldsa_ntt`

What the proofs of the in-place functions (`NTT`, `NTT⁻¹`) share: their
pointers are public (`inPlace_agree`), and a state satisfying their
precondition (`inPlaceSat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq zetas ntt)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)

/-- The pointers are public. -/
theorem inPlace_agree {t : Poly → Poly} (s₁ s₂ : State) (_ : (inPlaceK t).pre s₁) (_ : (inPlaceK t).pre s₂)
    (hp : (inPlaceK t).pub s₁ s₂) : VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1]) s₁ s₂ :=
  agree_regs hp.2.2 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.1, hp.2.1]

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

end VG.Proof.MlDsa.AArch64.Arith
