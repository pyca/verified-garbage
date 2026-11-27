module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

/-!
# ML-DSA on AArch64: a state for a product of polynomials

A state satisfying the precondition of a function that writes to `h` a
product of the polynomials at `f` and `g` (`mulSat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

end VG.Proof.MlDsa.AArch64.Arith
