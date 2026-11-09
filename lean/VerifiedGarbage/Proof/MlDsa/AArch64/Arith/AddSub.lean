module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_add` and `vg_mldsa_sub`

What the proofs of the functions of two polynomials share: the address of
the next coefficient (`coeffAddr_next`), that their pointers are public
(`acc_agree`), and a state satisfying their precondition (`accSat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)

/-! ## One coefficient -/

/-- A word, zero-extended. -/
abbrev w64 (v : BitVec 32) : BitVec 64 := v.setWidth 64

/-! ## The loop -/

theorem coeffAddr_next (p : Addr) (j : Nat) : coeffAddr p j + BitVec.ofNat 64 4 = coeffAddr p (j + 1) :=
  coeffAddr_add p j 1

/-! ## The functions -/

theorem acc_agree {t : Poly → Poly → Poly} (s₁ s₂ : State) (_ : (accK t).pre s₁) (_ : (accK t).pre s₂)
    (hp : (accK t).pub s₁ s₂) : VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1]) s₁ s₂ :=
  agree_regs hp.2.2 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.1, hp.2.1]

/-- A state satisfying the precondition. -/
def accSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

end VG.Proof.MlDsa.AArch64.Arith
