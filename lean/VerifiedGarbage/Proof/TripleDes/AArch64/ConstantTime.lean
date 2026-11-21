module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
public meta import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Block
public import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Block
meta import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Scrub.AArch64
meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint

/-! # Constant-time Triple DES block and key-expansion programs -/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. The
block functions keep their public pass state in vector registers, which
`VectorTaint` tracks. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

/-- The key expansion, then what it leaves cleared: words of the key in
`x4`–`x6`, and the key and the subkeys in `v0`–`v7` and `v16`–`v19`. -/
abbrev expandKeyCleared : Prog isa := Impl.TripleDes.AArch64.Fn.expandKey

theorem expandKeyCleared_noResidue (k : Contract isa) : NoResidue expandKeyCleared k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

end VG.Proof.TripleDes.AArch64
