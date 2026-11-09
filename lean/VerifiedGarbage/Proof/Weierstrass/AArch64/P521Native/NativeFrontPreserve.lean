module

-- separate module: API continuation edits reuse the kernel-checked preservation certificate over the complete validation/checkPoint callee tree.

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Lit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Lit

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (validateAndPrepare)

/-- Check the callee tree once, then project the three preservation facts. -/
private theorem prepare_unchanged : ∀i∈instrs validateAndPrepare,
    vdstOf i≠some .v31 ∧ clobbers i .x27=false ∧ clobbers i .x28=false := by
  have checked : Code.allInstrs (fun i => decide
      (vdstOf i≠some .v31 ∧ clobbers i .x27=false ∧ clobbers i .x28=false)) validateAndPrepare=true := by lit_decide
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ checked) i hi)

theorem prepare_no_v31 : ∀i∈instrs validateAndPrepare,vdstOf i≠some .v31 :=
  fun i hi => (prepare_unchanged i hi).1

theorem prepare_no_gp27 : ∀i∈instrs validateAndPrepare,clobbers i .x27=false :=
  fun i hi => (prepare_unchanged i hi).2.1

theorem prepare_no_gp28 : ∀i∈instrs validateAndPrepare,clobbers i .x28=false :=
  fun i hi => (prepare_unchanged i hi).2.2

theorem prepare_preserved {s : State} {Q : State → Prop} (h : WP isa validateAndPrepare s Q) :
    WP isa validateAndPrepare s fun t => Q t ∧ t.sp=s.sp ∧ t.v .v31=s.v .v31 ∧
      t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 := by
  obtain ⟨trace,t,exec,q⟩:=h
  exact ⟨trace,t,exec,q,Exec.sp exec,Exec.vec prepare_no_v31 exec,
    Exec.gpr prepare_no_gp27 exec,Exec.gpr prepare_no_gp28 exec⟩

end VG.Proof.Weierstrass.AArch64.P521Native
