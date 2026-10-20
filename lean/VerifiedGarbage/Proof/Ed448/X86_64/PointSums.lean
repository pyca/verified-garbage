module

public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
meta import VerifiedGarbage.Proof.Ed448.Scalar
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.X448.X86_64.AddSub
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified

/-!
# Taint summaries of the Ed448 x86-64 point functions

The verifier's timing proofs check code that runs the point doubling and
addition (`FieldVariant.bodies`) many times, in many theorems: each
`taint_decide` analysed each body again. These summaries analyse each body
once, from `rdi` public, keeping `rbx` (the loop counter, which the bodies
do not write) public through it; `relCT_sum` turns a check that uses them
(`taint_decide_sum`) into the same `RelCT` as `RelCT.taint`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64

taint_summary dblSum : taintS (Taint.ofRegs [.rdi]) Point64.doubleFn keeping (Taint.ofRegs [.rbx])
taint_summary addSum : taintS (Taint.ofRegs [.rdi]) Point64.addFn keeping (Taint.ofRegs [.rbx])
taint_summary dblAdxSum : taintS (Taint.ofRegs [.rdi]) Point64.doubleAdxFn keeping (Taint.ofRegs [.rbx])
taint_summary addAdxSum : taintS (Taint.ofRegs [.rdi]) Point64.addAdxFn keeping (Taint.ofRegs [.rbx])

/-- `RelCT.taint` for `taintS`, from a check that `taint_decide_sum` proves. -/
theorem relCT_sum {P : State → State → Prop} {c : Prog isa} (τ : X86_64.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → X86_64.Taint.Agree τ s₁ s₂) (h : ∃ hc, (taintS.check τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taintS) τ hp h

end VG.Proof.Ed448.X86_64
