module

public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Sqr

/-!
# The point functions keep `rbp` and `r12`–`r15`

Untrusted: everything here is checked by Lean. Each function saves the
registers in `xmm0`–`xmm4`, runs field code that writes no vector register,
and restores them (`fn`), so it keeps them (`fn_keeps`): one pass over the
code, where `KeepReg.keeps` evaluated on the code would take one for each
register.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64

variable {fld : Arith} [EdArith fld]

/-- The code between a function's saves and restores (`fn`'s five each). -/
def midCode : Prog isa → List Instr
  | .block l => (l.drop 5).take (l.length - 10)
  | _ => []

theorem midCode_fn (fld : Arith) (ops : List FieldOp) : midCode (fn fld ops) = fieldCode fld ops := by
  simp [midCode, fn, saves, restores, kept]

/-- A function keeps `rbp` and `r12`–`r15` if its field code writes no vector register: one
pass over the code, where `KeepReg.keeps` would take one for each register. -/
theorem fn_keeps {fld : Arith} {ops : List FieldOp}
    (h : (midCode (fn fld ops)).all (fun i => !KeepReg.writesVec i) = true) :
    ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true := by
  rw [midCode_fn] at h
  intro r hr
  refine KeepReg.keeps_around h fun b => ?_
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

/-- The functions' bodies keep `rbp` and `r12`–`r15`. -/
theorem doubleFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (doubleFn fld t) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    exact fn_keeps (by lit_decide)

theorem addFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (addFn fld t) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    exact fn_keeps (by lit_decide)

theorem addAffineFn_keeps : ∀ r ∈ keptRegs, KeepReg.keeps r (addAffineFn fld) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;>
    exact fn_keeps (by lit_decide)

end VG.Proof.Ed25519.X86_64.Point64
