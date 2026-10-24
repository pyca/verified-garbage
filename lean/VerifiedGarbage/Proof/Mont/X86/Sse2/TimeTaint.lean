module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
meta import VerifiedGarbage.Impl.Mont.X86.Sse2
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # The columns and the reduction leak only public data

Each runs with the parameters read-only: the columns inside the MCDT frame,
the parameters 12 bytes above `esp` (`colTaint`), and the reduction after it,
the parameters at `esp` (`argTaint [] 28`).
-/

@[expose] public section
namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86.Sse2

/-- Inside the MCDT frame: `esp` public, and the 28 bytes of parameters, 12
bytes above `esp`, public and never written (after 8 bytes treated as two
return addresses). -/
def colTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, stk := [none, none], argLen := 32 }

theorem columns_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree colTaint) columns :=
  VG.Taint.constantTime (A := sseTaint) colTaint (fun _ _ _ _ H => H) (by taint_decide)

/-- The reduction after the columns. -/
def rest : Prog isa := seqs [subM, .block mask, select]

theorem rest_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (argTaint [] 28)) rest :=
  VG.Taint.constantTime (A := VG.X86.taint) (argTaint [] 28) (fun _ _ _ _ H => H) (by taint_decide)

/-- The callee-saved registers' loads, at `esp`. -/
theorem restore_relCT :
    RelCT isa (fun x y => x.gpr .esp = y.gpr .esp) (.block restoreRegs) fun _ _ => True :=
  VG.RelCT.taint (A := VG.X86.taint) (VG.X86.τr [.esp]) (fun _ _ h => VG.X86.agree_regs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)

/-- `vg_rsa_mont_mul_at`'s parameters, from the arguments above `esp`. -/
theorem atParams_relCT :
    RelCT isa (fun x y => x.gpr .esp = y.gpr .esp) (.block atParams) fun _ _ => True :=
  VG.RelCT.taint (A := VG.X86.taint) (VG.X86.τr [.esp]) (fun _ _ h => VG.X86.agree_regs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)

/-- After the callee-saved registers' push: `esp` public, and the 20 bytes of
arguments above the return address, 16 bytes above `esp`, public and never
written. -/
def prTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, stk := [none, none, none, none], argLen := 24 }

/-- `vg_rsa_mont_mul`'s parameters, from the arguments and the header. -/
theorem preparedParams_constantTime :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree prTaint) (.block preparedParams) :=
  VG.Taint.constantTime (A := VG.X86.taint) prTaint (fun _ _ _ _ H => H) (by taint_decide)

end VG.Proof.Mont.X86.Sse2
