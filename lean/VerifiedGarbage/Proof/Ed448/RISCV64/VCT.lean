module

public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Ed448's verification equation on RISCV64: the pieces the taint analysis checks

Every piece of `verifyEquation` but the joint loop's branches on its digits
is constant time from the registers it addresses through and its counters
(`taint_decide`). The branches are on digits of `S` and `k`, which two runs
with the same inputs share, and each branch is constant time from the digit
(`VTiming.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64

/-- Code the taint analysis checks from the registers `rs`. -/
theorem ctp {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨(hP a b hab).1, fun r hr => (hP a b hab).2 r (Taint.mem_ofRegs.mp hr)⟩) h

variable {P : State → State → Prop}

theorem prefix_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], a.gpr r = b.gpr r) :
    RelCT isa P vPrefix fun _ _ => True := ctp _ hP (by taint_decide)

theorem init_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a3], a.gpr r = b.gpr r) :
    RelCT isa P (.block (constField RX 0 ++ constField RY 1 ++ constField RZ 1 ++ ([.li .t1 464] : List Instr)))
      fun _ _ => True := ctp _ hP (by taint_decide)

theorem dec_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.t1], a.gpr r = b.gpr r) :
    RelCT isa P (.block [.addi .t1 .t1 (-1)]) fun _ _ => True := ctp _ hP (by taint_decide)

theorem dbl_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a3], a.gpr r = b.gpr r) :
    RelCT isa P (opsProg dblOps) fun _ _ => True := ctp _ hP (by taint_decide)

theorem load2_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .t1], a.gpr r = b.gpr r) :
    RelCT isa P (.block (loadDigit 2)) fun _ _ => True := ctp _ hP (by taint_decide)

theorem load3_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .t1], a.gpr r = b.gpr r) :
    RelCT isa P (.block (loadDigit 3)) fun _ _ => True := ctp _ hP (by taint_decide)

theorem baseBody_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a3, .a5], a.gpr r = b.gpr r) :
    RelCT isa P baseBody fun _ _ => True := ctp _ hP (by taint_decide)

theorem keyBody_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a3, .a5], a.gpr r = b.gpr r) :
    RelCT isa P keyBody fun _ _ => True := ctp _ hP (by taint_decide)

theorem addNegR_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a3], a.gpr r = b.gpr r) :
    RelCT isa P addNegR fun _ _ => True := ctp _ hP (by taint_decide)

theorem vFinish_ct (hP : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ [Reg.a0, .a3], a.gpr r = b.gpr r) :
    RelCT isa P (.block vFinish) fun _ _ => True := ctp _ hP (by taint_decide)

end VG.Proof.Ed448.RISCV64
