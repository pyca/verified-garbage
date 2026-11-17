module

public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Rc4.AArch64.Lit
public import VerifiedGarbage.Impl.Rc4.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Rc4.AArch64.Lit
meta import VerifiedGarbage.Impl.Rc4.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64
meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- Key scheduling has no secret-dependent control flow or memory address:
the key bytes, `j` and the table indices stay in vector registers. -/
theorem init_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2])) init := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- `init`, then what it leaves cleared: the vector registers that held the
table and the key (`v0`–`v7`, `v16`–`v31`), and the high halves of `v8`–`v13`,
whose low halves it restores and which the calling convention does not
preserve, from `x9`, zeroed first. -/
abbrev initCleared : Prog isa :=
  Impl.Residue.AArch64.withClearsHi [.x9]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
     .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none .x9 [.v8, .v9, .v10, .v11, .v12, .v13] init

/-- `initCleared` returns without secret residue, with a 32-bit result
(`RTaintL.noResidue_of_check`, which sees the low and high halves of
`v8`–`v13` public apart). -/
theorem initCleared_noResidue (k : Contract isa) : NoResidue initCleared k 32 :=
  RTaintL.noResidue_of_check ⟨_, by taint_decide⟩ k

end VG.Proof.Rc4.AArch64
