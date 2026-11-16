module

public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
meta import VerifiedGarbage.Impl.MlKem.AArch64.Paired
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! # Public-address timing for paired and singleton SHAKE128 generation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem ct_eraseOff_eq {c d : Prog isa} (rs : List Reg)
    (he : Code.eraseOff c=d) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) d hc).isSome=true) :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs rs)) c :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs rs) (fun _ _ _ _ h => h)
    (Taint.isSome_check_of_eraseOff he h)

/-- `ct_eraseOff_eq` by the vector-aware analysis. -/
theorem vct_eraseOff_eq {c d : Prog isa} (rs : List Reg)
    (he : Code.eraseOff c=d) {hc : VG.Taint.Hint VectorTaint.T}
    (h : (VectorTaint.taint.check (VectorTaint.ofRegs rs) d hc).isSome=true) :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs rs)) c :=
  VectorTaint.constantTime (Taint.ofRegs rs) (fun _ _ _ _ h => h)
    (VectorTaint.isSome_check_of_eraseOff he h)

theorem init_ct (sb ss a b k : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28]))
    (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k)) := by
  unfold Impl.MlKem.AArch64.Paired.init ptrTo
  split <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x28])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem nextBlock_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19])) (nextBlock sha3) := by
  cases sha3
  -- With the call written out, the checks read the literal of the paired Keccak's code
  -- (`X2.code false`, `X2.code true`), which they do not look for behind `nextBlock`.
  · exact VectorTaint.constantTime (Taint.ofRegs [.x19]) (fun _ _ _ _ h => h)
      (by unfold nextBlock Impl.Sha3.AArch64.Neon.X2.call; taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
      (fun _ _ _ _ h => h) (by unfold nextBlock Impl.Sha3.AArch64.Neon.X2.call; taint_decide)

end VG.Proof.MlKem.AArch64.Paired
