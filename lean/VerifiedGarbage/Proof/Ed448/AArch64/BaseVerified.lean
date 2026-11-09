module

import VerifiedGarbage.Proof.Ed448.AArch64.Base.Main
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Ed448.AArch64.Base.Main
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
meta import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 base-point multiplication on AArch64: `Verified`

Correctness including the ABI; constant time (by taint tracking: the only
branches are on the counters, every address is an argument or the static's
address plus a constant or a counter, and the digits' masks only select); and
a concrete state satisfying the signature's contract, under the calling
convention with the comb's tables (`Abi.withConsts combConsts`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)
open VG.Proof.X448.AArch64.Base (CombHeld combWords_length combConsts_eq satMem satMem_held)

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

/-- The analysis, of the code without what it does not read. -/
theorem scalarBase_check :
    ∃ h, ((taintS [combSym]).check (Taint.ofRegs [.x0, .x1, .x2]) scalarBase h).isSome = true := by
  apply exists_isSome_of_eraseT
  refine Split.exists_isSome (c' := ?c') ?s ?g
  case s =>
    simp only [scalarBase, encode, Code.eraseT, Impl.X448.AArch64.Fast.invert, ops_eraseT, sqn_eraseT]
    exact .refl _
  case g => taint_decide_sum [VG.Proof.Ed448.AArch64.CombBase.combSum, VG.Proof.Ed448.AArch64.addSum, VG.Proof.Ed448.AArch64.powSum]

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase :=
  let ⟨_, hc⟩ := scalarBase_check
  VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h0, h1, h2]⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) hc

theorem scalarBase_baseOk : BaseOk := ⟨scalarBase_ok, scalarBase_ct⟩

end VG.Proof.Ed448.AArch64
