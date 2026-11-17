module

public import VerifiedGarbage.Proof.X448.Contract
public import VerifiedGarbage.Proof.X448.Arm.Main
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.X448.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.Arm.Main
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.X448.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.X448.Contract

/-!
# X448 on ARMv7: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter; with `umaal`,
by `taintU`, for which what a `umaal` writes is secret),
satisfiability, and the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm

variable {fv : Bool}

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448Arm.pre s) :
    ∃ t s', Exec isa (Impl.X448.Arm.x448 fv) s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448Arm.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448Arm.pre Proof.X448.x448Arm.pub
    (Impl.X448.Arm.x448 fv) := by
  obtain ha : ∀ s₁ s₂, Proof.X448.x448Arm.pre s₁ → Proof.X448.x448Arm.pre s₂ →
      Proof.X448.x448Arm.pub s₁ s₂ → VG.Arm.Taint.Agree (Taint.ofRegs [.r0, .r1, .r2, .r3]) s₁ s₂ := by
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, _⟩
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  cases fv
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ha (by native_taint_decide)
  · exact VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ha (by taint_decide)

theorem x448_verified :
    Verified Arm.target (Impl.X448.Arm.x448 fv) (Proof.X448.x448Contract Arm.abi) :=
  Verified.of_correct x448_ok x448_ct (by
    sig_implies [Proof.X448.x448Contract, Proof.X448.x448Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.X448.x448Arm]
      [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState)

end VG.Proof.X448.Arm
