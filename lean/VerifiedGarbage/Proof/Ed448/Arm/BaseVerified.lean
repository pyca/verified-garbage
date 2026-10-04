import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.Ed448.Arm.BaseLit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 base-point multiplication on ARMv7: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter), satisfiability,
and the shared contract of `Spec/`, given that the ladder the code computes
encodes as `[k]B` (`Proof.Ed448.BaseLadderOk`, proven with the group law in
`Proof/Ed448/Facts.lean`, which only the registration file imports).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm
open VG.Proof.Ed448 (BaseLadderOk decodeLE_below)

/-- `vg_ed448_scalar_base(out = r0, scalar = r1, scratch = r2)`. -/
def scalarBaseLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let scalar : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [scalar] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ scalar.Disjoint ws ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧ s.sp = t.sp

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : BasePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

def scalarBaseSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (hl : BaseLadderOk) (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_ladder (BasePre.of hs)
  refine ⟨t, s', he, ⟨h.1, Exec.sp he⟩, ?_⟩
  change Spec.Ed448.bytesAt s'.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul _ Spec.Ed448.basePoint)
  rw [h.2, hl _ (decodeLE_below (by simp [Spec.Ed448.bytesAt]))]

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, _⟩
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem scalarBase_verified (hl : BaseLadderOk) :
    Verified Arm.target scalarBase (Spec.Ed448.scalarBaseContract Arm.abi) :=
  Verified.of_correct (scalarBase_ok hl) scalarBase_ct (by
    sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
      Spec.Ed448.scratchWords, scalarBaseLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [scalarBaseSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scalarBaseSat)

end VG.Proof.Ed448.Arm
