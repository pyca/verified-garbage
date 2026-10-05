import VerifiedGarbage.Proof.Ed448.AArch64.BaseMain
import VerifiedGarbage.Proof.Ed448.AArch64.Erase
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 base-point multiplication on AArch64: `Verified`

Correctness including the ABI, given that the reference ladder encodes `[k]B`
(`BaseLadderOk`, which the registration file passes in); constant time (by
taint tracking: the only branches are on the loop counters, and every address
is an argument plus a constant or a counter); and a concrete state satisfying
the signature's contract.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

def scalarBaseSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (hL : Proof.Ed448.BaseLadderOk) (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct hL hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, Exec.preservedV he
    (Code.allInstrs_keepsV_of_eraseOff_eq scalarBase_eraseOff (by lit_decide))⟩, h.2⟩

theorem scalarBase_noFrames : scalarBase.noFrames = true := by
  rw [← Code.noFrames_eraseOff, scalarBase_eraseOff, Code.noFrames_eraseOff]; decide +kernel

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_
    -- The hint keeps public only the pointers and the counter, which the addresses and
    -- branches use: every field operation is then analysed from the same taint.
    (Taint.isSome_check_of_eraseOff scalarBase_eraseOff
      (by taint_decide_weak fun τ => τ.inter (Taint.ofRegs [.x0, .x1, .x2, .x3, .x19, .x20])))
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

theorem scalarBase_verified (hL : Proof.Ed448.BaseLadderOk) : Verified AArch64.target scalarBase
    (Spec.Ed448.scalarBaseContract AArch64.abi) :=
  Verified.of_correct (scalarBase_ok hL) scalarBase_ct (by
    sig_implies [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, scalarBaseLocal]
      [scalarBaseSat] using scalarBaseSat)

end VG.Proof.Ed448.AArch64
