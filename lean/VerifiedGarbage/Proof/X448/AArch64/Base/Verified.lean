import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.X448.AArch64.Base.Main
import VerifiedGarbage.Proof.X448.AArch64.Base.Erase
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X448 of the base point on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the counters, every address is an argument
plus a constant or a counter, and the digits' masks only select; checked on the code
without its immediates, `Base/Erase.lean`), and the
shared contract of `Spec/`.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseAArch64.pre Proof.X448.x448BaseAArch64.pub
    Impl.X448.AArch64.Base.x448Base := by
  refine Taint.constantTime_eraseImm_of_eq (Taint.ofRegs [.x0, .x1, .x2]) ?_ x448Base_eraseImm
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448Base_ok (s : State) (hs : Proof.X448.x448BaseAArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Base.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448Base_verified :
    Verified AArch64.target Impl.X448.AArch64.Base.x448Base (Spec.X448.x448BaseContract AArch64.abi) :=
  Verified.of_correct x448Base_ok x448Base_ct (by
    sig_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      Proof.X448.x448BaseAArch64] [satState] using satState)

end VG.Proof.X448.AArch64.Base
