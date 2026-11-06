module

public import VerifiedGarbage.Proof.X25519.AArch64.Top
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.X25519.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.AArch64.Top
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.X25519.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# X25519 on AArch64: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant, or the working space plus a
counter), satisfiability, and the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.X25519.x25519AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

end VG.Proof.X25519.AArch64
