module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Offset

/-! Entropy cutting changes only the caller's private-key output buffer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem ArgumentMemory.after_output {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    {dst : BitVec 32} {n : Nat} (h : ArgumentMemory p slots s)
    (frame : Frame [⟨State.addr dst, n⟩] s.mem t.mem) (rest : Rest rs s t)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr dst, n⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr dst, n⟩)
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) : ArgumentMemory p slots t := by
  refine h.after_frame frame rest (by simpa using domainSep) ?_
  intro d hd r hr
  rw [List.mem_singleton] at hr
  subst r
  exact stackSep.sub_left (Offset.sub_base _ (saved d hd))

end VG.Proof.Ffdh.Arm
