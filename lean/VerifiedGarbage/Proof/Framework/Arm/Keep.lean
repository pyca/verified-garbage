module

public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-!
# What ARMv7 code keeps

Untrusted: everything here is checked by Lean. `WP.keep` adds `Rest rs s s'`
(`s'` differs from `s` only in the registers `rs` and memory, with the same
permissions and stack pointer) to a postcondition for code without calls
whose instructions write only `rs` (`writesOnly`, decided by evaluation).
-/

@[expose] public section

namespace VG.Arm

open VG.Proof.X25519.Arm (Rest)

/-- Every instruction of the code writes only registers among `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  (instrs c).all fun i => (dsts i).all fun r => rs.contains r

/-- Registers that no instruction of code without calls writes keep their
values. -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa c s Q) (hc : writesOnly rs c = true)
    (hn : c.noCalls = true := by decide) :
    WP isa c s fun s' => Q s' ∧ Rest rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, Exec.sp he⟩⟩
  unfold writesOnly at hc
  rw [List.all_eq_true] at hc
  have hh := hc i hi
  rw [List.all_eq_true] at hh
  refine clobbers_eq_false fun hd => hr ?_
  exact List.contains_iff_mem.mp (hh r hd)

end VG.Arm
