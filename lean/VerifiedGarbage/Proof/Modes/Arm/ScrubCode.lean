module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal
public import VerifiedGarbage.Impl.StackScratch.Arm

-- separate module: the ARMv7 scrub proofs of every block cipher's modes share it (Blowfish, CAST5, IDEA, SEED, Camellia, SM4, AES)

/-!
# The frames of the block cipher modes on ARMv7

What `Arm.Scrub.scrubRegF` needs of a mode's code (`armStack c ≤ stack`,
`noIcall c`), from its core's: the one-block-at-a-time modes
(`Core.seq`, `Core.seqFinal`) use the stack only in the call of their core,
in a frame of 8 bytes if the core takes a working space, and the stack
scratch wrappers (`withStackScratchWiped`, `withRegScratchWiped`) add their
buffer. Each block cipher's ARMv7 scrub proof composes these with what its
ECB function's code is evaluated to (`lit_decide`), rather than evaluating
the modes with it.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG.Arm VG.Arm.FrameStack VG.Arm.Scrub VG.Impl.Modes.Arm

/-- The stack a call of the core uses beyond its code's: the frame that
pushes its working space's address, if it takes one. -/
def callExtraArm (c : Core) : Nat := if c.stackScratch = 0 then 0 else 8

theorem callStep_scrubArm {c : Core} {n : Nat}
    (hc : armStack c.code + callExtraArm c ≤ n ∧ noIcall c.code = true) :
    armStack c.callStep ≤ n ∧ noIcall c.callStep = true := by
  unfold Core.callStep callExtraArm at *
  split <;> rename_i h <;> simp only [h, ite_true, ite_false, armStack, noIcall, List.length_cons,
    List.length_nil] at hc ⊢ <;> exact ⟨by omega, hc.2⟩

/-- A mode one block at a time uses the stack only in its core's call. -/
theorem seq_scrubArm {c : Core} {n : Nat}
    (hc : armStack c.code + callExtraArm c ≤ n ∧ noIcall c.code = true) (m : Mode) :
    armStack (c.seq m) ≤ n ∧ noIcall (c.seq m) = true := by
  obtain ⟨h₁, h₂⟩ := callStep_scrubArm hc
  simp only [Core.seq, Core.body, armStack, noIcall, h₂, Bool.and_true,
    Nat.zero_max, Nat.max_zero, and_true]
  exact Nat.max_le.mpr ⟨Nat.zero_le _, h₁⟩

/-- So does a mode over a message's last piece. -/
theorem seqFinal_scrubArm {c : Core} {n : Nat}
    (hc : armStack c.code + callExtraArm c ≤ n ∧ noIcall c.code = true) (m : Mode) :
    armStack (c.seqFinal m) ≤ n ∧ noIcall (c.seqFinal m) = true := by
  obtain ⟨h₁, h₂⟩ := callStep_scrubArm hc
  simp only [Core.seqFinal, Core.seg, Core.segRest, tailCode, armStack, noIcall, h₂, Bool.and_true,
    Nat.zero_max, Nat.max_zero, and_true]
  exact h₁

/-- A stack scratch buffer of `bytes` bytes, wiped after the code. -/
theorem withStackScratchWiped_scrubArm {bytes m words n : Nat} {c : Prog isa}
    (hc : armStack c ≤ n ∧ noIcall c = true) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped bytes m words c) ≤ n + bytes ∧
      noIcall (Impl.StackScratch.Arm.withStackScratchWiped bytes m words c) = true := by
  simp only [Impl.StackScratch.Arm.withStackScratchWiped, Impl.StackScratch.Arm.withStackScratch, armStack,
    noIcall, hc.2, Bool.and_true, Nat.zero_max, Nat.max_zero, and_true]
  omega

/-- A scratch buffer of `bytes` bytes, passed in a register, wiped after the
code. -/
theorem withRegScratchWiped_scrubArm {bytes words n : Nat} {r : Reg} {c : Prog isa}
    (hc : armStack c ≤ n ∧ noIcall c = true) :
    armStack (Impl.StackScratch.Arm.withRegScratchWiped bytes r words c) ≤ n + bytes ∧
      noIcall (Impl.StackScratch.Arm.withRegScratchWiped bytes r words c) = true := by
  simp only [Impl.StackScratch.Arm.withRegScratchWiped, Impl.StackScratch.Arm.withRegScratch, armStack,
    noIcall, hc.2, Bool.and_true, Nat.zero_max, Nat.max_zero, and_true]
  omega

end VG.Proof.Modes.Arm
