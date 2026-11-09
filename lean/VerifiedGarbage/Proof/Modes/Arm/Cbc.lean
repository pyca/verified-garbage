module

public import VerifiedGarbage.Proof.Modes.Arm.SeqCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Modes.Arm.SeqLoop
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# CBC as a mode one block at a time on ARMv7

`Impl.Modes.Arm.cbcEnc` and `cbcDec` run CBC (SP 800-38A §6.2,
`Spec/Cbc.lean`): from the IV in the chaining block, whatever the spare
block holds, `runSeq` gives `Spec.Cbc.encrypt` and `Spec.Cbc.decrypt`.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem xor_comm (x y : List Byte) : Spec.Cbc.xor x y = Spec.Cbc.xor y x := by
  simp only [Spec.Cbc.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## The contracts of the ciphers' modes -/

/-- The arguments of a core without rounds: `(schedule = r0, iv = r1,
data = r2, n = r3, scratch = [sp])`. -/
theorem args_plain {c : Core} (hr : c.rounds = false) (s : State) :
    ivArg c s = s.gpr .r1 ∧ dArg c s = s.gpr .r2 ∧ nArg c s = s.gpr .r3 ∧ scArg c s = stackArg s 0 ∧
      argBytes c = 4 := by
  simp [ivArg, dArg, nArg, scArg, argBytes, hr]

theorem seqArm_pub {c : Core} {S : CoreSpec c} {M : Mode} (hr : c.rounds = false) {s₁ s₂ : State}
    (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0)
    (hk : ∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1 := by intro _ h; exact absurd h List.not_mem_nil) :
    (seqArm c S M).pub s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, fun h' => absurd h' (by simp [hr]), hk⟩

/-- The arguments of a core with rounds: `(schedule = r0, rounds = r1,
iv = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
theorem args_rounds {c : Core} (hr : c.rounds = true) (s : State) :
    ivArg c s = s.gpr .r2 ∧ dArg c s = s.gpr .r3 ∧ nArg c s = stackArg s 0 ∧ scArg c s = stackArg s 1 ∧
      argBytes c = 8 := by
  simp [ivArg, dArg, nArg, scArg, argBytes, hr]

section
variable (c : Core) (S : CoreSpec c) (s : State)

end

theorem stackArg_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArg (s.withRegions rd wr) i = stackArg s i := rfl

theorem stackArgAddr_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArgAddr (s.withRegions rd wr) i = stackArgAddr s i := rfl

theorem seqArm_pubR {c : Core} {S : CoreSpec c} {M : Mode} {s₁ s₂ : State}
    (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1)
    (hk : ∀ x ∈ S.consts, s₁.syms x.1 = s₂.syms x.1 := by intro _ h; exact absurd h List.not_mem_nil) :
    (seqArm c S M).pub s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, fun _ => h.2.2.2.2.2.2, hk⟩

/-- A core and a mode whose code between the calls passes the taint checks
give a function that is correct and constant time under `seqArm`, and so
under any contract `seqArm` implies. -/
theorem seq_verified {c : Core} (S : CoreSpec c) {M : Mode} (hM : ModeOk c M) (hT : SeqTaint c M)
    {k : Contract isa} (hk : (seqArm c S M).Implies k) : Verified Arm.target (c.seq M) k :=
  Verified.of_correct (fun _ hs => seq_wp S hM hs) (seq_ct S hM hT) hk

end VG.Proof.Modes.Arm
