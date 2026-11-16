module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Proof.Framework.X86_64.ModeSim
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.KernelList
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.SpTest

/-!
# The tests of every instruction, in one match (x86-64)

The proofs of a function's code have the kernel test every instruction of
it: that it does not touch MXCSR (`touchesMxcsr`: nor load it), that it leaves `rsp` as it is
(`Artifact.spSafe`), that it never writes `rsp`, not even as a frame does,
that it does not touch `rsp` (`Code.InlineOk`). Each test is a `match` on
the instruction, which costs the kernel from a tenth to a third of a
millisecond at every instruction it has not met before ("The match on the
instruction, with its cases closed", `Taint.lean`), and each is a walk of
the code.

`instrBitsK i` is the four tests of `i` as the bits of one number, by one
match whose cases are closed (`inline_match%`), and `hasBits m i` says that
the tests of the mask `m` hold of `i`. The kernel remembers `instrBitsK i`,
so the tests of an instruction cost one match however many of them, and
pieces of code, are checked in a declaration, and `c.allInstrs (hasBits m)`
is one walk of `c` for all the tests of `m`: `Code.noMx_of_bits`,
`Code.noTouchMx_of_bits`, `Code.sp_of_bits`, `Code.spSafe_of_bits`, `Code.noRsp_of_bits` and
`Code.rspFree_of_bits` give each test's own statement from it.
`Code.InlineOkB m` is `Code.InlineOk` and the tests of `m`, in one walk
(`Code.inlineOk_of_B`, `Code.allInstrs_of_inlineOkB`).
-/

@[expose] public section

namespace VG.X86_64

/-- The mask of the test that an instruction does not touch MXCSR, so does not load it. -/
abbrev bMx : Nat := 1
/-- The mask of the test that an instruction leaves `rsp` as it is (`Taint.keepsSp`). -/
abbrev bSp : Nat := 2
/-- The mask of the test that an instruction never writes `rsp`, not even as a frame does. -/
abbrev bNs : Nat := 4
/-- The mask of the test that an instruction does not touch `rsp` (`Instr.rspFree`). -/
abbrev bFree : Nat := 8

/-- The tests of an instruction, as the bits of a number. -/
def instrBits (i : Instr) : Nat :=
  (!touchesMxcsr i).toNat + 2 * (Taint.keepsSp i).toNat + 4 * (!Taint.clobbers i .rsp).toNat + 8 * i.rspFree.toNat

/-- `instrBits`, in one match with its cases closed. -/
def instrBitsK : Instr → Nat := inline_match% instrBits touchesMxcsr Taint.keepsSp Taint.clobbers Taint.dstOf Instr.rspFree

theorem instrBitsK_eq (i : Instr) : instrBitsK i = instrBits i := by
  cases i with
  | xop op => cases op <;> rfl
  | _ => rfl

/-- Whether the tests of the mask `m` hold of `i`: for the kernel. -/
def hasBits (m : Nat) (i : Instr) : Bool := Nat.beq (Nat.land (instrBitsK i) m) m

theorem testBit_of_hasBits {m : Nat} {i : Instr} (k : Nat) (hm : m.testBit k = true) (h : hasBits m i = true) :
    (instrBits i).testBit k = true := by
  rw [hasBits, instrBitsK_eq] at h
  have := congrArg (·.testBit k) (Nat.eq_of_beq_eq_true h)
  simp only [Nat.land_eq, Nat.testBit_and, hm, Bool.and_true] at this
  exact this

/-- Each test is its bit of `instrBits`. -/
theorem instrBits_bits (i : Instr) :
    (instrBits i).testBit 0 = !touchesMxcsr i ∧ (instrBits i).testBit 1 = Taint.keepsSp i ∧
    (instrBits i).testBit 2 = !Taint.clobbers i .rsp ∧ (instrBits i).testBit 3 = i.rspFree := by
  unfold instrBits
  cases touchesMxcsr i <;> cases Taint.keepsSp i <;> cases Taint.clobbers i .rsp <;> cases i.rspFree <;> decide

theorem noTouchMx_of_hasBits {m : Nat} {i : Instr} (hm : m.testBit 0 = true) (h : hasBits m i = true) :
    (!touchesMxcsr i) = true :=
  (instrBits_bits i).1.symm.trans (testBit_of_hasBits 0 hm h)

theorem noMx_of_hasBits {m : Nat} {i : Instr} (hm : m.testBit 0 = true) (h : hasBits m i = true) :
    (!loadsMxcsr i) = true := by
  have h := noTouchMx_of_hasBits hm h
  unfold loadsMxcsr
  split
  · exact h
  · rfl

theorem keepsSp_of_hasBits {m : Nat} {i : Instr} (hm : m.testBit 1 = true) (h : hasBits m i = true) :
    Taint.keepsSp i = true :=
  (instrBits_bits i).2.1.symm.trans (testBit_of_hasBits 1 hm h)

theorem noRsp_of_hasBits {m : Nat} {i : Instr} (hm : m.testBit 2 = true) (h : hasBits m i = true) :
    (!Taint.clobbers i .rsp) = true :=
  (instrBits_bits i).2.2.1.symm.trans (testBit_of_hasBits 2 hm h)

theorem rspFree_of_hasBits {m : Nat} {i : Instr} (hm : m.testBit 3 = true) (h : hasBits m i = true) :
    i.rspFree = true :=
  (instrBits_bits i).2.2.2.symm.trans (testBit_of_hasBits 3 hm h)

/-- The tests of `m`, from those of a mask with more. -/
theorem hasBits_of_lor {a m : Nat} {i : Instr} (h : hasBits (Nat.lor a m) i = true) : hasBits m i = true := by
  rw [hasBits] at h ⊢
  have h := Nat.eq_of_beq_eq_true h
  refine Nat.beq_eq_true_eq _ _ ▸ Nat.eq_of_testBit_eq fun k => ?_
  have := congrArg (·.testBit k) h
  simp only [Nat.land_eq, Nat.lor_eq, Nat.testBit_and, Nat.testBit_or] at this ⊢
  cases hx : (instrBitsK i).testBit k <;> cases hm : m.testBit k <;> simp_all

end VG.X86_64

namespace VG

open VG.X86_64

/-- A test of every instruction, from a test that implies it. -/
theorem Code.allInstrs_mono {I C : Type} {p q : I → Bool} {c : Code I C} (hpq : ∀ i, p i = true → q i = true)
    (h : c.allInstrs p = true) : c.allInstrs q = true := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h ⊢
  exact fun i hi => hpq i (h i hi)

variable {m : Nat} {c : Prog isa}

/-- No instruction loads MXCSR: of code whose instructions have the tests of `m`, `bMx` among them. -/
theorem Code.noMx_of_bits (hm : m.testBit 0 = true) (h : c.allInstrs (hasBits m) = true) :
    c.allInstrs (fun i => !loadsMxcsr i) = true :=
  Code.allInstrs_mono (fun _ => noMx_of_hasBits hm) h

/-- No instruction touches MXCSR: of code whose instructions have the tests of `m`, `bMx` among them. -/
theorem Code.noTouchMx_of_bits (hm : m.testBit 0 = true) (h : c.allInstrs (hasBits m) = true) :
    c.allInstrs (fun i => !touchesMxcsr i) = true :=
  Code.allInstrs_mono (fun _ => noTouchMx_of_hasBits hm) h

/-- No instruction writes `rsp` but as a frame does, for `bSp`. -/
theorem Code.sp_of_bits (hm : m.testBit 1 = true) (h : c.allInstrs (hasBits m) = true) :
    c.allInstrs (fun i => !isa.writesSp i) = true :=
  Code.allInstrs_of_spTest (keeps := Taint.keepsSp) (Code.allInstrs_mono (fun _ => keepsSp_of_hasBits hm) h)

/-- `Artifact.spSafe`, for `bSp`. -/
theorem Code.spSafe_of_bits (hm : m.testBit 1 = true) (h : c.allInstrs (hasBits m) = true) :
    c.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Code.sp_of_bits hm h)

/-- No instruction writes `rsp`, for `bNs`. -/
theorem Code.noRsp_of_bits (hm : m.testBit 2 = true) (h : c.allInstrs (hasBits m) = true) :
    c.allInstrs (fun i => !Taint.clobbers i .rsp) = true :=
  Code.allInstrs_mono (fun _ => noRsp_of_hasBits hm) h

/-- No instruction touches `rsp`, for `bFree`. -/
theorem Code.rspFree_of_bits (hm : m.testBit 3 = true) (h : c.allInstrs (hasBits m) = true) :
    c.allInstrs Instr.rspFree = true :=
  Code.allInstrs_mono (fun _ => rspFree_of_hasBits hm) h

/-- `Code.InlineOk`, and the tests of `m` of every instruction of the code and
of the functions it calls, in one walk of the code and one match for each
instruction: for the kernel. -/
noncomputable def Code.InlineOkB (m : Nat) : Prog isa → Bool
  | .block l => KList.all l (hasBits (Nat.lor bNs m))
  | .seq a b => a.InlineOkB m && b.InlineOkB m
  | .ite _ t e => t.InlineOkB m && e.InlineOkB m
  | .loop b _ => b.InlineOkB m
  | .call _ b => b.noCalls && b.allInstrs (hasBits (Nat.lor bFree m))
  | .frame .. => false
  | .icall .. => false

theorem Code.inlineOk_of_B (h : c.InlineOkB m = true) : c.InlineOk = true := by
  induction c with
  | block l =>
    simp only [InlineOkB, InlineOk, KList.all_eq, List.all_eq_true] at h ⊢
    exact fun i hi => noRsp_of_hasBits (Nat.testBit_or .. ▸ Bool.or_eq_true_iff.mpr (.inl rfl)) (h i hi)
  | seq a b iha ihb =>
    simp only [InlineOkB, InlineOk, Bool.and_eq_true] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | ite _ t e iht ihe =>
    simp only [InlineOkB, InlineOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihe h.2⟩
  | loop b _ ih => exact ih h
  | call _ b _ =>
    simp only [InlineOkB, InlineOk, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, Code.rspFree_of_bits (Nat.testBit_or .. ▸ Bool.or_eq_true_iff.mpr (.inl rfl)) h.2⟩
  | frame => simp only [InlineOkB, Bool.false_eq_true] at h
  | icall => simp only [InlineOkB, Bool.false_eq_true] at h

/-- The tests of `m` hold of every instruction of code that is `InlineOkB m`. -/
theorem Code.allInstrs_of_inlineOkB (h : c.InlineOkB m = true) : c.allInstrs (hasBits m) = true := by
  rw [Code.allInstrs_eq]
  induction c with
  | block l =>
    simp only [InlineOkB, KList.all_eq, List.all_eq_true] at h
    simp only [instrs, List.all_eq_true]
    exact fun i hi => hasBits_of_lor (h i hi)
  | seq a b iha ihb =>
    simp only [InlineOkB, Bool.and_eq_true] at h
    simp only [instrs, List.all_append, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | ite _ t e iht ihe =>
    simp only [InlineOkB, Bool.and_eq_true] at h
    simp only [instrs, List.all_append, Bool.and_eq_true]
    exact ⟨iht h.1, ihe h.2⟩
  | loop b _ ih => exact ih h
  | call _ b _ =>
    simp only [InlineOkB, Bool.and_eq_true, Code.allInstrs_eq, List.all_eq_true] at h
    simp only [instrs, List.all_eq_true]
    exact fun i hi => hasBits_of_lor (h.2 i hi)
  | frame => simp only [InlineOkB, Bool.false_eq_true] at h
  | icall => simp only [InlineOkB, Bool.false_eq_true] at h

end VG
