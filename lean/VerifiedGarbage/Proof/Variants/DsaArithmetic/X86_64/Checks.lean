module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks

/-!
# What the kernel evaluates of a DSA backend's entry points

A backend (`Backend`, `Proof/Dsa/X86_64/Backend.lean`) asks of each of its
eight entry points that its calls can be inlined, that it never touches MXCSR,
that it writes `rsp` only by its calls, and how much stack it uses: tests the
kernel evaluates on the code, each a `match` on every instruction it has not
met before. It remembers what it has evaluated only within one declaration,
and the entry points are built of the same code (the arithmetic they call,
and most of what is around it): so one declaration states the tests of all
eight (`Checks`), with the tests of an instruction in one match
(`Proof/Framework/X86_64/InstrBits.lean`), and a backend proves it by one
evaluation (`Checks.of_eval`).
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64

open VG VG.X86_64 VG.Impl.Dsa.X86_64

/-- The tests of an entry point `c`, which is `ci` with its calls inlined,
in `stack` bytes of stack: for the kernel. -/
noncomputable def entryOk (stack : Nat) (c ci : Prog isa) : Bool :=
  c.InlineOkB (bMx + bSp) && (ci.allInstrs (hasBits bMx) && Nat.ble c.x86_64Depth stack)

/-- What `entryOk` shows of an entry point. -/
structure EntryOk (stack : Nat) (c ci : Prog isa) : Prop where
  inl : c.InlineOk = true
  mx : ci.allInstrs (fun i => !loadsMxcsr i) = true
  mxFree : c.allInstrs (fun i => !touchesMxcsr i) = true
  sp : c.all (fun i => !isa.writesSp i) = true
  depth : c.x86_64Depth ≤ stack

theorem EntryOk.of_eval {stack : Nat} {c ci : Prog isa} (h : entryOk stack c ci = true) : EntryOk stack c ci := by
  simp only [entryOk, Bool.and_eq_true, Nat.ble_eq] at h
  exact ⟨Code.inlineOk_of_B h.1, Code.noMx_of_bits rfl h.2.1,
    Code.noTouchMx_of_bits rfl (Code.allInstrs_of_inlineOkB h.1),
    Code.spSafe_of_bits rfl (Code.allInstrs_of_inlineOkB h.1), h.2.2⟩

/-- The entry points, as functions of the arithmetic they call. -/
def entries : List (Prog isa → (Nat → Nat → Nat → Prog isa) → Prog isa) :=
  [SignVerify.sign, Prevalidated.validate, Prevalidated.verify, Generate.checkParameters, Generate.deriveKey,
    PrevalidatedSign.sign, PrevalidatedSign.validate, Generate.deriveChecked]

/-- The tests of every entry point with the calls `sq` and `mul`, which run
`sqI` and `mulI`. -/
structure Checks (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sqI : Prog isa)
    (mulI : Nat → Nat → Nat → Prog isa) (stack : Nat) : Prop where
  sign : EntryOk stack (SignVerify.sign sq mul) (SignVerify.sign sqI mulI)
  validate : EntryOk stack (Prevalidated.validate sq mul) (Prevalidated.validate sqI mulI)
  verify : EntryOk stack (Prevalidated.verify sq mul) (Prevalidated.verify sqI mulI)
  parameters : EntryOk stack (Generate.checkParameters sq mul) (Generate.checkParameters sqI mulI)
  derive : EntryOk stack (Generate.deriveKey sq mul) (Generate.deriveKey sqI mulI)
  prevalidatedSign : EntryOk stack (PrevalidatedSign.sign sq mul) (PrevalidatedSign.sign sqI mulI)
  validatePrivate : EntryOk stack (PrevalidatedSign.validate sq mul) (PrevalidatedSign.validate sqI mulI)
  deriveChecked : EntryOk stack (Generate.deriveChecked sq mul) (Generate.deriveChecked sqI mulI)

/-- `Checks`, by one evaluation: `.of_eval (by decide +kernel)`. -/
theorem Checks.of_eval {sq : Prog isa} {mul : Nat → Nat → Nat → Prog isa} {sqI : Prog isa}
    {mulI : Nat → Nat → Nat → Prog isa} {stack : Nat}
    (h : (entries.all fun f => entryOk stack (f sq mul) (f sqI mulI)) = true) : Checks sq mul sqI mulI stack := by
  simp only [entries, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
  exact ⟨.of_eval h₁, .of_eval h₂, .of_eval h₃, .of_eval h₄, .of_eval h₅, .of_eval h₆, .of_eval h₇, .of_eval h₈⟩

end VG.Proof.Variants.DsaArithmetic.X86_64
