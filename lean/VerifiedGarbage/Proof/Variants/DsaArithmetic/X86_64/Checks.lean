module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks

/-!
# What the kernel evaluates of a DSA backend's arithmetic, inlined

The functions over a backend's arithmetic call it through slots
(`Proof/Dsa/X86_64/Slots.lean`), and their proofs are those of their code
with the arithmetic inlined, which must not load MXCSR: a test the kernel
evaluates on that code, a `match` on every instruction it has not met before.
It remembers what it has evaluated only within one declaration, and the
functions are built of the same code (the arithmetic, and most of what is
around it): so one declaration states the tests of all seven (`Checks`), with
the test of an instruction in one match
(`Proof/Framework/X86_64/InstrBits.lean`), and a backend proves it by one
evaluation (`Checks.of_eval`).
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64

open VG VG.X86_64 VG.Impl.Dsa.X86_64

/-- The functions over the arithmetic. -/
def entries : List (Prog isa → (Nat → Nat → Nat → Prog isa) → Prog isa) :=
  [Prevalidated.validate, Prevalidated.verify, Generate.checkParameters, Generate.deriveKey,
    PrevalidatedSign.sign, PrevalidatedSign.validate, Generate.deriveChecked]

/-- That each function over the arithmetic `sqI` and `mulI`, inlined, never
loads MXCSR. -/
structure Checks (sqI : Prog isa) (mulI : Nat → Nat → Nat → Prog isa) : Prop where
  validate : (Prevalidated.validate sqI mulI).allInstrs (fun i => !loadsMxcsr i) = true
  verify : (Prevalidated.verify sqI mulI).allInstrs (fun i => !loadsMxcsr i) = true
  parameters : (Generate.checkParameters sqI mulI).allInstrs (fun i => !loadsMxcsr i) = true
  derive : (Generate.deriveKey sqI mulI).allInstrs (fun i => !loadsMxcsr i) = true
  prevalidatedSign : (PrevalidatedSign.sign sqI mulI).allInstrs (fun i => !loadsMxcsr i) = true
  validatePrivate : (PrevalidatedSign.validate sqI mulI).allInstrs (fun i => !loadsMxcsr i) = true
  deriveChecked : (Generate.deriveChecked sqI mulI).allInstrs (fun i => !loadsMxcsr i) = true

/-- `Checks`, by one evaluation: `.of_eval (by decide +kernel)`. -/
theorem Checks.of_eval {sqI : Prog isa} {mulI : Nat → Nat → Nat → Prog isa}
    (h : (entries.all fun f => (f sqI mulI).allInstrs (hasBits bMx)) = true) : Checks sqI mulI := by
  simp only [entries, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  exact ⟨Code.noMx_of_bits rfl h₁, Code.noMx_of_bits rfl h₂, Code.noMx_of_bits rfl h₃, Code.noMx_of_bits rfl h₄,
    Code.noMx_of_bits rfl h₅, Code.noMx_of_bits rfl h₆, Code.noMx_of_bits rfl h₇⟩

end VG.Proof.Variants.DsaArithmetic.X86_64
