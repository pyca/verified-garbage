module

public meta import Lean
public meta import VerifiedGarbage.TCB.AuditRecords

/-!
# Axiom audit

**Trusted.** `#assert_standard_axioms c` fails unless the constant `c` (and so
everything it depends on, transitively) uses only Lean's three standard
axioms. In particular this rejects `sorry` (`sorryAx`) and anything proven by
`native_decide`/`bv_decide`, which add an auxiliary axiom asserting the
result of compiled code and thus trust the compiler.

It walks the constants of the file it runs in, and takes what an imported constant
depends on from the audit records its module wrote when it was built
(`TCB/AuditRecords.lean`), which saw its proofs: so it runs in a module too, which
sees the theorems it imports without their proofs.
-/

public meta section

namespace VG

open Lean Elab Command

def standardAxioms : List Name := AuditRecords.standardAxioms

elab "#assert_standard_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs := AuditRecords.axiomsIn (← getEnv) n
  let bad := axs.filter (!standardAxioms.contains ·)
  unless bad.isEmpty do
    throwError m!"{n} depends on non-standard axioms: {bad.toList}"
  -- Through Lean's and Mathlib's constants it may depend on the others too, which
  -- `TCB/AuditBase.lean` does not list: only the non-standard ones matter.
  logInfo m!"{n} depends on no axiom but the standard ones (this project's proofs use {axs.toList})"

end VG
