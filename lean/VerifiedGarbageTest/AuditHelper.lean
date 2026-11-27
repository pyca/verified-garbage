module

/-!
# A helper of the test library that the audits must see

`VerifiedGarbageTest/AuditImported.lean` imports it and checks that the
emitter's audits report what it declares: an axiom, an `implemented_by`, an
`initialize`, a `csimp` theorem and a `VG.Spec` definition outside `Spec/`. The
audits read what an imported module holds from its audit records
(`TCB/AuditRecords.lean`), and once trusted every module not named
`VerifiedGarbage.…` as one of Lean or a dependency, whose records they ignored
(https://github.com/pyca/verified-garbage/issues/6304).
-/

-- separate module: what it declares must reach `AuditImported` through an import

@[expose] public section

namespace VG.Test.AuditHelper

/-- Not one of the three standard axioms. -/
axiom unsupported : True

theorem usesUnsupported : True := unsupported

def plusOne (x : Nat) : Nat := x + 1

/-- The kernel sees the identity; compiled code adds one. -/
@[implemented_by plusOne] def ident (x : Nat) : Nat := x

def same (x : Nat) : Nat := x

def same' (x : Nat) : Nat := x

/-- The compiler rewrites `same` to `same'` in whatever it compiles later. -/
@[csimp] theorem same_eq : @same = @same' := rfl

/-- Runs when a module importing this one is loaded. -/
initialize counter : Nat ← pure 0

end VG.Test.AuditHelper

/-- A contract that `Spec/` never declared. -/
def VG.Spec.Fake.helperContract : Nat := 0
