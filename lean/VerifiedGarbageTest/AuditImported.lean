module

import VerifiedGarbage.TCB.Audit
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbageTest.AuditHelper
meta import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Axioms

/-!
# The audits see what the test library declares

What `VerifiedGarbageTest/AuditHelper.lean` declares reaches the axiom audit
(`#assert_standard_axioms`), the override audit
(`#assert_no_compiler_overrides`) and the spec-origin audit
(`#assert_spec_origin`) through an import, from the helper's audit records:
a module's records are read whatever its name
(https://github.com/pyca/verified-garbage/issues/6304).
-/

-- `#guard_msgs` compares every message of its command, which would include
-- the lakefile's profile of it (`ci/lean_profile.py`), different on every
-- machine.
set_option profiler false

public section

namespace VG.Test.AuditImported

theorem throughImport : True := AuditHelper.usesUnsupported

def usesIdent : Nat := AuditHelper.ident 0

/-- error: VG.Test.AuditImported.throughImport depends on non-standard axioms: [VG.Test.AuditHelper.unsupported] -/
#guard_msgs in
#assert_standard_axioms throughImport

/-- error: the compiled code of [VG.Test.AuditImported.usesIdent] is not what the kernel checked:
@[implemented_by] on VG.Test.AuditHelper.ident
@[init] on VG.Test.AuditHelper.counter
@[csimp] VG.Test.AuditHelper.same_eq -/
#guard_msgs in
#assert_no_compiler_overrides usesIdent

end VG.Test.AuditImported

/-- error: these `VG.Spec` names are not declared in `Spec/`:
VG.Spec.Fake.helperContract (in VerifiedGarbageTest.AuditHelper) -/
#guard_msgs in
#assert_spec_origin
