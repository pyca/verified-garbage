module

meta import VerifiedGarbage.Proof.Framework.ConflictingBounds

-- Keep the diagnostic independent of the machine's profiling times.
set_option profiler false

namespace BoundsFixture

public abbrev preLen (fold len : Nat) := fold ≤ (len - 1) % 512 ∨ len < 1409

private theorem impossible (fold len : Nat) (_ : ¬ preLen fold len) (_ : len < 512) : True := trivial

-- When fold = 448 and len = 1409, both hypotheses hold.
public theorem reachable (fold len : Nat) (_ : ¬ preLen fold len) (_ : len ≤ 1409) : True := trivial

-- The contradiction itself is the statement this lemma documents.
@[intentional_vacuity] theorem emptyInterval (n : Nat) (lo : 7 ≤ n) (hi : n < 7) : False := by omega

public theorem touching (n : Nat) (_ : 6 < n) (_ : n ≤ 6) : True := trivial

-- Each pair is compatible. A contradiction needs all three comparisons.
private theorem chain (x y z : Nat) (_ : 10 ≤ x) (_ : x ≤ y) (_ : z ≤ 4) (_ : y < 10) : True := trivial

-- x = y = 10 witnesses the shared boundary.
theorem chainBoundary (x y : Nat) (_ : 10 ≤ x) (_ : x ≤ y) (_ : y ≤ 10) : True := trivial

-- Equality can join a strict cycle even without any numeric literal.
theorem cycle (x y z : Nat) (_ : x = y) (_ : y ≤ z) (_ : z < x) : True := trivial

-- The checker treats n + 1 as an unknown Nat. It only reasons about its stated bounds.
theorem opaqueOperand (n : Nat) (_ : n + 1 ≤ 0) : True := trivial

-- Bounds on different quantities can both hold.
theorem separate (x y : Nat) (_ : 10 ≤ x) (_ : y < 5) : True := trivial

-- The spelling of a comparison alone cannot establish its semantics.
section
local instance : LT Nat := ⟨fun _ _ => True⟩
theorem otherOrder (n : Nat) (_ : n < 2) (_ : 3 ≤ n) : True := trivial
end

/--
error: conflicting bounds in BoundsFixture.chain: 10 ≤ x, x ≤ y, y < 10
---
error: conflicting bounds in BoundsFixture.cycle: x = y, y ≤ z, z < x
---
error: conflicting bounds in BoundsFixture.impossible: ¬len < 1409, len < 512
---
error: conflicting bounds in BoundsFixture.touching: 6 < n, n ≤ 6
-/
#guard_msgs (ordering := sorted) in
run_cmd VG.ConflictingBounds.checkModule

end BoundsFixture
