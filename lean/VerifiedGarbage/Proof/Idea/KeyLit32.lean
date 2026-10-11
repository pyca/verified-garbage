import VerifiedGarbage.Impl.Idea.Key32
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The 32-bit key schedule's bit groups, once

`expandGroups32 w`, the groups of bits of schedule word `w` that the 32-bit
targets' key expansion moves together, as a table (`materialize_table`), as
`KeyLit.lean` for the 64-bit targets.
-/

namespace VG

materialize_table Impl.Idea.expandGroups32 26

end VG
