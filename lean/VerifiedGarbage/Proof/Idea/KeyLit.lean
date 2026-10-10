import VerifiedGarbage.Impl.Idea.Key
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The key schedule's bit groups, once

`expandGroups q`, the groups of bits of schedule quadword `q` that each
target's key expansion moves together, as a table (`materialize_table`): the
literals of both targets' code (`Lit.lean`) and their checks of each quadword
(`Key.lean`, `lit_decide`) read it rather than group the 64 bits again.
-/

namespace VG

materialize_table Impl.Idea.expandGroups 13

end VG
