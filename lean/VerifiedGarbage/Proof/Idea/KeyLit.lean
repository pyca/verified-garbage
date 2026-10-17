module

public import VerifiedGarbage.Impl.Idea.Key
meta import VerifiedGarbage.Impl.Idea.Key
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# The key schedule's bit groups, once

`expandGroups q`, the groups of bits of schedule quadword `q` that each
target's key expansion moves together, as a table (`materialize_table`): the
literals of both targets' code (`Lit.lean`) and their checks of each quadword
(`Key.lean`, `lit_decide`) read it rather than group the 64 bits again.
-/

@[expose] public section

namespace VG

materialize_table Impl.Idea.expandGroups 13

end VG
