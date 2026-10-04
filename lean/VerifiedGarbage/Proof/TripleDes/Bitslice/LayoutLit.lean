import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The bitsliced layout's tables, as literals

The words of the bits of IP, `E`'s bits and P's destinations, each
evaluated once (`materialize_table`), from the permutations' lists: the
literals of the code that reads them (`SboxLit`, `Lit`) and the kernel's
checks of facts about them (`lit_decide`) read one number rather than walk
the permutations again.
-/

namespace VG

materialize_table Impl.TripleDes.Bitslice.ipWord 64
materialize_table Impl.TripleDes.Bitslice.eBit 48
materialize_table Impl.TripleDes.Bitslice.outBit 8 4

end VG
