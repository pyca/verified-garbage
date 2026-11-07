module

import VerifiedGarbage.Impl.EcKey.Compressed.Root
meta import VerifiedGarbage.Impl.EcKey.Compressed.Root

/-! Exhaustive algebraic checks over a small synthetic prime field.
These exercise both square-root paths and checked parity selection, rather
than supply known-answer vectors for a supported cryptographic curve. -/

namespace VG.Test.EcCompressedRoot

open VG.Impl.EcKey.Compressed

private def root17 (a : Fin 17) : Fin 17 := rootTonelli a 1 4 3

-- Include zero, nonsquares and every requested byte parity.
#guard (List.finRange 17).all fun a => (List.range 256).all fun b =>
  (recoverRoot root17 a b).isSome ==
    (List.finRange 17).any fun y => y * y == a && y.val % 2 == b

#guard (List.finRange 19).all fun a => (List.range 256).all fun b =>
  (recoverRoot rootThreeModFour a b).isSome ==
    (List.finRange 19).any fun y => y * y == a && y.val % 2 == b

#guard recoverRoot root17 0 0 == some 0
#guard recoverRoot root17 0 1 == none
#guard recoverRoot (rootThreeModFour (p := 19)) 0 0 == some 0
#guard recoverRoot (rootThreeModFour (p := 19)) 0 1 == none

end VG.Test.EcCompressedRoot
