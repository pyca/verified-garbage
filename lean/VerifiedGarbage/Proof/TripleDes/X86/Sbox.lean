module

public import VerifiedGarbage.Proof.TripleDes.X86.Linear
public import VerifiedGarbage.Impl.TripleDes.X86.Permutation
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86.Linear
meta import VerifiedGarbage.Impl.TripleDes.X86.Permutation
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Triple DES key expansion on x86 (32-bit): the permutations' code and the working space

The code of the key schedule's two permutations as literals
(`materialize_code`), which their checks read (`Bytes.lean`), and the
working space of key expansion and of CMAC's block as the straight-line
checker sees it (`sboxCfg`: 128 words at `ebp`).
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86

materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.X86

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight

def sboxCfg : Cfg := { base := .ebp, slots := 128, ext := .ebp, exts := 0 }

end VG.Proof.TripleDes.X86
