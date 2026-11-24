module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.X86.Ssse3
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# CAST5 with its S-box look-ups by `pshufb` on x86 (32-bit): the table and the code as literals

The table of the planes of S1 to S8 and the constants
(`Impl.Cast5.X86.Ssse3.table`), the look-ups' function and the functions
over it as literals, which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build again. Each S-box's
planes are a literal of their own (`planes0` to `planes7`), which the
table's is put together from: the kernel evaluates an S-box's 1024 entries'
bytes in one declaration, not the eight S-boxes' in one.
-/

@[expose] public section

namespace VG

materialize_value planes0 := Impl.Cast5.X86.Ssse3.planesOf 0
materialize_value planes1 := Impl.Cast5.X86.Ssse3.planesOf 1
materialize_value planes2 := Impl.Cast5.X86.Ssse3.planesOf 2
materialize_value planes3 := Impl.Cast5.X86.Ssse3.planesOf 3
materialize_value planes4 := Impl.Cast5.X86.Ssse3.planesOf 4
materialize_value planes5 := Impl.Cast5.X86.Ssse3.planesOf 5
materialize_value planes6 := Impl.Cast5.X86.Ssse3.planesOf 6
materialize_value planes7 := Impl.Cast5.X86.Ssse3.planesOf 7
materialize_value Impl.Cast5.X86.Ssse3.table
materialize_code Impl.Cast5.X86.Ssse3.lookup
materialize_code Impl.Cast5.X86.Ssse3.cbcEncryptChained
materialize_code Impl.Cast5.X86.Ssse3.ofb
materialize_code Impl.Cast5.X86.Ssse3.cfbEncrypt
materialize_code Impl.Cast5.X86.Ssse3.cfbEncryptFinal
materialize_code Impl.Cast5.X86.Ssse3.cfbDecryptFinal
materialize_code Impl.Cast5.X86.Ssse3.ofbFinal

end VG
