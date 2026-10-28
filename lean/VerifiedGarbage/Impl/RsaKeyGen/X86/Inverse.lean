module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Mont.X86.Compact

/-! # `vg_rsa_keygen_inverse`: the key's binary extended GCD, emitted once

`KeyRt.inverse` on the caller's working space, inside the frame of the four
registers cdecl preserves, with its arguments `ws`, `ws_len` and `len` at
`esp + 20`, `+ 24` and `+ 28` (`Lay` indices 4, 5 and 6).
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Impl.Mont.X86

/-- The arguments after the frame: the working space at 4 and the length at 6. -/
def lay : VG.Impl.Rsa.X86.KeyRt.Lay := { len := 6, ws := 4 }

def code : Prog isa := .frame (.push [.ebx, .ebp, .esi, .edi])
  (.seq (.block (VG.Impl.Rsa.X86.KeyRt.restoreEdi lay))
    (.seq (VG.Impl.Rsa.X86.KeyRt.inverse lay) (.block Compact.restoreRegs))) (.pop .ebx 4)

end VG.Impl.RsaKeyGen.X86.Inverse
