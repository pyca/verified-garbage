module

public import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing, one compression

`compW`: the regions a compression writes: the hash value at `oSt`, the
scratch space at `oCW` and the frame below `esp`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Pbkdf2.Stream.X86 (After stk)
open VG.Proof.Pbkdf2.Md.X86 (CmpArgs cmp_ok cmp_rel)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The regions a compression writes. -/
abbrev compW (L : Lay) (scr : BitVec 32) : List Region := [sR scr oSt h.N, sR scr oCW h.H.so, L.LOW]

end VG.Proof.RsaPss.X86
