module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.X86.CtPad
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS on x86: hashing a message of secret length

`ctW`: the regions hashing a message of secret length writes.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- What hashing a message of secret length writes. -/
abbrev ctW (L : Lay) (scr : BitVec 32) (T : Nat) : List Region :=
  [sR scr oSt (h.N + h.B), L.LOW, sR scr oLen h.B, slotR L sLb, sR scr oY T, sR scr oCW h.H.so,
    sR scr oSel h.N, slotR L sBi, sR scr oDig h.N]

end VG.Proof.RsaPss.X86
