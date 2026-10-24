module
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
import VerifiedGarbage.Proof.Weierstrass.Unch
/-! # The inverse working bank and virtual modulus -/
@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.Impl.Rsa.X86.InvBatch
 def virtualMod (m : Nat) : Nat := if m=1 then 3 else m
 def initWrites (w : Nat) : List (Nat × Nat) :=
 [(offset w 0,8*(4*w+8)),(offset w 11,4*(4*w+8)),(100,4)]

end VG.Proof.Rsa.X86.InvBatch
