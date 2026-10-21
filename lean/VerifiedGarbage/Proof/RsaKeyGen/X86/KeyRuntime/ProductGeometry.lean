module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductLayout
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Framework.Omega

/-! # Geometry and public cursors of the shared native product -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.Proof.Mont

structure ProductGeometry (Z left right out a b : Nat) : Prop extends
    VG.Proof.RsaKeyGen.X86.Product.Layout Z left right out a b 128 where
  a_header : 156 ≤ a
  b_header : 156 ≤ b
  out_header : 156 ≤ out

def productRanges (left right out : Nat) : List (Nat × Nat) :=
  [(128, 28), (out, 4 * (left + right + 2))]


end VG.Proof.RsaKeyGen.X86.KeyRuntime
