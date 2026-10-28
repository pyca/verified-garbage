module
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.FrameBase
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import Aesop.BuiltinRules
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
/-! # Compositional arithmetic laws for the fixed RSA batch kernels

Callers use these laws without importing the arithmetic proof machinery.
The registration supplies the closed, kernel-checked instance.
-/
@[expose] public section
namespace VG.Proof.Rsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Rsa.X86.Keys
open VG.Proof.Weierstrass.X86.Inv (wordClob)
class BatchLaw : Prop where
  gcd_ok {s : State} {base : Addr} {size n : Nat}
      (hs : Scr s base size) (hn : 16 ≤ n) (hnMax : n ≤ 1024) (hz : VG.Impl.Rsa.X86.GcdBatch.offset n 15 ≤ size)
      (hm : val32 s.mem base (VG.Impl.Rsa.X86.GcdBatch.offset n 8) n % 2=1) :
      WP isa (VG.Impl.Rsa.X86.GcdBatch.body n) s fun z =>
        val32 z.mem base (VG.Impl.Rsa.X86.GcdBatch.offset n 1) n =
          Nat.gcd (val32 s.mem base (VG.Impl.Rsa.X86.GcdBatch.offset n 8) n) (val32 s.mem base (VG.Impl.Rsa.X86.GcdBatch.offset n 0) n) ∧
        Keeps wordClob s z ∧ Keep base n invArrs invSlots s.mem z.mem
end VG.Proof.Rsa.X86
