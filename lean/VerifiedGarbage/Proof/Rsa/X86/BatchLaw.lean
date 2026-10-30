module
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Writes
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
/-! # Compositional arithmetic laws for the RSA batch kernels

Callers use these laws without importing the arithmetic proof machinery.
The registration supplies the closed, kernel-checked instance.
-/
@[expose] public section
namespace VG.Proof.Rsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Rsa.X86.Keys
open VG.Proof.Weierstrass.X86.Inv (wordClob)
class BatchLaw : Prop where
  gcd_ok {L : VG.Impl.Rsa.X86.KeyRt.Lay} {s : State} {B : Addr} {Z len N : Nat}
      (h : VG.Proof.Rsa.X86.KeyRt.RtWs L s B Z len N) (room : 16 ≤ N) (hodd : InvBatchRt.nw len % 2 = 1)
      (h3 : 3 ≤ InvBatchRt.nw len) (hmax : InvBatchRt.nw len ≤ 1024) {m x : Nat}
      (hm : val32 s.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 4)) (InvBatchRt.nw len - 1) = m)
      (hx : val32 s.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 0)) (InvBatchRt.nw len - 1) = x)
      (odd : m % 2 = 1) :
      WP isa (VG.Impl.Rsa.X86.GcdBatchRt.body L) s fun z =>
        InvBatchRt.Bx L z B Z len N ∧
        val32 z.mem B (InvBatchRt.rv (KeyRt.kw len) VG.Impl.Rsa.X86.GcdBatchRt.res) (InvBatchRt.nw len - 1) =
          Nat.gcd m x ∧
        val32 z.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 5)) (InvBatchRt.nw len - 1) = 0 ∧
        Keeps wordClob s z ∧ Unch B (GcdBatchRt.gcdWrites len) s.mem z.mem
  inv_ok {L : VG.Impl.Rsa.X86.KeyRt.Lay} {s : State} {B : Addr} {Z len N : Nat}
      (h : VG.Proof.Rsa.X86.KeyRt.RtWs L s B Z len N) (room : 16 ≤ N) (hn2 : 2 ≤ InvBatchRt.nw len)
      (he : InvBatchRt.nw len % 2 = 0) {m x : Nat}
      (hm : val32 s.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 8)) (InvBatchRt.nw len) = m)
      (hx : val32 s.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 0)) (InvBatchRt.nw len) = x)
      (odd : m % 2 = 1) :
      WP isa (VG.Impl.Rsa.X86.InvBatchRt.body L) s fun z =>
        InvBatchRt.Bx L z B Z len N ∧
        val32 z.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 1)) (KeyRt.kw len) =
          Nat.gcd (InvBatchRt.virtualMod m) x ∧
        (InvBatchRt.virtualMod m : Int) ∣
          (val32 z.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 3)) (KeyRt.kw len) : Int) * x -
            (Nat.gcd (InvBatchRt.virtualMod m) x : Int) ∧
        val32 z.mem B (InvBatchRt.rv (KeyRt.kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 3)) (KeyRt.kw len) <
          InvBatchRt.virtualMod m ∧
        Keeps wordClob s z ∧ Unch B (InvBatchRt.bodyWrites len) s.mem z.mem
end VG.Proof.Rsa.X86
