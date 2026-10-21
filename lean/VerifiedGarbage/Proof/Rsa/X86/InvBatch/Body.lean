module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
/-! # The batch kernel's compositional arithmetic law -/
@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Rsa.X86.Keys
open VG.Proof.Weierstrass.X86.Inv (wordClob)
variable [law : VG.Proof.Rsa.X86.BatchLaw]
include law
theorem body_ok {s : State} {base : Addr} {size w n m x : Nat}
    (hs : Scr s base size) (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (hm : val32 s.mem base (offset w 8) n=m) (hx : val32 s.mem base (offset w 0) n=x) (odd : m%2=1) :
    WP isa (body w n) s fun z =>
      val32 z.mem base (offset w 1) w=Nat.gcd (virtualMod m) x ∧
      (virtualMod m : Int)∣(val32 z.mem base (offset w 3) w : Int)*x-(Nat.gcd (virtualMod m) x : Int) ∧
      val32 z.mem base (offset w 3) w<virtualMod m ∧
      Keeps wordClob s z ∧ Unch base (initWrites w) s.mem z.mem := VG.Proof.Rsa.X86.BatchLaw.inv_ok hs hn nl hw he hz hm hx odd
end VG.Proof.Rsa.X86.InvBatch
