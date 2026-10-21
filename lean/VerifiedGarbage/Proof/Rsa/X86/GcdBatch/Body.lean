module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
/-! # The batch kernel's compositional arithmetic law -/
@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Rsa.X86.Keys
open VG.Proof.Weierstrass.X86.Inv (wordClob)
variable [law : VG.Proof.Rsa.X86.BatchLaw]
include law
theorem body_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hn : 16 ≤ n) (hnMax : n ≤ 1024) (hz : offset n 15 ≤ size)
    (hm : val32 s.mem base (offset n 8) n % 2=1) :
    WP isa (body n) s fun z =>
      val32 z.mem base (offset n 1) n =
        Nat.gcd (val32 s.mem base (offset n 8) n) (val32 s.mem base (offset n 0) n) ∧
      Keeps wordClob s z ∧ Keep base n invArrs invSlots s.mem z.mem := VG.Proof.Rsa.X86.BatchLaw.gcd_ok hs hn hnMax hz hm
end VG.Proof.Rsa.X86.GcdBatch
