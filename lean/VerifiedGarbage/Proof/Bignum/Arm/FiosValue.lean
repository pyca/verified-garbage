module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Extend the quotient prefix using the two independent carry chains. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont

/-- The prefix algebra is independent of whether one or two limbs are scanned. -/
theorem prefix_extend {mem0 mem mem' : Mem} {base : Addr} {acc b mod i k x q oldCarry newCarry low : Nat}
    (prior : 2^32*val32 mem base acc i+2^(32*(i+1))*oldCarry=
      val32 mem0 base acc (i+1)+x*val32 mem0 base b (i+1)+q*val32 mem0 base mod (i+1))
    (step : low+2^(32*k)*newCarry=
      val32 mem0 base (acc+4*(i+1)) k+x*val32 mem0 base (b+4*(i+1)) k+
      q*val32 mem0 base (mod+4*(i+1)) k+oldCarry)
    (stored : val32 mem' base acc (i+k)=val32 mem base acc i+2^(32*i)*low) :
    2^32*val32 mem' base acc (i+k)+2^(32*((i+k)+1))*newCarry=
      val32 mem0 base acc ((i+k)+1)+x*val32 mem0 base b ((i+k)+1)+
      q*val32 mem0 base mod ((i+k)+1) := by
  have power : 2^(32*((i+k)+1))=2^(32*(i+1))*2^(32*k) := by
    rw [←Nat.pow_add]
    congr 1
    omega
  rw [stored,power,show i+k+1=(i+1)+k by omega,
    val32_append mem0 base acc (i+1) k,val32_append mem0 base b (i+1) k,
    val32_append mem0 base mod (i+1) k]
  have scaled := congrArg (fun z => 2^(32*(i+1))*z) step
  rw [pow32_succ] at prior scaled ⊢
  generalize 2^(32*i)=P at *
  generalize 2^(32*k)=Q at *
  grind

end VG.Proof.Bignum.Arm.Fios
