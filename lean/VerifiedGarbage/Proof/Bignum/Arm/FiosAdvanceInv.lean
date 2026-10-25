module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Proof.Bignum.Arm.FiosPair
import VerifiedGarbage.Proof.Bignum.Arm.FiosAdvance
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Advance public pointers after a proved quotient-prefix update. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem advance_inv {s0 s u : State} {x q base : BitVec 32} {size acc b mod n i k : Nat}
    (ctx : Ctx s0 base size acc b mod n) (inv : Inv s0 x q base acc b mod n i s)
    (hk : k=1 ∨ k=2) (bound : i+k+1≤n) (rs : Rest pairClobbers s u)
    (outside : Outside (State.addr base) acc (4*(i+k)) s0.mem u.mem)
    (value : 2^32*val32 u.mem (State.addr base) acc (i+k)+
      2^(32*((i+k)+1))*((u.gpr .r7).toNat+(u.gpr .r8).toNat)=
      val32 s0.mem (State.addr base) acc ((i+k)+1)+
      x.toNat*val32 s0.mem (State.addr base) b ((i+k)+1)+
      q.toNat*val32 s0.mem (State.addr base) mod ((i+k)+1)) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4*k))),
      .dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (4*k))),
      .dp .add .r4 .r4 (.imm (BitVec.ofNat 32 (4*k))),
      .subs .lr .lr (.imm (BitVec.ofNat 32 k))]) u fun t =>
      Inv s0 x q base acc b mod n (i+k) t ∧ t.z=decide (i+k+1=n) := by
  refine WP.mono (advance_ok u k hk) ?_
  rintro t ⟨p0,p12,p4,count,zero,mem,rt⟩
  have small : n<2^32 := by have := ctx.workspace.nowrap;have := ctx.accFits;omega
  refine ⟨⟨bound,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [p0,rs.gpr .r0 (by decide),inv.outPtr,Offset.add_add]
    congr 2
    omega
  · rw [p12,rs.gpr .r12 (by decide),inv.bPtr,Offset.add_add]
    congr 2
    omega
  · rw [p4,rs.gpr .r4 (by decide),inv.mPtr,Offset.add_add]
    congr 2
    omega
  · rw [count,rs.gpr .lr (by decide),inv.count,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    congr 1
    omega
  · rw [rt.gpr .r1 (by decide),rs.gpr .r1 (by decide),inv.scalar]
  · rw [rt.gpr .r2 (by decide),rs.gpr .r2 (by decide),inv.quotient]
  · rw [mem];exact outside
  · rw [mem,rt.gpr .r7 (by decide),rt.gpr .r8 (by decide)];exact value
  · exact inv.rest.trans ((rs.mono (by decide)).trans
      (rt.mono (by decide)))
  · rw [zero,rs.gpr .lr (by decide),inv.count,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega),ofNat_beq_zero (by omega)]
    simp only [show n-(i+1)-k=0 ↔ i+k+1=n by omega]

end VG.Proof.Bignum.Arm.Fios
