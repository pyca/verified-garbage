module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! The product carry is one limb ahead of the stored quotient prefix. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure Inv (s0 : State) (x q base : BitVec 32) (acc b mod n start i : Nat)
    (pending : Reg) (s : State) : Prop where
  index : i+2≤n
  progress : start≤i
  outPtr : s.gpr .r0=base+BitVec.ofNat 32 (acc+4*start)
  bPtr : s.gpr .r12=base+BitVec.ofNat 32 (b+4*(start+1))
  mPtr : s.gpr .r4=base+BitVec.ofNat 32 (mod+4*(start+1))
  count : s.gpr .lr=BitVec.ofNat 32 (n-(start+1))
  scalar : s.gpr .r1=x
  quotient : s.gpr .r2=q
  outside : Outside (State.addr base) acc (4*i) s0.mem s.mem
  value : 2^32*val32 s.mem (State.addr base) acc i+
      2^(32*(i+1))*((s.gpr pending).toNat+(s.gpr .r8).toNat)+
      2^(32*(i+2))*(s.gpr .r7).toNat=
    val32 s0.mem (State.addr base) acc (i+2)+
      x.toNat*val32 s0.mem (State.addr base) b (i+2)+
      q.toNat*val32 s0.mem (State.addr base) mod (i+1)
  rest : Rest roundClobbers s0 s

end VG.Proof.Bignum.Arm.FiosPipelined
