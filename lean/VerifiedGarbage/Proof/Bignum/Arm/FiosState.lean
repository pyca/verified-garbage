module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! The integrated row retains two carries while storing its quotient prefix. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure Ctx (s : State) (base : BitVec 32) (size acc b mod n : Nat) : Prop where
  workspace : Workspace s base size
  accFits : acc+4*(n+2)≤size
  bFits : b+4*n≤size
  mFits : mod+4*n≤size
  accB : acc+4*(n+2)≤b ∨ b+4*n≤acc
  accM : acc+4*(n+2)≤mod ∨ mod+4*n≤acc

structure Inv (s0 : State) (x q base : BitVec 32) (acc b mod n i : Nat) (s : State) : Prop where
  index : i+1≤n
  outPtr : s.gpr .r0=base+BitVec.ofNat 32 (acc+4*i)
  bPtr : s.gpr .r12=base+BitVec.ofNat 32 (b+4*(i+1))
  mPtr : s.gpr .r4=base+BitVec.ofNat 32 (mod+4*(i+1))
  count : s.gpr .lr=BitVec.ofNat 32 (n-(i+1))
  scalar : s.gpr .r1=x
  quotient : s.gpr .r2=q
  outside : Outside (State.addr base) acc (4*i) s0.mem s.mem
  value : 2^32*val32 s.mem (State.addr base) acc i+
      2^(32*(i+1))*((s.gpr .r7).toNat+(s.gpr .r8).toNat)=
    val32 s0.mem (State.addr base) acc (i+1)+
      x.toNat*val32 s0.mem (State.addr base) b (i+1)+
      q.toNat*val32 s0.mem (State.addr base) mod (i+1)
  rest : Rest roundClobbers s0 s

end VG.Proof.Bignum.Arm.Fios
