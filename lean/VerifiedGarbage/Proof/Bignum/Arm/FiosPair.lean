module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios
import VerifiedGarbage.Proof.Bignum.Arm.FiosFixedPair
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! Two product limbs are issued before their independent cancellation chain. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_str)

abbrev pairClobbers : List Reg := [.r3,.r5,.r6,.r7,.r8,.r10]

/-- The original arrays can overlap one another, but not the quotient stores. -/
theorem pair_ok (s : State) {base : BitVec 32} {size a m d : Nat}
    (ws : Workspace s base size) (fa : a+8≤size) (fm : m+8≤size) (fd : d+12≤size)
    (sep : d+8≤m ∨ m+8≤d)
    (pa : s.gpr .r12=base+BitVec.ofNat 32 a)
    (pm : s.gpr .r4=base+BitVec.ofNat 32 m)
    (pd : s.gpr .r0=base+BitVec.ofNat 32 d) :
    WP isa VG.Impl.Bignum.Arm.Fios.pairStep s fun t =>
      (t.gpr .r6).toNat+2^32*(t.gpr .r10).toNat+
        2^64*((t.gpr .r7).toNat+(t.gpr .r8).toNat)=
        (s.gpr .r1).toNat*(w32 s.mem (State.addr base) a+2^32*w32 s.mem (State.addr base) (a+4))+
        (s.gpr .r2).toNat*(w32 s.mem (State.addr base) m+2^32*w32 s.mem (State.addr base) (m+4))+
        (w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8))+
        (s.gpr .r7).toNat+(s.gpr .r8).toNat ∧
      t.mem=(s.mem.writeW (off (State.addr base) d) (t.gpr .r6)).writeW
        (off (State.addr base) (d+4)) (t.gpr .r10) ∧
      Rest pairClobbers s t := by
  simpa only [Nat.add_zero,VG.Impl.Bignum.Arm.FiosFixed.pairAt,
    VG.Impl.Bignum.Arm.Fios.pairStep,VG.Impl.Bignum.Arm.Fios.pairLoadsA0,
    VG.Impl.Bignum.Arm.Fios.pairLoadsA1,VG.Impl.Bignum.Arm.Fios.store,
    pairClobbers,VG.Proof.Bignum.Arm.FiosFixed.pairClobbers] using
    (VG.Proof.Bignum.Arm.FiosFixed.pairAt_ok (k:=0) s (by decide) ws fa fm fd sep pa pm pd)

end VG.Proof.Bignum.Arm.Fios
