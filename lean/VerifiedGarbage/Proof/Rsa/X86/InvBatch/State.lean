module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Mont.Words32

/-! # The encoded state carried between batches of RSA inversion -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont

 structure StateAt (w n : Nat) (base : Addr) (p iv : Nat) (st : VG.Proof.Divstep.W32.IState) (s : State) : Prop where
  d : s.mem.readW (off base (offset w 3)) 32=BitVec.ofInt 32 st.d
  modulus : val32 s.mem base (offset w 2) n=p
  inverse : w32 s.mem base (offset w 3+28)=iv
  f : (val32 s.mem base (offset w 4) (n+1) : Int)%2^(32*(n+1))=st.f%2^(32*(n+1))
  g : (val32 s.mem base (offset w 5) (n+1) : Int)%2^(32*(n+1))=st.g%2^(32*(n+1))
  a : (val32 s.mem base (offset w 6) n : Int)=st.a
  b : (val32 s.mem base (offset w 7) n : Int)=st.b
  aTop : w32 s.mem base (offset w 6+4*n)=0
  bTop : w32 s.mem base (offset w 7+4*n)=0

end VG.Proof.Rsa.X86.InvBatch
