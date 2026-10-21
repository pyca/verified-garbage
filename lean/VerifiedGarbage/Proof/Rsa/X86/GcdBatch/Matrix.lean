module
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.Words
/-! # The transition matrix stored in the RSA workspace -/
@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Rsa.X86.GcdBatch VG.Proof.Mont
structure MatrixAt (n : Nat) (base : Addr) (T : Divstep.MSt) (s : State) : Prop where
  d : s.mem.readW (VG.Proof.Mont.off base (offset n 3)) 32 = BitVec.ofInt 32 T.d
  u : s.mem.readW (VG.Proof.Mont.off base (offset n 3+12)) 32 = BitVec.ofInt 32 T.u
  v : s.mem.readW (VG.Proof.Mont.off base (offset n 3+16)) 32 = BitVec.ofInt 32 T.v
  q : s.mem.readW (VG.Proof.Mont.off base (offset n 3+20)) 32 = BitVec.ofInt 32 T.q
  r : s.mem.readW (VG.Proof.Mont.off base (offset n 3+24)) 32 = BitVec.ofInt 32 T.r

end VG.Proof.Rsa.X86.GcdBatch
