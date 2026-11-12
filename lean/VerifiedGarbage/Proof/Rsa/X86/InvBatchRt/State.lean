module

public import VerifiedGarbage.Proof.Divstep.Alg32Def
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-! # The state carried between batches at a run-time width

`GcdBatch.MatrixAt` with the divstep window at the header's `win` rather than in array 3.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass

/-- A batch's transition matrix in the window. -/
structure MatrixAt (B : Addr) (T : Divstep.MSt) (s : State) : Prop where
  d : s.mem.readW (off B win) 32 = BitVec.ofInt 32 T.d
  u : s.mem.readW (off B (win + 12)) 32 = BitVec.ofInt 32 T.u
  v : s.mem.readW (off B (win + 16)) 32 = BitVec.ofInt 32 T.v
  q : s.mem.readW (off B (win + 20)) 32 = BitVec.ofInt 32 T.q
  r : s.mem.readW (off B (win + 24)) 32 = BitVec.ofInt 32 T.r

variable {L : Lay} {Z N : Nat}

end VG.Proof.Rsa.X86.InvBatchRt
