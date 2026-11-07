module
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Xor (st dp L bp stR dR bR)

theorem read_write_self (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.write p 16 v).read p 16 = v := by
  have h := Mem.readW_writeW_self m p 16 v (by decide)
  simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using h

end VG.Proof.ChaCha20.AArch64.Rows6
