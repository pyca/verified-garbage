module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Chunk

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20.AArch64.Xor (st dp L bp stR dR bR)

theorem read_saved (m : Mem) (p : Addr) (a b c : BitVec 64) (j : Fin 3) :
    (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 (256 + 8 * j)) 64 =
        [a,b,c].getD j a := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Fin.ext_iff]; omega
  rcases hj with rfl | rfl | rfl
  · change (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 256) 64 = a
    rw [Mem.readW_writeW_sep (Offset.sep p (d := 256) (n := 8) (e := 272) (k := 8)
      (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (d := 256) (n := 8) (e := 264) (k := 8)
        (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]
  · change (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 264) 64 = b
    rw [Mem.readW_writeW_sep (Offset.sep p (d := 264) (n := 8) (e := 272) (k := 8)
      (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.ChaCha20.AArch64.Mixed5
