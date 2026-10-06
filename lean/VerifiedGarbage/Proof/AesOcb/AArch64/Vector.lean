import VerifiedGarbage.Proof.AesOcb.AArch64.Batch

/-! Vector block transfers and XOR, against the existing OCB block specification. -/
set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem)

theorem vBlock_xor (x y : BitVec 128) : vBlock (x ^^^ y) = vBlock x ^^^ vBlock y := by
  unfold vBlock
  rw [← Proof.Ocb.ofBytes_xor (by simp) (by simp)]
  congr 1
  simp only [Spec.Ocb.xor, List.zipWith_map, List.zipWith_self]
  apply List.map_congr_left
  intro j hj
  exact BitVec.extractLsb'_xor ..

theorem blockAtMem_storeV (m : Mem) (p : Addr) (x : BitVec 128) :
    blockAtMem (m.write p 16 x) p = vBlock x := by
  rw [← vBlock_read]
  change vBlock ((m.writeW p x).readW p 128) = _
  rw [Mem.readW_writeW_self m p 16 x (by decide)]

end VG.Proof.AesOcb.AArch64
