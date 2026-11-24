module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TagFinish
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Mem

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64 VG.Proof.Gcm.AArch64.Pmull
open VG.Proof.Aes.Vector (st getD_st st_ext getD_ofFn vbyte_readW vbyte_xor)
open VG.Spec.Gcm (toBytes aesWith blockAt)

/-- Read the hash and tag mask in byte order from the tag store. -/
theorem tagBytes (m : Mem) (dest iv : Addr) (z mask : BitVec 128) (nr : Nat) (keys : List Byte)
    (h : st mask = Spec.Aes.cipher nr keys (st (m.readW iv 128))) :
    Spec.Aes.bytesAt (m.write dest 16 (VRevOp.eval .rev64b (ext8 z z) ^^^ mask)) dest 16 =
      toBytes (z ^^^ aesWith nr keys (blockAt m iv)) := by
  let word := VRevOp.eval .rev64b (ext8 z z)
  have stIv : (Vector.ofFn fun i : Fin 16 => (toBytes (blockAt m iv)).getD i 0) = st (m.readW iv 128) := by
    apply st_ext; intro i hi
    rw [getD_ofFn hi,getD_st _ hi,vbyte_readW _ _ hi,Proof.Aes.toBytes_blockAt _ _ hi]
  have readByte (w : BitVec 128) {i : Nat} (hi : i < 16) :
      (m.write dest 16 w) (dest + BitVec.ofNat 64 i) = VG.VectorCrypto.vbyte w i := by
    rw [← vbyte_readW (m.write dest 16 w) dest hi]
    exact congrArg (VG.VectorCrypto.vbyte · i) (read_write16 m dest w)
  have hash : blockAt (m.write dest 16 word) dest = z := by
    exact (blockAt_store m dest (ext8 z z)).trans (ext8_ext8 z)
  rw [Proof.Cmac.bytesAt_blockAt]
  apply congrArg toBytes
  apply Proof.Aes.block_ext
  intro i hi
  have hb := Proof.Aes.toBytes_blockAt (m.write dest 16 word) dest hi
  rw [hash,readByte _ hi] at hb
  rw [Proof.Aes.toBytes_blockAt _ _ hi,readByte _ hi,vbyte_xor,← hb,Proof.Aes.toBytes_xor _ _ hi]
  apply congrArg ((toBytes z).getD i 0 ^^^ ·)
  rw [← getD_st _ hi,h,aesWith,stIv,Proof.Aes.toBytes_ofBytes (by simp) hi,Proof.Aes.getD_eq _ hi,
    List.getD_eq_getElem?_getD,Vector.getElem?_toList,Vector.getElem?_eq_getElem hi,Option.getD_some]

end VG.Proof.AesGcm.AArch64.Contiguous.Tag
