module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Squeeze
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The serialized pair output is the specified ML-KEM noise PRF -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG
open VG.Proof.Sha3.AArch64.Neon

theorem Rate128.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : Rate128 m p A)
    {j : Nat} (hj : j < 128) : m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (outAddr p (j/8)) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [outAddr,BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8 = j by omega] at he
  exact he

theorem output_prf {m input : Mem} {p seed : Addr} {n : Nat} (hn : n < 256)
    (h : Rate128 m p (Spec.Sha3.keccakF (seedState input seed n))) :
    Spec.Sha3.bytesAt m p 128 = Spec.MlKem.prf 2 (Spec.Sha3.bytesAt input seed 32) (BitVec.ofNat 8 n) := by
  apply Proof.MlKem.bytesAt_eq (Proof.MlKem.prf_length 2 _ _)
  intro j hj
  rw [h.byte hj, seedState_eq input seed hn]
  have he := Seed.prf_get (Proof.Sha3.bytesAt_length input seed 32) (BitVec.ofNat 8 n) hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [Proof.MlKem.prf_length]; exact hj), Option.getD_some] at he
  exact he.symm

end VG.Proof.MlKem.AArch64.Noise
