module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Output
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Bswap

-- separate module: CTR's final memory values are related to the GCM contract here.
/-! # POWER8 AES CTR results -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory

theorem ctr_processed {m₀ m : Mem} {D : Addr} {n nr : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : Processed m₀ m D n n (outputState false true nr w icb m₀ D)) :
    Spec.Gcm.blocksAt m D n = Spec.Gcm.ctr32 (Spec.Gcm.aesWith nr w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.blocksAt Spec.Gcm.ctr32 Spec.Gcm.keystream
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hin : i < n := by simpa only [List.length_map, List.length_range] using hi
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map, List.length_range]
  apply aesState_inj
  rw [aesState_blockAt, h.stateAt hin (Nat.le_refl _)]
  simp only [outputState, ite_true, BitVec.xor_comm]

theorem counter_after {m m' : Mem} {C : Addr} {n : Nat} {word : BitVec 32}
    (hw : word = (Spec.Gcm.blockAt m C).extractLsb' 0 32 + BitVec.ofNat 32 n)
    (h : ∀ k < 16, m' (C + BitVec.ofNat 64 k) = if k < 12 then m (C + BitVec.ofNat 64 k)
      else (rev32 word).extractLsb' (8*(k-12)) 8) :
    Spec.Gcm.blockAt m' C = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m C) := by
  apply VG.Proof.Aes.block_ext
  intro k hk
  rw [VG.Proof.Aes.toBytes_blockAt _ _ hk, h k hk, VG.Proof.Aes.ctrBlock_byte _ _ hk]
  split
  · rw [VG.Proof.Aes.toBytes_blockAt _ _ hk]
  · rw [← hw]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev32_bit _ (by omega) hj]
    simp only [hj, decide_true, Bool.true_and]
    exact congrArg word.getLsbD (by omega)

end VG.Proof.Aes.PPC64LE.Crypto
