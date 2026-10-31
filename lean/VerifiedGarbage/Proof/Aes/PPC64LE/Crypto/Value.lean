module

public import VerifiedGarbage.Proof.Aes.Vector
public import VerifiedGarbage.Proof.Aes.KeyWords
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Mem

-- separate module: byte-order and round facts are shared by key setup, ECB and CTR.
/-! # POWER8 AES values and byte order -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey invSubBytes invShiftRows invMixColumns)

/-- The POWER register's architectural byte zero is the first AES byte. -/
def aesState (v : BitVec 128) : Spec.Aes.State := VG.Proof.Aes.Vector.st (rev128 v)

def IsKey (v : BitVec 128) (rk : List Byte) : Prop := VG.Proof.Aes.Vector.KeyIs (rev128 v) rk

theorem xor_state {v k : BitVec 128} {rk : List Byte} (hk : IsKey k rk) :
    aesState (v ^^^ k) = addRoundKey (aesState v) rk := by
  simp only [aesState, rev128_xor, VG.Proof.Aes.Vector.eor_st hk]

theorem cipher_state (last : Bool) {v k : BitVec 128} {rk : List Byte} (hk : IsKey k rk) :
    aesState (vcipher false last v k) = addRoundKey
      (if last then shiftRows (subBytes (aesState v)) else mixColumns (shiftRows (subBytes (aesState v)))) rk := by
  cases last <;>
    simp only [aesState, vcipher, Bool.false_eq_true, ite_false, ite_true, rev128_rev128]
  · rw [VG.Proof.Aes.Vector.eor_st hk, VG.Proof.Aes.Vector.aesmc_st, VG.Proof.Aes.Vector.subShift_st]
  · rw [VG.Proof.Aes.Vector.eor_st hk, VG.Proof.Aes.Vector.subShift_st]

theorem invCipher_state (last : Bool) {v k : BitVec 128} {rk : List Byte} (hk : IsKey k rk) :
    aesState (vcipher true last v k) =
      if last then addRoundKey (invSubBytes (invShiftRows (aesState v))) rk
      else invMixColumns (addRoundKey (invSubBytes (invShiftRows (aesState v))) rk) := by
  cases last <;>
    simp only [aesState, vcipher, Bool.false_eq_true, ite_false, ite_true, rev128_rev128]
  · rw [VG.Proof.Aes.Vector.st_aesimc, VG.Proof.Aes.Vector.eor_st hk, VG.Proof.Aes.Vector.st_invSub]
  · rw [VG.Proof.Aes.Vector.eor_st hk, VG.Proof.Aes.Vector.st_invSub]

theorem aesState_inj {v w : BitVec 128} (h : aesState v = aesState w) : v = w := by
  have he : rev128 v = rev128 w := by
    apply VG.Proof.Aes.Vector.ext_vbyte
    intro i hi
    rw [← VG.Proof.Aes.Vector.getD_st _ hi, ← VG.Proof.Aes.Vector.getD_st _ hi]
    exact congrArg (fun x : Spec.Aes.State => x.getD i 0) h
  have hh := congrArg rev128 he
  simpa only [rev128_rev128] using hh

/-- Reverse bytes within each architectural doubleword. -/
def flip (v : BitVec 128) : BitVec 128 := rev128 (swapDwords v)

theorem mask_control {i : Nat} (hi : i < 16) :
    (vbyte Impl.Aes.PPC64LE.Crypto.byteMask i).toNat % 32 = if i < 8 then 7-i else 23-i := by
  have h : ∀ i : Fin 16,
      (vbyte Impl.Aes.PPC64LE.Crypto.byteMask i).toNat % 32 = if i.val < 8 then 7-i.val else 23-i.val := by decide
  exact h ⟨i, hi⟩

theorem perm_flip (v : BitVec 128) :
    permSelf v Impl.Aes.PPC64LE.Crypto.byteMask = flip v := by
  unfold permSelf
  apply VG.PPC64LE.ext_vbyte
  intro i hi
  rw [vbyte_packed _ hi, flip, vbyte_rev128 _ hi, vbyte_swapDwords _ (by omega), mask_control hi]
  rw [ite_eq_left (show (if i < 8 then 7-i else 23-i) < 16 by split <;> omega)]
  exact congrArg (vbyte v) (by split <;> split <;> omega)

theorem flip_load (v : BitVec 128) : flip (swapDwords v) = rev128 v := by
  rw [flip, swapDwords_involutive]

theorem flip_store (v : BitVec 128) : swapDwords (flip v) = rev128 v := by
  rw [flip, ← rev128_swapDwords, swapDwords_involutive]

theorem flip_flip (v : BitVec 128) : flip (flip v) = v := by
  simp only [flip, rev128_swapDwords, rev128_rev128, swapDwords_involutive]

theorem exec_flip (d n : VReg) (s : State)
    (hm : s.vpr Impl.Aes.PPC64LE.Crypto.mask = Impl.Aes.PPC64LE.Crypto.byteMask) :
    exec (.vop (.perm d n n Impl.Aes.PPC64LE.Crypto.mask)) s = some (s.writeV d (flip (s.vpr n))) := by
  simp only [reduceExec, reduceVOpEval, hm, Option.map_some]
  apply congrArg (fun x => some (s.writeV d x))
  exact perm_flip _

theorem stateAt_read16 (m : Mem) (p : Addr) :
    VG.Proof.Aes.Vector.st (m.read p 16) = Spec.Aes.stateAt m p := by
  apply VG.Proof.Aes.Vector.st_ext
  intro i hi
  rw [VG.Proof.Aes.Vector.getD_st _ hi, Spec.Aes.stateAt, VG.Proof.Aes.Vector.getD_ofFn hi]
  simpa only [Mem.readW, BitVec.setWidth_eq] using VG.Proof.Aes.Vector.vbyte_readW m p hi


theorem load_state (m : Mem) (p : Addr) : aesState (rev128 (m.read p 16)) = Spec.Aes.stateAt m p := by
  rw [aesState, rev128_rev128, stateAt_read16]

theorem stateAt_store (m : Mem) (p : Addr) (v : BitVec 128) :
    Spec.Aes.stateAt (m.write p 16 (swapDwords (flip v))) p = aesState v := by
  rw [flip_store, ← stateAt_read16, VG.Proof.VectorCrypto.read_write16]
  rfl

theorem key_read (m : Mem) (p : Addr) {L j : Nat} (hj : 16*j+16 ≤ L) :
    IsKey (rev128 (m.read (p + BitVec.ofNat 64 (16*j)) 16))
      (Spec.Aes.roundKey (Spec.Aes.bytesAt m p L) j) := by
  rw [IsKey, rev128_rev128]
  simpa only [Mem.readW, BitVec.setWidth_eq] using VG.Proof.Aes.Vector.keyIs_readW m p hj


theorem counter_control {i : Nat} (hi : i < 16) :
    (vbyte Impl.Aes.PPC64LE.Crypto.counterControl i).toNat % 32 = if i < 12 then i else i+8 := by
  have h : ∀ i : Fin 16,
      (vbyte Impl.Aes.PPC64LE.Crypto.counterControl i).toNat % 32 = if i.val < 12 then i.val else i.val+8 := by decide
  exact h ⟨i, hi⟩

theorem counter_value (base : BitVec 128) (word undef : BitVec 64) :
    (ofVBytes fun i =>
      let j := (vbyte Impl.Aes.PPC64LE.Crypto.counterControl i).toNat % 32
      if j < 16 then vbyte base j else vbyte (word ++ undef) (j-16)) =
      base.extractLsb' 32 96 ++ word.extractLsb' 0 32 := by
  apply VG.PPC64LE.ext_vbyte
  intro i hi
  rw [vbyte_packed _ hi, counter_control hi]
  by_cases h : i < 12
  · rw [ite_eq_left h, ite_eq_left hi]
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      hr, decide_true, Bool.true_and]
    rw [ite_eq_right (show ¬8*(15-i)+r < 32 by omega)]
    simp only [show 8*(15-i)+r-32 < 96 by omega, decide_true, Bool.true_and]
    exact congrArg base.getLsbD (by omega)
  · rw [ite_eq_right h, ite_eq_right (show ¬i+8 < 16 by omega)]
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      hr, decide_true, Bool.true_and]
    rw [ite_eq_right (show ¬8*(15-(i+8-16))+r < 64 by omega),
      ite_eq_left (show 8*(15-i)+r < 32 by omega)]
    simp only [show 8*(15-i)+r < 32 by omega, decide_true, Bool.true_and, Nat.zero_add]
    exact congrArg word.getLsbD (by omega)


theorem sbox_word (word undef : BitVec 64) :
    (((ofVBytes fun i => VG.VectorCrypto.aesSbox (vbyte (word ++ undef) i)).extractLsb' 64 64).setWidth 32) =
      VG.Proof.Aes.KeyWords.sub32 (word.setWidth 32) := by
  apply VG.Proof.Aes.KeyWords.ext32
  intro q hq
  rw [extract_high_word_byte _ hq, vbyte_packed _ (by omega),
    ← extract_high_word_byte (word ++ undef) hq, BitVec.extractLsb'_append_eq_left,
    VG.Proof.Aes.KeyWords.sub32_byte _ hq]

/-- The architectural bytes are GCM's big-endian block bytes. -/
theorem aesState_byte (v : BitVec 128) {i : Nat} (hi : i < 16) :
    (aesState v).getD i 0 = (Spec.Gcm.toBytes v).getD i 0 := by
  rw [aesState, VG.Proof.Aes.Vector.getD_st _ hi, VG.Proof.Aes.toBytes_getD _ hi]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.VectorCrypto.vbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [getLsbD_rev128 _ (by omega)]
  exact congrArg v.getLsbD (by omega)

theorem aesState_blockAt (m : Mem) (p : Addr) :
    aesState (Spec.Gcm.blockAt m p) = Spec.Aes.stateAt m p := by
  apply VG.Proof.Aes.Vector.st_ext
  intro i hi
  rw [aesState_byte _ hi, VG.Proof.Aes.toBytes_blockAt _ _ hi,
    Spec.Aes.stateAt, VG.Proof.Aes.Vector.getD_ofFn hi]

theorem read_blockAt (m : Mem) (p : Addr) :
    rev128 (m.read p 16) = Spec.Gcm.blockAt m p :=
  aesState_inj ((load_state m p).trans (aesState_blockAt m p).symm)

theorem aesState_aesWith (nr : Nat) (w : List Byte) (v : BitVec 128) :
    aesState (Spec.Gcm.aesWith nr w v) = Spec.Aes.cipher nr w (aesState v) := by
  have hv : (Vector.ofFn fun i : Fin 16 => (Spec.Gcm.toBytes v).getD i 0) = aesState v := by
    apply VG.Proof.Aes.Vector.st_ext
    intro i hi
    rw [VG.Proof.Aes.Vector.getD_ofFn hi, aesState_byte _ hi]
  apply VG.Proof.Aes.Vector.st_ext
  intro i hi
  rw [aesState_byte _ hi, Spec.Gcm.aesWith, hv,
    VG.Proof.Aes.toBytes_ofBytes (by simp) hi]
  simp [Vector.getD, List.getD_eq_getElem?_getD, hi]

theorem rev32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (rev32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  rw [show rev32 = byteRev32 from rfl, byteRev32_getLsbD _ (by omega),
    show (8 * k + j) / 8 = k by omega, show (8 * k + j) % 8 = j by omega]

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega
  rw [e, rev32_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    VG.Proof.Aes.blockAt_bit _ _ (by omega) (by omega)]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega]

end VG.Proof.Aes.PPC64LE.Crypto
