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
  rw [vbyte_packed _ hi, flip, vbyte_rev128 _ hi, vbyte_swapDwords _ (by omega_using []), mask_control hi]
  rw [ite_eq_left (show (if i < 8 then 7-i else 23-i) < 16 by split <;> omega_arith)]
  exact congrArg (vbyte v) (by split <;> split <;> omega_arith)

theorem flip_load (v : BitVec 128) : flip (swapDwords v) = rev128 v := by
  rw [flip, swapDwords_involutive]

theorem flip_store (v : BitVec 128) : swapDwords (flip v) = rev128 v := by
  rw [flip, ← rev128_swapDwords, swapDwords_involutive]

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

theorem key_read (m : Mem) (p : Addr) {L j : Nat} (hj : 16*j+16 ≤ L) :
    IsKey (rev128 (m.read (p + BitVec.ofNat 64 (16*j)) 16))
      (Spec.Aes.roundKey (Spec.Aes.bytesAt m p L) j) := by
  rw [IsKey, rev128_rev128]
  simpa only [Mem.readW, BitVec.setWidth_eq] using VG.Proof.Aes.Vector.keyIs_readW m p hj


/-- The counter block `v` with `i` added to its last 32 bits, modulo 2³²
(`Spec.Gcm.inc32`, `i` times). -/
def ctrAdd (v : BitVec 128) (i : Nat) : BitVec 128 := v.extractLsb' 32 96 ++ (v.extractLsb' 0 32 + BitVec.ofNat 32 i)

theorem ctrAdd_hi (v : BitVec 128) (i : Nat) : (ctrAdd v i).extractLsb' 32 96 = v.extractLsb' 32 96 := by
  rw [ctrAdd, BitVec.extractLsb'_append_eq_left]

theorem ctrAdd_lo (v : BitVec 128) (i : Nat) :
    (ctrAdd v i).extractLsb' 0 32 = v.extractLsb' 0 32 + BitVec.ofNat 32 i := by
  rw [ctrAdd, BitVec.extractLsb'_append_eq_right]

theorem ctrAdd_add (v : BitVec 128) (i j : Nat) : ctrAdd (ctrAdd v i) j = ctrAdd v (i + j) := by
  rw [ctrAdd, ctrAdd_hi, ctrAdd_lo, BitVec.add_assoc, ← BitVec.ofNat_add, ctrAdd]

theorem ctrAdd_zero (v : BitVec 128) : ctrAdd v 0 = v := by
  rw [ctrAdd, BitVec.add_zero, BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_eq_self]

/-- Four words packed most significant first, as the word-wise vector
operations do. -/
theorem pack4 (f : Nat → BitVec 32) :
    (List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32 * (3 - i)))) 0 =
      ((f 0 ++ f 1) ++ f 2) ++ f 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.false_or, BitVec.getLsbD_append]
  rcases (by omega_using [] : b < 32 ∨ (32 ≤ b ∧ b < 64) ∨ (64 ≤ b ∧ b < 96) ∨ 96 ≤ b) with h | h | h | h
  all_goals simp (disch := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
    Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true,
    Bool.false_or, Bool.or_false, hb]
  all_goals simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_true, Bool.true_and]
  all_goals exact congrArg _ (by omega_using [])

theorem hi96 (v : BitVec 128) : v.extractLsb' 32 96 = (vword v 0 ++ vword v 1) ++ vword v 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  rcases (by omega_using [] : b < 32 ∨ (32 ≤ b ∧ b < 64) ∨ 64 ≤ b) with h | h | h
  all_goals simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
  all_goals exact congrArg v.getLsbD (by omega_using [h])

/-- `vadduwm` by `counterOne` adds one to the last word. -/
theorem counter_step (v : BitVec 128) :
    (List.range 4).foldl (fun x i => x |||
      ((vword v i + vword Impl.Aes.PPC64LE.Crypto.counterOne i).setWidth 128 <<< (32 * (3 - i)))) 0 =
      ctrAdd v 1 := by
  have h0 : vword Impl.Aes.PPC64LE.Crypto.counterOne 0 = 0#32 := by decide
  have h1 : vword Impl.Aes.PPC64LE.Crypto.counterOne 1 = 0#32 := by decide
  have h2 : vword Impl.Aes.PPC64LE.Crypto.counterOne 2 = 0#32 := by decide
  have h3 : vword Impl.Aes.PPC64LE.Crypto.counterOne 3 = BitVec.ofNat 32 1 := by decide
  have e3 : vword v 3 = v.extractLsb' 0 32 := rfl
  rw [pack4 (fun i => vword v i + vword Impl.Aes.PPC64LE.Crypto.counterOne i), ctrAdd, hi96, h0, h1, h2, h3,
    BitVec.add_zero, BitVec.add_zero, BitVec.add_zero, e3]

theorem sbox_word (word undef : BitVec 64) :
    (((ofVBytes fun i => VG.VectorCrypto.aesSbox (vbyte (word ++ undef) i)).extractLsb' 64 64).setWidth 32) =
      VG.Proof.Aes.KeyWords.sub32 (word.setWidth 32) := by
  apply VG.Proof.Aes.KeyWords.ext32
  intro q hq
  rw [extract_high_word_byte _ hq, vbyte_packed _ (by omega_using []),
    ← extract_high_word_byte (word ++ undef) hq, BitVec.extractLsb'_append_eq_left,
    VG.Proof.Aes.KeyWords.sub32_byte _ hq]

/-- The architectural bytes are GCM's big-endian block bytes. -/
theorem aesState_byte (v : BitVec 128) {i : Nat} (hi : i < 16) :
    (aesState v).getD i 0 = (Spec.Gcm.toBytes v).getD i 0 := by
  rw [aesState, VG.Proof.Aes.Vector.getD_st _ hi, VG.Proof.Aes.toBytes_getD _ hi]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.VectorCrypto.vbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [getLsbD_rev128 _ (by omega_using [hi, hj])]
  exact congrArg v.getLsbD (by omega_using [hj])

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
  rw [show rev32 = byteRev32 from rfl, byteRev32_getLsbD _ (by omega_using [hk, hj]),
    show (8 * k + j) / 8 = k by omega_using [hj], show (8 * k + j) % 8 = j by omega_using [hj]]

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega_using []
  rw [e, rev32_bit _ (by omega_using [ht]) (by omega_using []), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega_using [ht] : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega_using [ht],
    VG.Proof.Aes.blockAt_bit _ _ (by omega_using []) (by omega_using [])]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega_using [])
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega_using [ht]] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega_using []]

end VG.Proof.Aes.PPC64LE.Crypto
