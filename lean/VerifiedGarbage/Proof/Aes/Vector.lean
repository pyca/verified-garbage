module

public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Proof.Aes.InvRounds
public import VerifiedGarbage.Proof.Framework.VectorCrypto -- shake: keep (re-exports byte-packing facts)
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority

/-! # Shared vector AES values implement FIPS 197 -/

@[expose] public section
namespace VG.Proof.Aes.Vector
open VG.VectorCrypto
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey sbox roundKey cipher bytesAt)

/-! ## GF(2⁸) -/

theorem mul_eq : aesMul = Spec.Aes.mul := rfl

/-- Both square and multiply `b²`, `b⁴`, …, `b¹²⁸` in the same order: unfolded
to the same term (no evaluation left for the kernel). -/
theorem inv_eq (b : BitVec 8) : aesInv b = Spec.Aes.inv b := by
  simp only [aesInv, Spec.Aes.inv, Spec.Aes.pow, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, mul_eq,
    ite_true, ite_false, Nat.testBit_eq_decide_div_mod_eq, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceEqDiff, decide_true, decide_false, Bool.false_eq_true]

theorem sbox_eq : aesSbox = sbox := by
  funext b
  simp only [aesSbox, sbox, inv_eq, ofBits8]

theorem mul_one' : ∀ b : BitVec 8, Spec.Aes.mul 1 b = b := by decide +kernel

/-! ## Bytes of vectors -/

export VG.Proof.VectorCrypto (getLsbD_append_block getLsbD_ofVBytes)

theorem vbyte_ofVBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : vbyte (ofVBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  exact getLsbD_ofVBytes f hi hr

theorem ext_vbyte {a b : BitVec 128} (h : ∀ i < 16, vbyte a i = vbyte b i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (BitVec.getLsbD · (j % 8)) (h (j / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt j (by omega : 8 > 0)),
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem vbyte_readW (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    vbyte (m.readW p 128) i = m (p + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m p (n := 16) hi]
  simp only [vbyte, Mem.readW]
  rfl

theorem vbyte_xor (a b : BitVec 128) (i : Nat) : vbyte (a ^^^ b) i = vbyte a i ^^^ vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

/-! ## States in registers -/

/-- The AES state held by a register. -/
def st (v : BitVec 128) : Spec.Aes.State := Vector.ofFn fun i => vbyte v i

theorem getD_ofFn {f : Fin 16 → Byte} {i : Nat} (h : i < 16) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

theorem getD_st (v : BitVec 128) {i : Nat} (h : i < 16) : (st v).getD i 0 = vbyte v i := by
  rw [st, getD_ofFn h]

theorem st_ext {s t : Spec.Aes.State} (h : ∀ i < 16, s.getD i 0 = t.getD i 0) : s = t := by
  apply Vector.ext; intro i hi
  have := h i hi
  simpa [Vector.getD, hi] using this

/-! ## FIPS 197's transformations, byte by byte -/

theorem getD_addRoundKey (s : Spec.Aes.State) (rk : List Byte) {i : Nat} (h : i < 16) :
    (addRoundKey s rk).getD i 0 = s.getD i 0 ^^^ rk.getD i 0 := by
  rw [addRoundKey, getD_ofFn h]

theorem getD_subBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (subBytes s).getD i 0 = sbox (s.getD i 0) := by
  simp [subBytes, Vector.getD, h]

theorem getD_shiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (shiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [shiftRows, getD_ofFn h]

theorem getD_mixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (mixColumns s).getD i 0 =
      Spec.Aes.mul 0x02 (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x03 (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0 ^^^ s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0 := by
  rw [mixColumns, getD_ofFn h]

theorem vbyte_mapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesMapBytes f x) i = f (vbyte x i) := by
  rw [aesMapBytes, vbyte_ofVBytes _ h]

theorem vbyte_shiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesShiftRows x) i = vbyte x (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  rw [aesShiftRows, vbyte_ofVBytes _ h]

theorem vbyte_mixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesMixColumns x) i =
      aesMul 0x02 (vbyte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x03 (vbyte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (vbyte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (vbyte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesMixColumns, aesMixWith, vbyte_ofVBytes _ h]

/-! ## The instructions -/

/-- A round key in a register: its bytes are those of `rk`. -/
def KeyIs (k : BitVec 128) (rk : List Byte) : Prop := ∀ i < 16, vbyte k i = rk.getD i 0

/-- `eor` with a round key is `AddRoundKey`. -/
theorem eor_st {v k : BitVec 128} {rk : List Byte} (hk : KeyIs k rk) :
    st (v ^^^ k) = addRoundKey (st v) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, getD_st _ hi, ← hk i hi]
  exact vbyte_xor v k i

/-- `aese` with a round key is `AddRoundKey`, then `SubBytes` and `ShiftRows`. -/
theorem aese_st {v k : BitVec 128} {rk : List Byte} (hk : KeyIs k rk) :
    st (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))) = shiftRows (subBytes (addRoundKey (st v) rk)) := by
  apply st_ext; intro i hi
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  rw [getD_st _ hi, getD_shiftRows _ hi, getD_subBytes _ (hs _), getD_addRoundKey _ _ (hs _),
    getD_st _ (hs _), ← hk _ (hs _), vbyte_mapBytes _ _ hi, vbyte_shiftRows _ hi, vbyte_xor, sbox_eq]


theorem subShift_st (v : BitVec 128) :
    st (aesShiftRows (aesMapBytes aesSbox v)) = shiftRows (subBytes (st v)) := by
  apply st_ext
  intro i hi
  have hs : i % 4 + 4*((i/4+i%4)%4) < 16 := by omega
  rw [getD_st _ hi, getD_shiftRows _ hi, getD_subBytes _ hs, getD_st _ hs,
    vbyte_shiftRows _ hi, vbyte_mapBytes _ _ hs, sbox_eq]

/-- `aesmc` is `MixColumns`. -/
theorem aesmc_st (v : BitVec 128) : st (aesMixColumns v) = mixColumns (st v) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, getD_mixColumns _ hi, vbyte_mixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq, mul_one']

/-! ## The cipher -/

/-- The state after `AddRoundKey` and `k` full rounds. -/
def rnds (w : List Byte) (x : Spec.Aes.State) (k : Nat) : Spec.Aes.State :=
  (List.range k).foldl
    (fun s j => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (j + 1)))
    (addRoundKey x (roundKey w 0))

theorem rnds_zero (w : List Byte) (x : Spec.Aes.State) :
    rnds w x 0 = addRoundKey x (roundKey w 0) := rfl

theorem rnds_succ (w : List Byte) (x : Spec.Aes.State) (k : Nat) :
    rnds w x (k + 1) =
      addRoundKey (mixColumns (shiftRows (subBytes (rnds w x k)))) (roundKey w (k + 1)) := by
  simp only [rnds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem cipher_eq (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher nr w x = addRoundKey (shiftRows (subBytes (rnds w x (nr - 1)))) (roundKey w nr) := rfl

/-- A full round: `aese` with round key `j`, then `aesmc`. The register
holds the state before the `AddRoundKey` of round key `j`. -/
theorem round_st {v k : BitVec 128} {w : List Byte} {x : Spec.Aes.State} {j : Nat}
    (hk : KeyIs k (roundKey w j)) (h : addRoundKey (st v) (roundKey w j) = rnds w x j) :
    addRoundKey (st (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))) (roundKey w (j + 1)) =
      rnds w x (j + 1) := by
  rw [rnds_succ, aesmc_st, aese_st hk, h]

/-- The last round: `aese` with round key `Nr − 1`, then `eor` with round key `Nr`. -/
theorem last_st {v k k' : BitVec 128} {w : List Byte} {x : Spec.Aes.State} {nr : Nat}
    (hk : KeyIs k (roundKey w (nr - 1))) (hk' : KeyIs k' (roundKey w nr))
    (h : addRoundKey (st v) (roundKey w (nr - 1)) = rnds w x (nr - 1)) :
    st (aesMapBytes aesSbox (aesShiftRows (v ^^^ k)) ^^^ k') = cipher nr w x := by
  rw [eor_st hk', aese_st hk, h, cipher_eq]

/-- Round key `j`, loaded from the schedule. -/
theorem keyIs_readW (m : Mem) (p : Addr) {L j : Nat} (hj : 16 * j + 16 ≤ L) :
    KeyIs (m.readW (p + BitVec.ofNat 64 (16 * j)) 128) (roundKey (bytesAt m p L) j) := by
  intro i hi
  rw [vbyte_readW _ _ hi, BitVec.add_assoc, ← BitVec.ofNat_add]
  simp [roundKey, bytesAt, List.getD, hi, show 16 * j + i < L by omega]


open VG.Spec.Aes (invSubBytes invShiftRows invMixColumns invSbox invCipher)
open VG.Proof.Aes (rkState irnd invMid invMid_succ invCipher_eq invMixColumns_addRoundKey)

theorem invSbox_eq : aesInvSbox = invSbox := by
  funext b
  simp only [aesInvSbox, invSbox, Spec.Aes.invAffine, inv_eq, ofBits8]

theorem getD_invSubBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invSubBytes s).getD i 0 = invSbox (s.getD i 0) := by
  simp [invSubBytes, Vector.getD, h]

theorem getD_invShiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invShiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) 0 := by
  rw [invShiftRows, getD_ofFn h]

theorem getD_invMixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invMixColumns s).getD i 0 =
      Spec.Aes.mul 0x0e (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0b (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0d (s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x09 (s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0) := by
  rw [invMixColumns, getD_ofFn h]

theorem vbyte_invShiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesInvShiftRows x) i = vbyte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) := by
  rw [aesInvShiftRows, vbyte_ofVBytes _ h]

theorem vbyte_invMixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesInvMixColumns x) i =
      aesMul 0x0e (vbyte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0b (vbyte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0d (vbyte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x09 (vbyte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesInvMixColumns, aesMixWith, vbyte_ofVBytes _ h]

/-- `aesimc` is `InvMixColumns`. -/
theorem st_aesimc (k : BitVec 128) : st (aesInvMixColumns k) = invMixColumns (st k) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, vbyte_invMixColumns _ hi, getD_invMixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq]

/-- `aesd` without its `AddRoundKey`: `InvShiftRows`, then `InvSubBytes`. -/
theorem st_invSub (v : BitVec 128) :
    st (aesMapBytes aesInvSbox (aesInvShiftRows v)) = invSubBytes (invShiftRows (st v)) := by
  apply st_ext; intro i hi
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + 4 - j % 4) % 4) < 16 := fun j => by omega
  rw [getD_st _ hi, vbyte_mapBytes _ _ hi, vbyte_invShiftRows _ hi, getD_invSubBytes _ hi,
    getD_invShiftRows _ hi, getD_st _ (hs _), invSbox_eq]

/-- `InvMixColumns` of a round key, as the bytes of a round key. -/
def imcKey (rk : List Byte) : List Byte := (invMixColumns (rkState rk)).toList

theorem getD_imcKey (rk : List Byte) {i : Nat} (hi : i < 16) :
    (imcKey rk).getD i 0 = (invMixColumns (rkState rk)).getD i 0 := by
  simp [imcKey, Vector.getD, hi]

/-- `aesimc` of round key `rk` in a register. -/
theorem keyIs_aesimc {k : BitVec 128} {rk : List Byte} (hk : KeyIs k rk) :
    KeyIs (aesInvMixColumns k) (imcKey rk) := by
  intro i hi
  rw [← getD_st _ hi, st_aesimc, getD_imcKey _ hi]
  refine congrArg (fun s => (invMixColumns s).getD i 0) ?_
  apply st_ext; intro j hj
  rw [getD_st _ hj, hk j hj]
  simp [rkState, Vector.getD, hj]

/-- `aesd` with the round key `K` that turns the register into `Z`, then
`aesimc`, is a middle round of the inverse cipher from `Z`, with round key
`rk`, the register then needing `InvMixColumns` of `rk`. -/
theorem dround_st {v k : BitVec 128} {K rk : List Byte} {Z : Spec.Aes.State} (hk : KeyIs k K)
    (h : addRoundKey (st v) K = Z) :
    addRoundKey (st (aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k)))))
        (imcKey rk) = invMixColumns (addRoundKey (invSubBytes (invShiftRows Z)) rk) := by
  apply st_ext; intro i hi
  rw [invMixColumns_addRoundKey _ _ hi, getD_addRoundKey _ _ hi, getD_imcKey _ hi, st_aesimc,
    st_invSub, eor_st hk, h]

/-- `aesd` with the round key `K` that turns the register into `Z`, then
`eor` with `rk₀`: the last round of the inverse cipher. -/
theorem dlast_st {v k k₀ : BitVec 128} {K rk₀ : List Byte} {Z : Spec.Aes.State} (hk : KeyIs k K)
    (hk₀ : KeyIs k₀ rk₀) (h : addRoundKey (st v) K = Z) :
    st (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k)) ^^^ k₀) =
      addRoundKey (invSubBytes (invShiftRows Z)) rk₀ := by
  rw [eor_st hk₀, st_invSub, eor_st hk, h]

end VG.Proof.Aes.Vector
