import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Aes.X86_64.AesNi
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.Omega

section

section

/-!
# AES key expansion as 32-bit words

`W m kp nk i` is word `w[i]` of the key schedule of the `nk`-word key at `kp`,
as the 32-bit value whose bytes, least significant first, are the word's bytes
(`wv`), which is how a doubleword of an SSE register holds it. `expandKey_eq`:
FIPS 197's `KEYEXPANSION` is these words, in order; `bytesAt_eq`: memory
holding them as little-endian doublewords holds the schedule.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Spec.Aes (Word subWord rotWord rcon xorWord expandWords expandKey bytesAt rounds)

/-- The bytes of a word, least significant first. -/
def wv (d : BitVec 32) : Word := (List.range 4).map fun j => d.extractLsb' (8 * j) 8

/-- `SUBWORD`, as `aeskeygenassist` computes it. -/
def sub32 (x : BitVec 32) : BitVec 32 :=
  aesSbox (x.extractLsb' 24 8) ++ aesSbox (x.extractLsb' 16 8) ++
    aesSbox (x.extractLsb' 8 8) ++ aesSbox (x.extractLsb' 0 8)

/-- `temp` of `KEYEXPANSION` for word `i`, from `w[i − 1]`. -/
def temp32 (nk i : Nat) (x : BitVec 32) : BitVec 32 :=
  if i % nk = 0 then (sub32 x).rotateRight 8 ^^^ (Impl.Aes.X86_64.AesNi.rc (i / nk)).setWidth 32
  else if nk > 6 ∧ i % nk = 4 then sub32 x else x

/-- Word `i` of the key schedule of the `nk`-word key at `kp`. -/
def W (m : Mem) (kp : Addr) (nk : Nat) (i : Nat) : BitVec 32 :=
  if i < nk ∨ nk = 0 then m.readW (kp + BitVec.ofNat 64 (4 * i)) 32
  else W m kp nk (i - nk) ^^^ temp32 nk i (W m kp nk (i - 1))
termination_by i
decreasing_by all_goals omega_arith

theorem W_lt {m : Mem} {kp : Addr} {nk i : Nat} (h : i < nk) :
    W m kp nk i = m.readW (kp + BitVec.ofNat 64 (4 * i)) 32 := by
  rw [W]; simp [h]

theorem W_ge {m : Mem} {kp : Addr} {nk i : Nat} (h0 : 0 < nk) (h : nk ≤ i) :
    W m kp nk i = W m kp nk (i - nk) ^^^ temp32 nk i (W m kp nk (i - 1)) := by
  rw [W]; simp only [show ¬ (i < nk ∨ nk = 0) by omega_arith, ite_false]

/-! ## Words and bytes -/

theorem wv_eq (d : BitVec 32) :
    wv d = [d.extractLsb' 0 8, d.extractLsb' 8 8, d.extractLsb' 16 8, d.extractLsb' 24 8] := rfl

theorem extract_xor (a b : BitVec 32) (k : Nat) :
    (a ^^^ b).extractLsb' k 8 = a.extractLsb' k 8 ^^^ b.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem wv_xor (a b : BitVec 32) : wv (a ^^^ b) = xorWord (wv a) (wv b) := by
  simp only [wv_eq, extract_xor, xorWord, List.zipWith_cons_cons, List.zipWith_nil_left]

theorem extract_cat (a b c d : BitVec 8) :
    (a ++ b ++ c ++ d).extractLsb' 0 8 = d ∧ (a ++ b ++ c ++ d).extractLsb' 8 8 = c ∧
      (a ++ b ++ c ++ d).extractLsb' 16 8 = b ∧ (a ++ b ++ c ++ d).extractLsb' 24 8 = a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp (disch := omega_arith) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
      Bool.true_and, ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega_arith)

theorem rot_cat (a b c d : BitVec 8) : (a ++ b ++ c ++ d).rotateRight 8 = d ++ a ++ b ++ c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi' : i < 32 := hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, hi', decide_true, Bool.true_and]
  rcases (by omega_arith : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h <;>
    simp (disch := omega_arith) only [ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega_arith)

theorem wv_cat (a b c d : BitVec 8) : wv (a ++ b ++ c ++ d) = [d, c, b, a] := by
  obtain ⟨e0, e1, e2, e3⟩ := extract_cat a b c d
  rw [wv_eq, e0, e1, e2, e3]

theorem sub_wv (x : BitVec 32) : subWord (wv x) = wv (sub32 x) := by
  rw [sub32, wv_cat, wv_eq, subWord, sbox_eq]; rfl

theorem subRot_wv (x : BitVec 32) : subWord (rotWord (wv x)) = wv ((sub32 x).rotateRight 8) := by
  rw [sub32, rot_cat, wv_cat, wv_eq, rotWord, subWord, sbox_eq]; rfl

theorem rcon_wv (j : Nat) : rcon j = wv ((Impl.Aes.X86_64.AesNi.rc j).setWidth 32) := by
  rw [show (Impl.Aes.X86_64.AesNi.rc j).setWidth 32 = 0#8 ++ 0#8 ++ 0#8 ++ Impl.Aes.X86_64.AesNi.rc j by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_zero]
    by_cases h : i < 8
    · simp [h]; omega_arith
    · simp [h]; exact fun _ => BitVec.getLsbD_of_ge _ _ (by omega_arith), wv_cat]
  rfl

theorem temp_wv (nk i : Nat) (x : BitVec 32) :
    (if i % nk = 0 then xorWord (subWord (rotWord (wv x))) (rcon (i / nk))
      else if nk > 6 ∧ i % nk = 4 then subWord (wv x) else wv x) = wv (temp32 nk i x) := by
  unfold temp32
  by_cases h1 : i % nk = 0
  · simp only [h1, ite_true, wv_xor, subRot_wv, rcon_wv]
  · by_cases h2 : nk > 6 ∧ i % nk = 4
    · have h2' : (nk > 6 ∧ i % nk = 4) = True := eq_true h2
      simp only [h1, h2', ite_true, ite_false, sub_wv]
    · simp only [h1, h2, ite_false]

/-! ## The key and the schedule -/

theorem getD_mapRange {α : Type} (f : Nat → α) {n i : Nat} (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, h]

theorem ofNat_add' (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 (a + b) = p + BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- Word `i` of the key. -/
theorem keyWord (m : Mem) (kp : Addr) {L i : Nat} (h : 4 * i + 4 ≤ L) :
    ((bytesAt m kp L).drop (4 * i)).take 4 = wv (m.readW (kp + BitVec.ofNat 64 (4 * i)) 32) := by
  apply List.ext_getElem
  · simp [bytesAt, wv]; omega_arith
  · intro j h₁ h₂
    have hj : j < 4 := by simpa [wv] using h₂
    simp only [List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range,
      wv]
    rw [ofNat_add', Mem.readW_byte m (kp + BitVec.ofNat 64 (4 * i)) hj]

theorem expandWords_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    ∀ n, expandWords (bytesAt m kp (4 * nk)) nk n = (List.range n).map fun i => wv (W m kp nk i)
  | 0 => rfl
  | i + 1 => by
    rw [expandWords, expandWords_eq m kp h0 i, List.range_succ, List.map_append, List.map_singleton]
    by_cases h : i < nk
    · simp only [h, ite_true]
      rw [keyWord _ _ (by omega_arith), W_lt h]
    · simp only [h, ite_false]
      rw [getD_mapRange _ _ (by omega_arith), getD_mapRange _ _ (by omega_arith), temp_wv, ← wv_xor,
        ← W_ge h0 (by omega_arith)]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- `KEYEXPANSION`, as words. -/
theorem expandKey_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    expandKey (bytesAt m kp (4 * nk)) =
      ((List.range (4 * (rounds nk + 1))).map fun i => wv (W m kp nk i)).flatten := by
  rw [expandKey, length_bytesAt, show 4 * nk / 4 = nk by omega_arith, expandWords_eq m kp h0]

/-- Memory holding the words `f 0 … f (K − 1)` as little-endian doublewords. -/
theorem bytesAt_eq (m : Mem) (p : Addr) (f : Nat → BitVec 32) :
    ∀ K, (∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i) →
      bytesAt m p (4 * K) = ((List.range K).map fun i => wv (f i)).flatten
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.map_append, List.flatten_append, ← bytesAt_eq m p f K
      fun i hi => h i (by omega_arith), List.map_singleton, List.flatten_singleton, ← h K (by omega_arith),
      show 4 * (K + 1) = 4 * K + 4 by omega_arith, bytesAt, bytesAt, List.range_add, List.map_append,
      List.map_map]
    congr 1
    simp only [wv]
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [ofNat_add', Mem.readW_byte m (p + BitVec.ofNat 64 (4 * K)) hj]

end VG.Proof.Aes.X86_64.AesNi

end

/-!
# AES-NI key expansion: the steps

What `kstep` and `kstepB6` compute, as doublewords (one symbolic execution of
each, for any registers and offsets), and `good_store`: storing a register
whose first `n` doublewords are the next `n` words of the schedule extends the
stored prefix of the schedule by `n` words.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ kstep kgen kmix kstepB6)

/-! ## Doublewords -/

/-- `pslldq x, 4`. -/
def sh (x : BitVec 128) : BitVec 128 := x <<< 32

theorem pslldq4 (x : BitVec 128) : XShiftOp.eval .pslldq x 4 = sh x := rfl

theorem eval_pxor' (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem dword_xor (a b : BitVec 128) (j : Nat) : dword (a ^^^ b) j = dword a j ^^^ dword b j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]

theorem dword_sh0 (x : BitVec 128) : dword (sh x) 0 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, sh, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_zero]
  simp; omega_arith

theorem dword_sh (x : BitVec 128) {j : Nat} (hj : j < 3) : dword (sh x) (j + 1) = dword x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, sh, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rw [decide_eq_true (by omega_arith), decide_eq_false (by omega_arith), Bool.not_false, Bool.true_and,
    Bool.true_and]
  exact congrArg _ (by omega_arith)

theorem dword_sh1 (x : BitVec 128) : dword (sh x) 1 = dword x 0 := dword_sh x (j := 0) (by decide)
theorem dword_sh2 (x : BitVec 128) : dword (sh x) 2 = dword x 1 := dword_sh x (j := 1) (by decide)
theorem dword_sh3 (x : BitVec 128) : dword (sh x) 3 = dword x 2 := dword_sh x (j := 2) (by decide)

/-- `prefixXor(x) ⊕ t`, as `kstep` computes it. -/
def kv (x t : BitVec 128) : BitVec 128 := x ^^^ sh x ^^^ sh (sh x) ^^^ sh (sh (sh x)) ^^^ t

theorem dword_kv (x t : BitVec 128) :
    dword (kv x t) 0 = dword x 0 ^^^ dword t 0 ∧
    dword (kv x t) 1 = dword x 1 ^^^ (dword x 0 ^^^ dword t 1) ∧
    dword (kv x t) 2 = dword x 2 ^^^ (dword x 1 ^^^ (dword x 0 ^^^ dword t 2)) ∧
    dword (kv x t) 3 = dword x 3 ^^^ (dword x 2 ^^^ (dword x 1 ^^^ (dword x 0 ^^^ dword t 3))) := by
  simp only [kv, dword_xor, dword_sh0, dword_sh1, dword_sh2, dword_sh3, BitVec.zero_xor,
    BitVec.xor_assoc, and_self]

/-- `[b₀, b₀ ⊕ b₁, …] ⊕ t`, as `kstepB6` computes it. -/
def kb (b t : BitVec 128) : BitVec 128 := b ^^^ sh b ^^^ t

theorem dword_kb (b t : BitVec 128) :
    dword (kb b t) 0 = dword b 0 ^^^ dword t 0 ∧
    dword (kb b t) 1 = dword b 1 ^^^ (dword b 0 ^^^ dword t 1) := by
  simp only [kb, dword_xor, dword_sh0, dword_sh1, BitVec.zero_xor, BitVec.xor_assoc, and_self]

theorem shuf_ff (x : BitVec 128) :
    shufDwords x 0xff = ofDwords (dword x 3) (dword x 3) (dword x 3) (dword x 3) := rfl
theorem shuf_55 (x : BitVec 128) :
    shufDwords x 0x55 = ofDwords (dword x 1) (dword x 1) (dword x 1) (dword x 1) := rfl
theorem shuf_aa (x : BitVec 128) :
    shufDwords x 0xaa = ofDwords (dword x 2) (dword x 2) (dword x 2) (dword x 2) := rfl

theorem kga1 (x : BitVec 128) (r : BitVec 8) :
    dword (aesKeygenAssist x r) 1 = (sub32 (dword x 1)).rotateRight 8 ^^^ r.setWidth 32 := by
  simp only [aesKeygenAssist, dword_ofDwords_1]; rfl

theorem kga2 (x : BitVec 128) (r : BitVec 8) : dword (aesKeygenAssist x r) 2 = sub32 (dword x 3) := by
  simp only [aesKeygenAssist, dword_ofDwords_2]; rfl

theorem kga3 (x : BitVec 128) (r : BitVec 8) :
    dword (aesKeygenAssist x r) 3 = (sub32 (dword x 3)).rotateRight 8 ^^^ r.setWidth 32 := by
  simp only [aesKeygenAssist, dword_ofDwords_3]; rfl

/-! ## `aesenclast` on equal columns -/

/-- `c` in every doubleword. -/
def bc (c : BitVec 8) : BitVec 128 := ofDwords (c.setWidth 32) (c.setWidth 32) (c.setWidth 32) (c.setWidth 32)

theorem byte_bcast (w : BitVec 32) {i : Nat} (h : i < 16) :
    byte (ofDwords w w w w) i = w.extractLsb' (8 * (i % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byte, ofDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and]
  repeat' split
  all_goals exact congrArg _ (by omega_arith)

theorem sub32_extract (u : BitVec 32) {m : Nat} (h : m < 4) :
    (sub32 u).extractLsb' (8 * m) 8 = aesSbox (u.extractLsb' (8 * m) 8) := by
  obtain ⟨e0, e1, e2, e3⟩ := extract_cat (aesSbox (u.extractLsb' 24 8)) (aesSbox (u.extractLsb' 16 8))
    (aesSbox (u.extractLsb' 8 8)) (aesSbox (u.extractLsb' 0 8))
  rcases (by omega_arith : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl
  · exact e0
  · exact e1
  · exact e2
  · exact e3

/-- `aesenclast` of equal columns: `ShiftRows` moves bytes only between
columns, so each is `SubWord` of the column, XORed with the round key. -/
theorem aesenc_bcast (u k : BitVec 32) :
    XBinOp.eval .aesenclast (ofDwords u u u u) (ofDwords k k k k) =
      ofDwords (sub32 u ^^^ k) (sub32 u ^^^ k) (sub32 u ^^^ k) (sub32 u ^^^ k) := by
  refine VG.Proof.Gcm.X86_64.ext_byte fun i hi => ?_
  show byte (aesMapBytes aesSbox (aesShiftRows (ofDwords u u u u)) ^^^ ofDwords k k k k) i = _
  rw [byte_xor, byte_mapBytes _ _ hi, byte_shiftRows _ hi, byte_bcast _ (by omega_arith), byte_bcast _ hi,
    byte_bcast _ hi, show (i % 4 + 4 * ((i / 4 + i % 4) % 4)) % 4 = i % 4 by omega_arith]
  have hx : ∀ a b : BitVec 32, (a ^^^ b).extractLsb' (8 * (i % 4)) 8 =
      a.extractLsb' (8 * (i % 4)) 8 ^^^ b.extractLsb' (8 * (i % 4)) 8 := fun a b => extract_xor a b _
  rw [hx, sub32_extract _ (by omega_arith)]

theorem shuf_00 (x : BitVec 128) :
    shufDwords x 0 = ofDwords (dword x 0) (dword x 0) (dword x 0) (dword x 0) := rfl

/-- `RotWord` of each of equal doublewords: the register shifted right by a
byte, whose doubleword 0 is broadcast. -/
theorem rot_bcast (w : BitVec 32) :
    shufDwords (XShiftOp.eval .psrldq (ofDwords w w w w) 1) 0 =
      ofDwords (w.rotateRight 8) (w.rotateRight 8) (w.rotateRight 8) (w.rotateRight 8) := by
  have e : dword (XShiftOp.eval .psrldq (ofDwords w w w w) 1) 0 = w.rotateRight 8 := by
    show dword (ofDwords w w w w >>> 8) 0 = _
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [getLsbD_dword, BitVec.getLsbD_ushiftRight, ofDwords, BitVec.getLsbD_append,
      BitVec.getLsbD_rotateRight, hj, decide_true, Bool.true_and]
    repeat' split
    all_goals first | (exact congrArg _ (by omega_arith)) | (exfalso; omega_arith)
  rw [shuf_00, e]

theorem rot_extract (w : BitVec 32) {m : Nat} (h : m < 4) :
    (w.rotateRight 8).extractLsb' (8 * m) 8 = w.extractLsb' (8 * ((m + 1) % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hlt : 8 * m + j < 32 := by omega_arith
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, hj, hlt, decide_true, Bool.true_and]
  repeat' split
  all_goals first | (exact congrArg _ (by omega_arith)) | (exfalso; omega_arith)

/-- `SubWord` commutes with `RotWord`. -/
theorem sub32_rot (w : BitVec 32) : sub32 (w.rotateRight 8) = (sub32 w).rotateRight 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hb : ∀ v : BitVec 32, v.getLsbD j = (v.extractLsb' (8 * (j / 8)) 8).getLsbD (j % 8) := fun v => by
    simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega_arith, decide_true, Bool.true_and]
    exact congrArg _ (by omega_arith)
  rw [hb, hb ((sub32 w).rotateRight 8)]
  simp (disch := omega_arith) only [sub32_extract, rot_extract]

/-- What `kgen` leaves in `xmm3`, from the source `x` and the round key `K`. -/
def genT (x : BitVec 128) (sel : BitVec 8) (rot : Bool) (K : BitVec 128) : BitVec 128 :=
  XBinOp.eval .aesenclast (if rot then shufDwords (XShiftOp.eval .psrldq (shufDwords x sel) 1) 0
    else shufDwords x sel) K

theorem genT_rot (x : BitVec 128) (sel : BitVec 8) (i : Nat) (r : BitVec 8)
    (hs : shufDwords x sel = ofDwords (dword x i) (dword x i) (dword x i) (dword x i)) :
    genT x sel true (bc r) =
      ofDwords ((sub32 (dword x i)).rotateRight 8 ^^^ r.setWidth 32) ((sub32 (dword x i)).rotateRight 8 ^^^ r.setWidth 32)
        ((sub32 (dword x i)).rotateRight 8 ^^^ r.setWidth 32) ((sub32 (dword x i)).rotateRight 8 ^^^ r.setWidth 32) := by
  show XBinOp.eval .aesenclast (shufDwords (XShiftOp.eval .psrldq (shufDwords x sel) 1) 0) (bc r) = _
  rw [hs, rot_bcast, bc, aesenc_bcast, sub32_rot]

theorem genT_sub (x : BitVec 128) :
    genT x 0xff false 0 = ofDwords (sub32 (dword x 3)) (sub32 (dword x 3)) (sub32 (dword x 3)) (sub32 (dword x 3)) := by
  have z : (0 : BitVec 128) = ofDwords 0#32 0#32 0#32 0#32 := rfl
  show XBinOp.eval .aesenclast (shufDwords x 0xff) 0 = _
  rw [shuf_ff, z, aesenc_bcast, BitVec.xor_zero]

/-- `prefixXor(x) ⊕ t` with two shifts, as `kmix` computes it, is `kv`. -/
theorem kv2 (x t : BitVec 128) :
    x ^^^ sh x ^^^ (x ^^^ sh x) <<< 64 ^^^ t = kv x t := by
  have h64 : ∀ y : BitVec 128, y <<< 64 = sh (sh y) := fun y => by
    simp only [sh, ← BitVec.shiftLeft_add]
  rw [h64, kv]
  simp only [sh, BitVec.shiftLeft_xor_distrib, BitVec.xor_assoc]

theorem pslldq8 (x : BitVec 128) : XShiftOp.eval .pslldq x 8 = x <<< 64 := rfl

/-! ## The steps -/

theorem kstep_exec (d s : XReg) (sel : BitVec 8) (rot : Bool) (k : XReg) (off : Nat) (st : State)
    (hd3 : d ≠ .xmm3) (hd4 : d ≠ .xmm4) (hk3 : k ≠ .xmm3)
    (hw : InRegions st.wr (st.gpr .rdx + BitVec.ofInt 64 (off : Int)) 16) :
    WP isa (.block (kstep d s sel rot k off)) st fun st' =>
      st'.xmm d = kv (st.xmm d) (genT (st.xmm s) sel rot (st.xmm k)) ∧
      st'.mem = st.mem.writeW (st.gpr .rdx + BitVec.ofInt 64 (off : Int))
        (kv (st.xmm d) (genT (st.xmm s) sel rot (st.xmm k))) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  rw [← kv2]
  cases rot <;>
  simp only [reduceCtorEq, ↓reduceIte, kstep, kgen, kmix, Bool.false_eq_true, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    State.store128, ea_at, hw, hd3, hd4, hk3, Ne.symm hd3, Ne.symm hd4, Option.some.injEq, exists_eq_left',
    eval_movdqa, pslldq4, pslldq8, eval_pxor', genT] <;>
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, trivial, trivial, trivial,
    fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

theorem kstepB6_exec (off : Nat) (st : State)
    (hw : InRegions st.wr (st.gpr .rdx + BitVec.ofInt 64 (off : Int)) 16) :
    WP isa (.block (kstepB6 off)) st fun st' =>
      st'.xmm .xmm2 = kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff) ∧
      st'.mem = st.mem.writeW (st.gpr .rdx + BitVec.ofInt 64 (off : Int))
        (kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, kstepB6, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, ea_at, hw, 
    Option.some.injEq, exists_eq_left', eval_movdqa, pslldq4, eval_pxor']
  exact ⟨rfl, rfl, trivial, trivial, trivial, fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

/-! ## The stored words -/

/-- Words `0 … K − 1` of `f` are stored at `p`, as little-endian doublewords. -/
def Good (m : Mem) (p : Addr) (f : Nat → BitVec 32) (K : Nat) : Prop :=
  ∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i

theorem good_store {m : Mem} {p : Addr} {f : Nat → BitVec 32} {K : Nat} (hG : Good m p f K)
    (v : BitVec 128) {n : Nat} (hn : n ≤ 4) (hv : ∀ j < n, dword v j = f (K + j))
    (hK : 4 * K + 16 ≤ 240) :
    Good (m.writeW (p + BitVec.ofNat 64 (4 * K)) v) p f (K + n) := by
  intro i hi
  by_cases h : i < K
  · rw [Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
    exact hG i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = K + j := ⟨i - K, by omega_arith⟩
    rw [show 4 * (K + j) = 4 * K + 4 * j by omega_arith, ofNat_add', readW_writeW128 _ _ _ (by omega_arith)]
    exact hv j (by omega_arith)

theorem Good.mono {m : Mem} {p : Addr} {f : Nat → BitVec 32} {K K' : Nat} (h : Good m p f K)
    (hK : K' ≤ K) : Good m p f K' := fun i hi => h i (by omega_arith)

end VG.Proof.Aes.X86_64.AesNi

end

/-!
# AES-NI key expansion: the whole function

`expandKey_verified` proves `Impl.Aes.X86_64.AesNi.expandKey` against
`expandKeyX86_64`. After each step, the first `K` words of the schedule are
stored (`KS`) and the registers hold the last words computed; the steps are
composed by induction (`wp_range_flatMap`), each proved once for any index
(`kstepK`, `kstepB6K`).
-/

namespace VG.Proof.Aes.X86_64.AesNi.Key

open VG VG.X86_64
open VG.Proof.Aes.X86_64.AesNi
open VG.Impl.Aes.X86_64.AesNi (at_ kstep kstepB6 rc expand128 expand192 expand256 expandKey)

section
variable (s₀ : State)

abbrev kp : Addr := s₀.gpr .rdi
abbrev len : Nat := (s₀.gpr .rsi).toNat
abbrev sp : Addr := s₀.gpr .rdx
abbrev schR : Region := ⟨sp s₀, 240⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨kp s₀, len s₀⟩]
  wr : s₀.wr = [schR s₀, ⟨s₀.gpr .rcx, 512⟩]
  ret : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (schR s₀)
  len : len s₀ = 16 ∨ len s₀ = 24 ∨ len s₀ = 32

theorem pre_of (s₀ : State) (h : expandKeyX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- Words `0 … K − 1` of the schedule of the `nk`-word key are stored. -/
structure KS (s₀ : State) (nk K : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [schR s₀] s₀.mem s.mem
  good : Good s.mem (sp s₀) (W s₀.mem (kp s₀) nk) K

theorem KS.of_eq {s₀ : State} {nk K K' : Nat} {s : State} (h : KS s₀ nk K s) (e : K = K') :
    KS s₀ nk K' s := e ▸ h

theorem sched_in {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) (hg : s.gpr = s₀.gpr)
    {off : Nat} (h : off + 16 ≤ 240) :
    InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 (off : Int)) 16 :=
  ⟨schR s₀, by simp [hwr, hp.wr], by rw [hg, ofInt_natCast]; exact contains_offset h (by omega_arith)⟩

theorem key_in {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hg : s.gpr = s₀.gpr)
    {off : Nat} (h : off + 16 ≤ len s₀) :
    InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (off : Int)) 16 :=
  ⟨⟨kp s₀, len s₀⟩, by simp [hrd, hp.rd], by
    rw [hg, ofInt_natCast]
    have : len s₀ < 2 ^ 64 := (s₀.gpr .rsi).isLt
    exact contains_offset h (by omega_arith)⟩

/-! ## Words -/

theorem W_plain {m : Mem} {p : Addr} {nk i : Nat} (h0 : 0 < nk) (h : nk ≤ i)
    (hp : ∀ y, temp32 nk i y = y) : W m p nk i = W m p nk (i - nk) ^^^ W m p nk (i - 1) := by
  rw [W_ge h0 h, hp]

theorem temp_plain {nk i : Nat} (h1 : i % nk ≠ 0) (h2 : ¬ (nk > 6 ∧ i % nk = 4)) (y : BitVec 32) :
    temp32 nk i y = y := by
  simp only [temp32, h1, h2, ite_false]

theorem temp_rc {nk i : Nat} (h1 : i % nk = 0) (y : BitVec 32) :
    temp32 nk i y = (sub32 y).rotateRight 8 ^^^ (rc (i / nk)).setWidth 32 := by
  simp only [temp32, h1, ite_true]

theorem temp_sub {nk i : Nat} (h1 : i % nk ≠ 0) (h2 : nk > 6 ∧ i % nk = 4) (y : BitVec 32) :
    temp32 nk i y = sub32 y := by
  have h2' : (nk > 6 ∧ i % nk = 4) = True := eq_true h2
  simp only [temp32, h1, h2', ite_true, ite_false]

theorem dword_bcast (a : BitVec 32) {j : Nat} (hj : j < 4) : dword (ofDwords a a a a) j = a := by
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp

/-- A doubleword of a register loaded from the key. -/
theorem dword_key (m : Mem) (p : Addr) (o j i : Nat) (hj : j < 4) (ho : o + 4 * j = 4 * i) :
    dword (m.readW (p + BitVec.ofInt 64 (o : Int)) 128) j = m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := by
  rw [dword_readW _ _ hj, ofInt_natCast, ← ofNat_add', ho]

theorem psrldq8 (x : BitVec 128) : XShiftOp.eval .psrldq x 8 = x >>> 64 := rfl

theorem dword_shr64 (x : BitVec 128) :
    dword (XShiftOp.eval .psrldq x 8) 0 = dword x 2 ∧ dword (XShiftOp.eval .psrldq x 8) 1 = dword x 3 := by
  rw [psrldq8]
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [getLsbD_dword, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and] <;>
    exact congrArg _ (by omega_arith)

/-- Storing the next `n` words. -/
theorem store_mem {s₀ : State} {nk K n : Nat} {m : Mem} (hf : Frame [schR s₀] s₀.mem m)
    (hg : Good m (sp s₀) (W s₀.mem (kp s₀) nk) K) (v : BitVec 128) (off : Nat) (hoff : off = 4 * K)
    (hn : n ≤ 4) (hv : ∀ j < n, dword v j = W s₀.mem (kp s₀) nk (K + j)) (hK : 4 * K + 16 ≤ 240) :
    Frame [schR s₀] s₀.mem (m.writeW (sp s₀ + BitVec.ofInt 64 (off : Int)) v) ∧
      Good (m.writeW (sp s₀ + BitVec.ofInt 64 (off : Int)) v) (sp s₀) (W s₀.mem (kp s₀) nk) (K + n) := by
  subst hoff
  rw [ofInt_natCast]
  exact ⟨hf.writeW (List.mem_singleton_self _) _ (contains_offset hK (by omega_arith)), good_store hg _ hn hv hK⟩

theorem good_zero (m : Mem) (p : Addr) (f : Nat → BitVec 32) : Good m p f 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-! ## The steps -/

/-- `kstep`: from words `a … a + 3` in `d`, words `b … b + 3` (`b = a + Nk`). -/
theorem kstepK {s₀ : State} (hp : Pre s₀) {nk : Nat} (h0 : 0 < nk) (d s : XReg) (sel : BitVec 8)
    (rot : Bool) (k : XReg) (a b off : Nat) (hb : b = a + nk) (hoff : off = 4 * b) (hK : 4 * b + 16 ≤ 240)
    (hd3 : d ≠ .xmm3) (hd4 : d ≠ .xmm4) (hk3 : k ≠ .xmm3) {st : State} (hI : KS s₀ nk b st)
    (hA : ∀ j < 4, dword (st.xmm d) j = W s₀.mem (kp s₀) nk (a + j))
    (hT : ∀ j < 4, dword (genT (st.xmm s) sel rot (st.xmm k)) j =
      temp32 nk b (W s₀.mem (kp s₀) nk (b - 1)))
    (hres : ∀ j, 0 < j → j < 4 → ∀ y, temp32 nk (b + j) y = y) :
    WP isa (.block (kstep d s sel rot k off)) st fun st' => KS s₀ nk (b + 4) st' ∧
      (∀ j < 4, dword (st'.xmm d) j = W s₀.mem (kp s₀) nk (b + j)) ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  subst hoff hb
  refine WP.mono (kstep_exec d s sel rot k _ st hd3 hd4 hk3 (sched_in hp hI.wr hI.gpr hK))
    fun st' ⟨hx, hm, hg, hrd, hwr, hxo⟩ => ?_
  have v0 : W s₀.mem (kp s₀) nk (a + nk) =
      W s₀.mem (kp s₀) nk (a + 0) ^^^ temp32 nk (a + nk) (W s₀.mem (kp s₀) nk (a + nk - 1)) := by
    rw [W_ge h0 (by omega_arith), Nat.add_sub_cancel, Nat.add_zero]
  have vj : ∀ j, 0 < j → j < 4 → W s₀.mem (kp s₀) nk (a + nk + j) =
      W s₀.mem (kp s₀) nk (a + j) ^^^ W s₀.mem (kp s₀) nk (a + nk + (j - 1)) := fun j h1 h2 => by
    rw [W_plain h0 (by omega_arith) (hres j h1 h2), show a + nk + j - nk = a + j by omega_arith,
      show a + nk + j - 1 = a + nk + (j - 1) by omega_arith]
  have v1 := vj 1 (by omega_arith) (by omega_arith)
  have v2 := vj 2 (by omega_arith) (by omega_arith)
  have v3 := vj 3 (by omega_arith) (by omega_arith)
  simp only [Nat.reduceSub, Nat.add_zero] at v1 v2 v3
  obtain ⟨e0, e1, e2, e3⟩ := dword_kv (st.xmm d) (genT (st.xmm s) sel rot (st.xmm k))
  have hv : ∀ j < 4, dword (kv (st.xmm d) (genT (st.xmm s) sel rot (st.xmm k))) j =
      W s₀.mem (kp s₀) nk (a + nk + j) := by
    intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · show _ = W s₀.mem (kp s₀) nk (a + nk)
      rw [e0, hA 0 (by omega_arith), hT 0 (by omega_arith), v0]
    · rw [e1, hA 1 (by omega_arith), hA 0 (by omega_arith), hT 1 (by omega_arith), v1, v0]
    · rw [e2, hA 2 (by omega_arith), hA 1 (by omega_arith), hA 0 (by omega_arith), hT 2 (by omega_arith), v2, v1, v0]
    · rw [e3, hA 3 (by omega_arith), hA 2 (by omega_arith), hA 1 (by omega_arith), hA 0 (by omega_arith), hT 3 (by omega_arith),
        v3, v2, v1, v0]
  refine ⟨⟨hg.trans hI.gpr, hrd.trans hI.rd, hwr.trans hI.wr, ?_, ?_⟩, fun j hj => by rw [hx]; exact hv j hj,
    hxo⟩
  · rw [hm, hI.gpr, ofInt_natCast]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (contains_offset hK (by omega_arith))
  · rw [hm, hI.gpr, ofInt_natCast]
    exact good_store hI.good _ (Nat.le_refl 4) hv hK

/-- `kstepB6`: from words `b − 6`, `b − 5` in `xmm2` and `b − 1` in `xmm1`'s
last doubleword, words `b`, `b + 1` in `xmm2`. -/
theorem kstepB6K {s₀ : State} (hp : Pre s₀) (c b off : Nat) (hc : c % 6 = 4) (hb : b = c + 6) (hoff : off = 4 * b)
    (hK : 4 * b + 16 ≤ 240) {st : State} (hI : KS s₀ 6 b st)
    (hB0 : dword (st.xmm .xmm2) 0 = W s₀.mem (kp s₀) 6 c)
    (hB1 : dword (st.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (c + 1))
    (hA3 : dword (st.xmm .xmm1) 3 = W s₀.mem (kp s₀) 6 (c + 5)) :
    WP isa (.block (kstepB6 off)) st fun st' => KS s₀ 6 (b + 2) st' ∧
      dword (st'.xmm .xmm2) 0 = W s₀.mem (kp s₀) 6 b ∧
      dword (st'.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (b + 1) ∧
      ∀ x, x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  subst hoff hb
  refine WP.mono (kstepB6_exec _ st (sched_in hp hI.wr hI.gpr hK))
    fun st' ⟨hx, hm, hg, hrd, hwr, hxo⟩ => ?_
  have v0 : W s₀.mem (kp s₀) 6 (c + 6) = W s₀.mem (kp s₀) 6 c ^^^ W s₀.mem (kp s₀) 6 (c + 5) := by
    rw [W_plain (by decide) (by omega_arith) (temp_plain (by omega_arith) (by omega_arith)),
      show c + 6 - 6 = c by omega_arith, show c + 6 - 1 = c + 5 by omega_arith]
  have v1 : W s₀.mem (kp s₀) 6 (c + 6 + 1) =
      W s₀.mem (kp s₀) 6 (c + 1) ^^^ W s₀.mem (kp s₀) 6 (c + 6) := by
    rw [W_plain (by decide) (by omega_arith) (temp_plain (by omega_arith) (by omega_arith)),
      show c + 6 + 1 - 6 = c + 1 by omega_arith, show c + 6 + 1 - 1 = c + 6 by omega_arith]
  obtain ⟨e0, e1⟩ := dword_kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)
  have t : ∀ j < 4, dword (shufDwords (st.xmm .xmm1) 0xff) j = W s₀.mem (kp s₀) 6 (c + 5) :=
    fun j hj => by rw [shuf_ff, dword_bcast _ hj, hA3]
  have hv : ∀ j < 2, dword (kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)) j =
      W s₀.mem (kp s₀) 6 (c + 6 + j) := by
    intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl
    · rw [e0, hB0, t 0 (by omega_arith), Nat.add_zero, v0]
    · rw [e1, hB1, hB0, t 1 (by omega_arith), v1, v0]
  refine ⟨⟨hg.trans hI.gpr, hrd.trans hI.rd, hwr.trans hI.wr, ?_, ?_⟩,
    by rw [hx]; exact hv 0 (by omega_arith), by rw [hx]; exact hv 1 (by omega_arith), hxo⟩
  · rw [hm, hI.gpr, ofInt_natCast]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (contains_offset hK (by omega_arith))
  · rw [hm, hI.gpr, ofInt_natCast]
    exact good_store hI.good _ (by decide) hv hK

/-! ## The round constants -/

open VG.Impl.Aes.X86_64.AesNi (rcReg rcons rcons128)

theorem rcReg_ne (j : Nat) :
    rcReg j ≠ .xmm1 ∧ rcReg j ≠ .xmm2 ∧ rcReg j ≠ .xmm3 ∧ rcReg j ≠ .xmm4 ∧ rcReg j ≠ .xmm15 := by
  unfold rcReg; split <;> decide

/-- `rcReg j` holds `Rcon[j + 1]` in every doubleword, for each `j < n`. -/
def RC (n : Nat) (st : State) : Prop := ∀ j < n, st.xmm (rcReg j) = bc (rc (j + 1))

theorem RC.keep {n : Nat} {st st' : State} (h : RC n st) {d : XReg} (hd : d = .xmm1 ∨ d = .xmm2)
    (hx : ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x) : RC n st' := fun j hj => by
  obtain ⟨n1, n2, n3, n4, -⟩ := rcReg_ne j
  rw [hx _ (by rcases hd with rfl | rfl <;> with_reducible assumption) n3 n4]
  exact h j hj

theorem RC.frame {n : Nat} {rs : List XReg} {st st' : State} (h : RC n st) (hf : XFrame rs st st')
    (hrs : ∀ j < n, rcReg j ∉ rs) : RC n st' := fun j hj => by
  rw [hf.xmm _ (hrs j hj)]
  exact h j hj

theorem pcmpeqd_self (x : BitVec 128) :
    XBinOp.eval .pcmpeqd x x = ofDwords 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF := by
  simp only [XBinOp.eval, ↓reduceIte]

/-- The registers `rcons` writes. -/
abbrev rcRegs : List XReg := [.xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12]

theorem rcons_ok (st : State) : WP isa (.block rcons) st fun st' => XFrame rcRegs st st' ∧ RC 8 st' := by
  apply WP.of_runBlock
  simp only [rcons, show List.range 7 = [0, 1, 2, 3, 4, 5, 6] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, rcReg, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, Option.some.injEq, exists_eq_left', eval_movdqa]
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, fun j hj => ?_⟩
  · simp only [rcRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr, ite_false]
  · match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp only [rcReg, reduceCtorEq, ↓reduceIte, pcmpeqd_self] <;> decide

theorem rcons128_ok {st : State} (h : RC 8 st) :
    WP isa (.block rcons128) st fun st' => XFrame [.xmm13, .xmm14] st st' ∧ RC 10 st' := by
  apply WP.of_runBlock
  simp only [rcons128, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    Option.some.injEq, exists_eq_left', eval_movdqa]
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, fun j hj => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr, ite_false]
  · have h0 := h 0 (by omega_arith)
    have h1 := h 1 (by omega_arith)
    have h3 := h 3 (by omega_arith)
    have h4 := h 4 (by omega_arith)
    simp only [rcReg] at h0 h1 h3 h4
    rcases (by omega_arith : j < 8 ∨ j = 8 ∨ j = 9) with hj | rfl | rfl
    · obtain ⟨-, -, -, -, -⟩ := rcReg_ne j
      have e : rcReg j ≠ .xmm13 ∧ rcReg j ≠ .xmm14 := by
        rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [e.1, e.2, ite_false]
      exact h j hj
    · simp only [rcReg, reduceCtorEq, ↓reduceIte, h0, h1, h3, h4]
      decide
    · simp only [rcReg, reduceCtorEq, ↓reduceIte, h0, h1, h3, h4]
      decide

/-! ## AES-128 -/

/-- After `k` steps: words `0 … 4k + 3` stored, `4k … 4k + 3` in `xmm1`. -/
def Inv128 (s₀ : State) (k : Nat) (st : State) : Prop :=
  KS s₀ 4 (4 * k + 4) st ∧ (∀ j < 4, dword (st.xmm .xmm1) j = W s₀.mem (kp s₀) 4 (4 * k + j)) ∧ RC 10 st

theorem expand128_ok {s₀ : State} (hp : Pre s₀) (hl : len s₀ = 16) {rs : List XReg} {st : State}
    (hf : XFrame rs s₀ st) (hrc : RC 8 st) : WP isa (.block expand128) st (KS s₀ 4 44) := by
  simp only [expand128, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rcons128_ok hrc) fun (st₀ : State) ⟨hf₀, hrc₀⟩ => ?_
  have hf' := hf.comp hf₀
  rw [WP.block_append_iff]
  have hin := key_in hp (s := s₀) rfl rfl (off := 0) (by omega_arith)
  have hw := sched_in hp (s := s₀) rfl rfl (off := 0) (by omega_arith)
  refine WP.mono (Q := Inv128 s₀ 0) ?_ fun st₁ h₁ => WP.mono
    (wp_range_flatMap (Inv128 s₀) (fun k st hk h => ?_) 10 (Nat.le_refl _) st₁ h₁) fun _ h => h.1
  · apply WP.of_runBlock
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
      State.setXmm, State.load128, State.store128, ea_at, hf'.gpr, hf'.rd, hf'.wr, hf'.mem, hin, hw,
      Option.map_some, Option.some.injEq, exists_eq_left']
    have hv : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 4 (0 + j) := fun j hj => by
      rw [dword_key _ _ 0 j (0 + j) hj (by omega_arith), W_lt (by omega_arith)]
    obtain ⟨f₁, g₁⟩ := store_mem (Frame.refl _ _) (good_zero _ _ _) _ 0 rfl (Nat.le_refl 4) hv (by decide)
    exact ⟨⟨rfl, rfl, rfl, f₁, g₁.mono (by omega_arith)⟩, fun j hj => (hv j hj).trans (congrArg _ (by omega_arith)),
      fun j hj => by simp only [(rcReg_ne j).1, ite_false]; exact hrc₀ j hj⟩
  · refine WP.mono (kstepK hp (nk := 4) (by decide) .xmm1 .xmm1 0xff true (rcReg k) (4 * k) (4 * (k + 1)) _
      (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (rcReg_ne k).2.2.1 (h.1.of_eq (by omega_arith)) h.2.1
      (fun j hj => ?_) (fun j h1 h2 y => temp_plain (by omega_arith) (by omega_arith) y))
      fun st' ⟨hI', hA', hx'⟩ => ⟨hI'.of_eq (by omega_arith), hA', h.2.2.keep (Or.inl rfl) hx'⟩
    rw [h.2.2 k (by omega_arith), genT_rot _ _ 3 _ (shuf_ff _), dword_bcast _ hj, h.2.1 3 (by omega_arith),
      temp_rc (by omega_arith), show 4 * (k + 1) / 4 = k + 1 by omega_arith, show 4 * (k + 1) - 1 = 4 * k + 3 by omega_arith]

/-! ## AES-192 -/

/-- After `k` steps: words `0 … 6k + 5` stored, `6k … 6k + 3` in `xmm1`,
`6k + 4` and `6k + 5` in `xmm2`. -/
def Inv192 (s₀ : State) (k : Nat) (st : State) : Prop :=
  KS s₀ 6 (6 * k + 6) st ∧ (∀ j < 4, dword (st.xmm .xmm1) j = W s₀.mem (kp s₀) 6 (6 * k + j)) ∧
    dword (st.xmm .xmm2) 0 = W s₀.mem (kp s₀) 6 (6 * k + 4) ∧
    dword (st.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (6 * k + 5) ∧ RC 8 st

theorem hT55 {s₀ : State} {st : State} {b k : Nat} (hb : b = 6 * k + 6)
    (h : dword (st.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (b - 1)) (hr : st.xmm (rcReg k) = bc (rc (k + 1))) :
    ∀ j < 4, dword (genT (st.xmm .xmm2) 0x55 true (st.xmm (rcReg k))) j =
      temp32 6 b (W s₀.mem (kp s₀) 6 (b - 1)) := fun j hj => by
  rw [hr, genT_rot _ _ 1 _ (shuf_55 _), dword_bcast _ hj, h, temp_rc (by omega_arith), show b / 6 = k + 1 by omega_arith]

theorem expand192_ok {s₀ : State} (hp : Pre s₀) (hl : len s₀ = 24) {rs : List XReg} {st : State}
    (hf : XFrame rs s₀ st) (hrc : RC 8 st) : WP isa (.block expand192) st (KS s₀ 6 52) := by
  simp only [expand192, List.append_assoc]
  rw [WP.block_append_iff]
  have hin0 := key_in hp (s := s₀) rfl rfl (off := 0) (by omega_arith)
  have hin8 := key_in hp (s := s₀) rfl rfl (off := 8) (by omega_arith)
  have hw0 := sched_in hp (s := s₀) rfl rfl (off := 0) (by omega_arith)
  have hw16 := sched_in hp (s := s₀) rfl rfl (off := 16) (by omega_arith)
  refine WP.mono (Q := Inv192 s₀ 0) ?_ fun st₁ h₁ => WP.block_append_iff.mpr (WP.mono
    (wp_range_flatMap (Inv192 s₀) (fun k st hk h => ?_) 7 (Nat.le_refl _) st₁ h₁) fun st₂ h => ?_)
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, isa,
      XOp.exec, State.setXmm, State.load128, State.store128, ea_at, hf.gpr, hf.rd, hf.wr, hf.mem,
      hin0, hin8, hw0, hw16, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
    have hv : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 6 (0 + j) := fun j hj => by
      rw [dword_key _ _ 0 j (0 + j) hj (by omega_arith), W_lt (by omega_arith)]
    have hB : ∀ j < 2, dword (XShiftOp.eval .psrldq
        (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 128) 8) j =
        W s₀.mem (kp s₀) 6 (4 + j) := fun j hj => by
      obtain ⟨e0, e1⟩ := dword_shr64 (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 128)
      rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl
      · rw [e0, dword_key _ _ 8 2 4 (by omega_arith) (by omega_arith), W_lt (by omega_arith)]
      · rw [e1, dword_key _ _ 8 3 5 (by omega_arith) (by omega_arith), W_lt (by omega_arith)]
    obtain ⟨f₁, g₁⟩ := store_mem (Frame.refl _ _) (good_zero _ _ _) _ 0 rfl (Nat.le_refl 4) hv (by decide)
    obtain ⟨f₂, g₂⟩ := store_mem f₁ g₁ _ 16 rfl (by decide) hB (by decide)
    exact ⟨⟨rfl, rfl, rfl, f₂, g₂.mono (by omega_arith)⟩, fun j hj => (hv j hj).trans (congrArg _ (by omega_arith)),
      hB 0 (by omega_arith), hB 1 (by omega_arith),
      fun j hj => by simp only [(rcReg_ne j).1, (rcReg_ne j).2.1, ite_false]; exact hrc j hj⟩
  · rw [WP.block_append_iff]
    refine WP.mono (kstepK hp (nk := 6) (by decide) .xmm1 .xmm2 0x55 true (rcReg k) (6 * k) (6 * k + 6) _
      (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (rcReg_ne k).2.2.1 h.1 h.2.1
      (hT55 rfl (h.2.2.2.1.trans (congrArg _ (by omega_arith))) (h.2.2.2.2 k (by omega_arith)))
      (fun j h1 h2 y => temp_plain (by omega_arith) (by omega_arith) y)) fun st₁ ⟨hI₁, hA₁, hx₁⟩ => ?_
    have hx2 := hx₁ .xmm2 (by decide) (by decide) (by decide)
    have hrc₁ := h.2.2.2.2.keep (Or.inl rfl) hx₁
    refine WP.mono (kstepB6K hp (6 * k + 4) (6 * k + 6 + 4) _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      hI₁ (by rw [hx2]; exact h.2.2.1) (by rw [hx2]; exact h.2.2.2.1.trans (congrArg _ (by omega_arith)))
      ((hA₁ 3 (by omega_arith)).trans (congrArg _ (by omega_arith)))) fun st₂ ⟨hI₂, hb0, hb1, hx₂⟩ =>
      ⟨hI₂.of_eq (by omega_arith), fun j hj => ?_, hb0.trans (congrArg _ (by omega_arith)),
        hb1.trans (congrArg _ (by omega_arith)), hrc₁.keep (Or.inr rfl) hx₂⟩
    rw [hx₂ .xmm1 (by decide) (by decide) (by decide)]
    exact (hA₁ j hj).trans (congrArg _ (by omega_arith))
  · refine WP.mono (kstepK hp (nk := 6) (by decide) .xmm1 .xmm2 0x55 true (rcReg 7) (6 * 7) (6 * 7 + 6) 192
      (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (rcReg_ne 7).2.2.1 h.1 h.2.1
      (hT55 (k := 7) rfl (h.2.2.2.1.trans (congrArg _ (by omega_arith))) (h.2.2.2.2 7 (by omega_arith)))
      (fun j h1 h2 y => temp_plain (by omega_arith) (by omega_arith) y)) fun st' ⟨hI', _, _⟩ => hI'.of_eq (by omega_arith)

/-! ## AES-256 -/

/-- After `k` steps: words `0 … 8k + 7` stored, `8k … 8k + 3` in `xmm1`,
`8k + 4 … 8k + 7` in `xmm2`. -/
def Inv256 (s₀ : State) (k : Nat) (st : State) : Prop :=
  KS s₀ 8 (8 * k + 8) st ∧ (∀ j < 4, dword (st.xmm .xmm1) j = W s₀.mem (kp s₀) 8 (8 * k + j)) ∧
    (∀ j < 4, dword (st.xmm .xmm2) j = W s₀.mem (kp s₀) 8 (8 * k + 4 + j)) ∧ RC 7 st ∧ st.xmm .xmm15 = 0

theorem hTff {s₀ : State} {st : State} {b k : Nat} (hb : b = 8 * k + 8)
    (h : dword (st.xmm .xmm2) 3 = W s₀.mem (kp s₀) 8 (b - 1)) (hr : st.xmm (rcReg k) = bc (rc (k + 1))) :
    ∀ j < 4, dword (genT (st.xmm .xmm2) 0xff true (st.xmm (rcReg k))) j =
      temp32 8 b (W s₀.mem (kp s₀) 8 (b - 1)) := fun j hj => by
  rw [hr, genT_rot _ _ 3 _ (shuf_ff _), dword_bcast _ hj, h, temp_rc (by omega_arith), show b / 8 = k + 1 by omega_arith]

theorem expand256_ok {s₀ : State} (hp : Pre s₀) (hl : len s₀ = 32) {rs : List XReg} {st : State}
    (hf : XFrame rs s₀ st) (hrc : RC 8 st) : WP isa (.block expand256) st (KS s₀ 8 60) := by
  simp only [expand256, List.append_assoc]
  rw [WP.block_append_iff]
  have hin0 := key_in hp (s := s₀) rfl rfl (off := 0) (by omega_arith)
  have hin16 := key_in hp (s := s₀) rfl rfl (off := 16) (by omega_arith)
  have hw0 := sched_in hp (s := s₀) rfl rfl (off := 0) (by omega_arith)
  have hw16 := sched_in hp (s := s₀) rfl rfl (off := 16) (by omega_arith)
  refine WP.mono (Q := Inv256 s₀ 0) ?_ fun st₁ h₁ => WP.block_append_iff.mpr (WP.mono
    (wp_range_flatMap (Inv256 s₀) (fun k st hk h => ?_) 6 (Nat.le_refl _) st₁ h₁) fun st₂ h => ?_)
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, isa,
      XOp.exec, State.setXmm, State.load128, State.store128, ea_at, hf.gpr, hf.rd, hf.wr, hf.mem, hin0, hin16,
      hw0, hw16, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left', eval_pxor',
      BitVec.xor_self]
    have hv : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 8 (0 + j) := fun j hj => by
      rw [dword_key _ _ 0 j (0 + j) hj (by omega_arith), W_lt (by omega_arith)]
    have hB : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((16 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 8 (4 + j) := fun j hj => by
      rw [dword_key _ _ 16 j (4 + j) hj (by omega_arith), W_lt (by omega_arith)]
    obtain ⟨f₁, g₁⟩ := store_mem (Frame.refl _ _) (good_zero _ _ _) _ 0 rfl (Nat.le_refl 4) hv (by decide)
    obtain ⟨f₂, g₂⟩ := store_mem f₁ g₁ _ 16 rfl (Nat.le_refl 4) hB (by decide)
    exact ⟨⟨rfl, rfl, rfl, f₂, g₂.mono (by omega_arith)⟩, fun j hj => (hv j hj).trans (congrArg _ (by omega_arith)),
      fun j hj => (hB j hj).trans (congrArg _ (by omega_arith)),
      fun j hj => by
        simp only [(rcReg_ne j).1, (rcReg_ne j).2.1, (rcReg_ne j).2.2.2.2, ite_false]; exact hrc j (by omega_arith),
      rfl⟩
  · rw [WP.block_append_iff]
    refine WP.mono (kstepK hp (nk := 8) (by decide) .xmm1 .xmm2 0xff true (rcReg k) (8 * k) (8 * k + 8) _
      (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (rcReg_ne k).2.2.1 h.1 h.2.1
      (hTff rfl ((h.2.2.1 3 (by omega_arith)).trans (congrArg _ (by omega_arith))) (h.2.2.2.1 k (by omega_arith)))
      (fun j h1 h2 y => temp_plain (by omega_arith) (by omega_arith) y)) fun st₁ ⟨hI₁, hA₁, hx₁⟩ => ?_
    have hx2 := hx₁ .xmm2 (by decide) (by decide) (by decide)
    have hz₁ : st₁.xmm .xmm15 = 0 := by rw [hx₁ .xmm15 (by decide) (by decide) (by decide)]; exact h.2.2.2.2
    have hrc₁ := h.2.2.2.1.keep (Or.inl rfl) hx₁
    refine WP.mono (kstepK hp (nk := 8) (by decide) .xmm2 .xmm1 0xff false .xmm15 (8 * k + 4) (8 * k + 8 + 4) _
      (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) hI₁
      (fun j hj => by rw [hx2]; exact h.2.2.1 j hj)
      (fun j hj => by
        rw [hz₁, genT_sub, dword_bcast _ hj, hA₁ 3 (by omega_arith), temp_sub (by omega_arith) (by omega_arith),
          show 8 * k + 8 + 4 - 1 = 8 * k + 8 + 3 by omega_arith])
      (fun j h1 h2 y => temp_plain (by omega_arith) (by omega_arith) y)) fun st₂ ⟨hI₂, hA₂, hx₂⟩ =>
      ⟨hI₂.of_eq (by omega_arith), fun j hj => ?_, fun j hj => (hA₂ j hj).trans (congrArg _ (by omega_arith)),
        hrc₁.keep (Or.inr rfl) hx₂, by rw [hx₂ .xmm15 (by decide) (by decide) (by decide)]; exact hz₁⟩
    rw [hx₂ .xmm1 (by decide) (by decide) (by decide)]
    exact (hA₁ j hj).trans (congrArg _ (by omega_arith))
  · refine WP.mono (kstepK hp (nk := 8) (by decide) .xmm1 .xmm2 0xff true (rcReg 6) (8 * 6) (8 * 6 + 8) 224
      (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (rcReg_ne 6).2.2.1 h.1 h.2.1
      (hTff (k := 6) rfl ((h.2.2.1 3 (by omega_arith)).trans (congrArg _ (by omega_arith))) (h.2.2.2.1 6 (by omega_arith)))
      (fun j h1 h2 y => temp_plain (by omega_arith) (by omega_arith) y)) fun st' ⟨hI', _, _⟩ => hI'.of_eq (by omega_arith)

/-! ## The whole function -/

theorem fin {s₀ : State} (hp : Pre s₀) {nk : Nat} (h0 : 0 < nk) (hl : len s₀ = 4 * nk) {st : State}
    (hI : KS s₀ nk (4 * (nk + 7)) st) : gprPreserved s₀ st ∧ expandKeyX86_64.post s₀ st := by
  refine ⟨⟨fun r _ => by rw [hI.gpr], hI.frame.readW (Region.contains_self _ _)
    (by simpa using hp.ret) (by decide)⟩, ?_⟩
  have hl' : (s₀.gpr .rsi).toNat = 4 * nk := hl
  show Spec.Aes.bytesAt st.mem (sp s₀) (16 * (Spec.Aes.rounds ((s₀.gpr .rsi).toNat / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (kp s₀) (s₀.gpr .rsi).toNat)
  rw [hl', show 4 * nk / 4 = nk by omega_arith, expandKey_eq s₀.mem _ h0, Spec.Aes.rounds,
    show 16 * (nk + 6 + 1) = 4 * (4 * (nk + 6 + 1)) by omega_arith]
  exact bytesAt_eq st.mem _ _ _ fun i hi => hI.good i (by omega_arith)

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa expandKey s₀ fun s' => gprPreserved s₀ s' ∧ expandKeyX86_64.post s₀ s' := by
  have hrsi : s₀.gpr .rsi = BitVec.ofNat 64 (len s₀) := by simp [len]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (rcons_ok s₀) fun (s₀' : State) ⟨hfa, hrca⟩ =>
    WP.mono (cmpRsi_ok s₀' 24 (len s₀) (by rw [hfa.gpr]; exact hrsi)) fun (s₁ : State) ⟨hz₁, hfb⟩ => ?_))
  have hf₁ := hfa.comp hfb
  have hrc₁ := hrca.frame hfb fun _ _ h => by cases h
  refine WP.ite (decide (len s₀ = 24)) (by
    rw [show isa.eval .e s₁ = s₁.zf from rfl, hz₁]
    rcases hp.len with h | h | h <;> rw [h] <;> decide) (fun h => ?_) (fun h => ?_)
  · have h24 : len s₀ = 24 := by simpa using h
    exact WP.mono (expand192_ok hp h24 hf₁ hrc₁) fun _ hI => fin hp (nk := 6) (by decide) h24 hI
  · refine WP.seq (WP.mono (cmpRsi_ok s₁ 32 (len s₀) (by rw [hf₁.gpr]; exact hrsi)) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
    have hf := hf₁.comp hf₂
    have hrc₂ := hrc₁.frame hf₂ fun _ _ h => by cases h
    refine WP.ite (decide (len s₀ = 32)) (by
      rw [show isa.eval .e s₂ = s₂.zf from rfl, hz₂]
      rcases hp.len with h | h | h <;> rw [h] <;> decide) (fun h' => ?_) (fun h' => ?_)
    · have h32 : len s₀ = 32 := by simpa using h'
      exact WP.mono (expand256_ok hp h32 hf hrc₂) fun _ hI => fin hp (nk := 8) (by decide) h32 hI
    · have h16 : len s₀ = 16 := by
        simp only [decide_eq_false_iff_not] at h h'; rcases hp.len with e | e | e <;> omega_arith
      exact WP.mono (expand128_ok hp h16 hf hrc₂) fun _ hI => fin hp (nk := 4) (by decide) h16 hI

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : expandKeyX86_64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem expandKey_ct : ConstantTime isa expandKeyX86_64.pre expandKeyX86_64.pub expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.expandKey (Spec.Aes.expandKeyScratchContract X86_64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Aes.expandKeyScratchContract, Spec.Aes.expandKeyScratchSig,
      Proof.Aes.X86_64.AesNi.expandKeyX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Aes.X86_64.AesNi.Key.satState] using Proof.Aes.X86_64.AesNi.Key.satState)

end VG.Proof.Aes.X86_64.AesNi.Key
