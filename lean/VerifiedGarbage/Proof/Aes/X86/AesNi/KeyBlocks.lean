import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Impl.Aes.X86.AesNi
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Aes.X86.ExpandKey

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Arith`. -/
section

section

/-!
# AES-NI: the instructions are FIPS 197's rounds

Untrusted: everything here is checked by Lean. An SSE register holds an
AES state as its 16 bytes in memory order (`st`): byte `r + 4c` is
`s[r, c]`, as FIPS 197 §3.4 lays the state out and as the SDM's AES
instructions read it. On such registers `pxor`, `aesenc` and `aesenclast`
are `AddRoundKey`, a full round and the last round of `Spec.Aes.cipher`
(`pxor_st`, `aesenc_st`, `aesenclast_st`); the S-box of the ISA model,
computed by repeated squaring, is the one of `Spec/Aes.lean` (`sbox_eq`).
-/

namespace VG.Proof.Aes.X86.AesNi

open VG.X86
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey sbox roundKey cipher bytesAt)

/-! ## GF(2⁸) -/

theorem mul_eq : aesMul = Spec.Aes.mul := rfl

/-- Both square and multiply `b²`, `b⁴`, …, `b¹²⁸` in the same order: unfolded
to the same term (no evaluation left for the kernel). -/
theorem inv_eq (b : BitVec 8) : aesInv b = Spec.Aes.inv b := by
  simp (config := {decide := true}) only [aesInv, Spec.Aes.inv, Spec.Aes.pow, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, VG.Proof.Aes.X86.AesNi.mul_eq,
    ite_true, ite_false]

theorem sbox_eq : aesSbox = VG.Spec.Aes.sbox := by
  funext b
  simp only [aesSbox, VG.Spec.Aes.sbox, VG.Proof.Aes.X86.AesNi.inv_eq, ofBits8]

theorem mul_one' : ∀ b : BitVec 8, Spec.Aes.mul 1 b = b := by decide +kernel

/-! ## States in registers -/

/-- The AES state held by a register. -/
def st (v : BitVec 128) : Spec.Aes.State := Vector.ofFn fun i => byte v i

theorem getD_ofFn {f : Fin 16 → Byte} {i : Nat} (h : i < 16) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

theorem getD_st (v : BitVec 128) {i : Nat} (h : i < 16) : (VG.Proof.Aes.X86.AesNi.st v).getD i 0 = byte v i := by
  rw [VG.Proof.Aes.X86.AesNi.st, VG.Proof.Aes.X86.AesNi.getD_ofFn h]

theorem st_ext {s t : Spec.Aes.State} (h : ∀ i < 16, s.getD i 0 = t.getD i 0) : s = t := by
  apply Vector.ext; intro i hi
  have := h i hi
  simpa [Vector.getD, hi] using this

theorem st_inj {a b : BitVec 128} (h : VG.Proof.Aes.X86.AesNi.st a = VG.Proof.Aes.X86.AesNi.st b) : a = b :=
  VG.Proof.Gcm.X86.ext_byte fun i hi => by rw [← VG.Proof.Aes.X86.AesNi.getD_st a hi, ← VG.Proof.Aes.X86.AesNi.getD_st b hi, h]

theorem byte_xor (a b : BitVec 128) (i : Nat) : byte (a ^^^ b) i = byte a i ^^^ byte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

/-! ## FIPS 197's transformations, byte by byte -/

theorem getD_addRoundKey (s : Spec.Aes.State) (rk : List Byte) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.addRoundKey s rk).getD i 0 = s.getD i 0 ^^^ rk.getD i 0 := by
  rw [VG.Spec.Aes.addRoundKey, VG.Proof.Aes.X86.AesNi.getD_ofFn h]

theorem getD_subBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (subBytes s).getD i 0 = VG.Spec.Aes.sbox (s.getD i 0) := by
  simp [subBytes, Vector.getD, h]

theorem getD_shiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.shiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [VG.Spec.Aes.shiftRows, VG.Proof.Aes.X86.AesNi.getD_ofFn h]

theorem getD_mixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.mixColumns s).getD i 0 =
      Spec.Aes.mul 0x02 (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x03 (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0 ^^^ s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0 := by
  rw [VG.Spec.Aes.mixColumns, VG.Proof.Aes.X86.AesNi.getD_ofFn h]

theorem byte_mapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMapBytes f x) i = f (byte x i) := by
  rw [aesMapBytes, VG.Proof.Gcm.X86.byte_ofBytes _ h]

theorem byte_shiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesShiftRows x) i = byte x (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  rw [aesShiftRows, VG.Proof.Gcm.X86.byte_ofBytes _ h]

theorem byte_mixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMixColumns x) i =
      aesMul 0x02 (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x03 (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesMixColumns, aesMixWith, VG.Proof.Gcm.X86.byte_ofBytes _ h]

/-! ## The instructions -/

/-- `pxor` with a round key is `AddRoundKey`. -/
theorem pxor_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .pxor v k) = VG.Spec.Aes.addRoundKey (VG.Proof.Aes.X86.AesNi.st v) rk := by
  apply VG.Proof.Aes.X86.AesNi.st_ext; intro i hi
  rw [VG.Proof.Aes.X86.AesNi.getD_st _ hi, VG.Proof.Aes.X86.AesNi.getD_addRoundKey _ _ hi, VG.Proof.Aes.X86.AesNi.getD_st _ hi, ← hk i hi]
  exact VG.Proof.Aes.X86.AesNi.byte_xor v k i

/-- `aesenc` is a round. -/
theorem aesenc_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .aesenc v k) = VG.Spec.Aes.addRoundKey (VG.Spec.Aes.mixColumns (VG.Spec.Aes.shiftRows (subBytes (VG.Proof.Aes.X86.AesNi.st v)))) rk := by
  apply VG.Proof.Aes.X86.AesNi.st_ext; intro i hi
  rw [VG.Proof.Aes.X86.AesNi.getD_st _ hi, VG.Proof.Aes.X86.AesNi.getD_addRoundKey _ _ hi, VG.Proof.Aes.X86.AesNi.getD_mixColumns _ hi, ← hk i hi]
  simp only [XBinOp.eval, VG.Proof.Aes.X86.AesNi.byte_xor]
  rw [VG.Proof.Aes.X86.AesNi.byte_mixColumns _ hi]
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [VG.Proof.Aes.X86.AesNi.byte_mapBytes _ _ (hr _), VG.Proof.Aes.X86.AesNi.getD_shiftRows _ (hr _), VG.Proof.Aes.X86.AesNi.byte_shiftRows _ (hr _), VG.Proof.Aes.X86.AesNi.sbox_eq,
    VG.Proof.Aes.X86.AesNi.mul_eq, VG.Proof.Aes.X86.AesNi.mul_one', VG.Proof.Aes.X86.AesNi.getD_subBytes _ (hs _), VG.Proof.Aes.X86.AesNi.getD_st _ (hs _)]

/-- `aesenclast` is the last round. -/
theorem aesenclast_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .aesenclast v k) = VG.Spec.Aes.addRoundKey (VG.Spec.Aes.shiftRows (subBytes (VG.Proof.Aes.X86.AesNi.st v))) rk := by
  apply VG.Proof.Aes.X86.AesNi.st_ext; intro i hi
  rw [VG.Proof.Aes.X86.AesNi.getD_st _ hi, VG.Proof.Aes.X86.AesNi.getD_addRoundKey _ _ hi, ← hk i hi]
  simp only [XBinOp.eval, VG.Proof.Aes.X86.AesNi.byte_xor]
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [VG.Proof.Aes.X86.AesNi.byte_mapBytes _ _ hi, VG.Proof.Aes.X86.AesNi.getD_shiftRows _ hi, VG.Proof.Aes.X86.AesNi.byte_shiftRows _ hi, VG.Proof.Aes.X86.AesNi.sbox_eq,
    VG.Proof.Aes.X86.AesNi.getD_subBytes _ (hs _), VG.Proof.Aes.X86.AesNi.getD_st _ (hs _)]

/-! ## The cipher -/

/-- The state after `AddRoundKey` and `k` full rounds. -/
def rnds (w : List Byte) (x : Spec.Aes.State) (k : Nat) : Spec.Aes.State :=
  (List.range k).foldl
    (fun s j => VG.Spec.Aes.addRoundKey (VG.Spec.Aes.mixColumns (VG.Spec.Aes.shiftRows (subBytes s))) (roundKey w (j + 1)))
    (VG.Spec.Aes.addRoundKey x (roundKey w 0))

theorem rnds_zero (w : List Byte) (x : Spec.Aes.State) :
    VG.Proof.Aes.X86.AesNi.rnds w x 0 = VG.Spec.Aes.addRoundKey x (roundKey w 0) := rfl

theorem rnds_succ (w : List Byte) (x : Spec.Aes.State) (k : Nat) :
    VG.Proof.Aes.X86.AesNi.rnds w x (k + 1) =
      VG.Spec.Aes.addRoundKey (VG.Spec.Aes.mixColumns (VG.Spec.Aes.shiftRows (subBytes (VG.Proof.Aes.X86.AesNi.rnds w x k)))) (roundKey w (k + 1)) := by
  simp only [VG.Proof.Aes.X86.AesNi.rnds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem cipher_eq (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher nr w x = VG.Spec.Aes.addRoundKey (VG.Spec.Aes.shiftRows (subBytes (VG.Proof.Aes.X86.AesNi.rnds w x (nr - 1)))) (roundKey w nr) := rfl

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem roundKey_getD (m : Mem) (p : Addr) {L j i : Nat} (hi : i < 16) (hj : 16 * j + 16 ≤ L) :
    (roundKey (VG.Spec.Aes.bytesAt m p L) j).getD i 0 = m (p + BitVec.ofNat 64 (16 * j + i)) := by
  simp [roundKey, VG.Spec.Aes.bytesAt, List.getD, hi, show 16 * j + i < L by omega]

/-- Round key `j`, loaded from the schedule. -/
theorem byte_roundKey (m : Mem) (p : Addr) {L j : Nat} (hj : 16 * j + 16 ≤ L) :
    ∀ i < 16, byte (m.readW (p + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128) i =
      (roundKey (VG.Spec.Aes.bytesAt m p L) j).getD i 0 := by
  intro i hi
  rw [VG.Proof.Gcm.X86.byte_readW _ _ hi, VG.Proof.Aes.X86.AesNi.roundKey_getD _ _ hi hj, VG.Proof.Aes.X86.AesNi.ofInt_natCast,
    BitVec.add_assoc, BitVec.ofNat_add]

theorem st_toList (r : BitVec 128) : (VG.Proof.Aes.X86.AesNi.st r).toList = (List.range 16).map (byte r) := by
  apply List.ext_getElem <;> simp [VG.Proof.Aes.X86.AesNi.st]

/-- `CIPH_K` of a block, as `Spec.Gcm.aesWith` states it, from the register
`r` that encrypting the block's bytes left. -/
theorem aesWith_eq (nr : Nat) (w : List Byte) (x r : BitVec 128)
    (h : VG.Proof.Aes.X86.AesNi.st r = cipher nr w (VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86.revMask))) :
    Spec.Gcm.aesWith nr w x = XBinOp.eval .pshufb r VG.Proof.Gcm.X86.revMask := by
  have e : (Vector.ofFn fun i => (Spec.Gcm.toBytes x).getD i 0) =
      VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86.revMask) := by
    apply VG.Proof.Aes.X86.AesNi.st_ext; intro i hi
    rw [VG.Proof.Aes.X86.AesNi.getD_ofFn hi, VG.Proof.Aes.X86.AesNi.getD_st _ hi, VG.Proof.Gcm.X86.byte_pshufb_rev _ hi]
    simp [Spec.Gcm.toBytes, List.getD, hi, byte]
  rw [Spec.Gcm.aesWith, e, ← h, VG.Proof.Aes.X86.AesNi.st_toList, VG.Proof.Gcm.X86.gcmOfBytes_eq,
    VG.Proof.Gcm.X86.pshufb_rev]

end VG.Proof.Aes.X86.AesNi

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Counters`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (ctrs)

/-- The byte-order numeric counter word occupies the last memory dword;
the cached prefix has that dword zero. -/
def counterLane (c : BitVec 32) (pfx : BitVec 128) : BitVec 128 :=
  XBinOp.eval .por (XShiftOp.eval .pslldq ((0 : BitVec 96) ++ bswap c) 12) pfx

/-- Inserting the byte-swapped low word preserves all 96 prefix bits. -/
theorem counterLane_eq (c : BitVec 32) (pfx : BitVec 96) :
    VG.Proof.Aes.X86.AesNi.counterLane c ((0 : BitVec 32) ++ pfx) = bswap c ++ pfx := by
  change ((((0 : BitVec 96) ++ bswap c) <<< 96) ||| ((0 : BitVec 32) ++ pfx)) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h : i < 96 <;> simp [h, BitVec.ofNat_eq_ofNat]
  simp [show i - 96 < 32 by omega, show i < 128 by omega]

/-- The two byte shifts cache exactly the first twelve memory bytes. -/
theorem cache_prefix (v : BitVec 128) :
    XShiftOp.eval .psrldq (XShiftOp.eval .pslldq v 4) 4 =
      (0 : BitVec 32) ++ v.extractLsb' 0 96 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change ((v <<< 32) >>> 32).getLsbD i = _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split <;> simp_all <;> omega

/-- Counter-lane bytes follow GCM's big-endian low word. -/
theorem counterLane_byte (c : BitVec 32) (pfx : BitVec 96) {i : Nat} (hi : i < 16) :
    byte (VG.Proof.Aes.X86.AesNi.counterLane c ((0 : BitVec 32) ++ pfx)) i =
      if i < 12 then pfx.extractLsb' (8 * i) 8
      else c.extractLsb' (8 * (15 - i)) 8 := by
  rw [VG.Proof.Aes.X86.AesNi.counterLane_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : i < 12
  · simp [h, show 8 * i + r < 96 by omega, hr]
  · simp only [h, ite_false, show ¬8 * i + r < 96 by omega, ite_false]
    rw [show 8 * i + r - 96 = 8 * (i - 12) + r by omega,
      getLsbD_bswap_block c (by omega : i - 12 < 4) hr]
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
    rcases (by omega : i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with h | h | h | h <;>
      subst i <;> simp

/-- A lane is exactly the AES state of the specified incremented GCM counter. -/
theorem counterLane_state (x : Spec.Gcm.Block) (pfx : BitVec 96) (i : Nat)
    (hpfx : ∀ k < 12, pfx.extractLsb' (8 * k) 8 = (Spec.Gcm.toBytes x).getD k 0) :
    VG.Proof.Aes.X86.AesNi.st (VG.Proof.Aes.X86.AesNi.counterLane (x.extractLsb' 0 32 + BitVec.ofNat 32 i) ((0 : BitVec 32) ++ pfx)) =
      VG.Proof.Aes.ctrState x i := by
  apply VG.Proof.Aes.X86.AesNi.st_ext
  intro k hk
  rw [VG.Proof.Aes.X86.AesNi.getD_st _ hk, VG.Proof.Aes.X86.AesNi.counterLane_byte _ _ hk]
  rw [VG.Proof.Aes.ctrState, VG.Proof.Aes.X86.AesNi.getD_ofFn hk]
  rw [VG.Proof.Aes.ctrBlock_byte x i hk]
  split
  · exact hpfx k (by assumption)
  · rfl

theorem ctrState_rev (x : Spec.Gcm.Block) (i : Nat) :
    VG.Proof.Aes.ctrState x i = VG.Proof.Aes.X86.AesNi.st (XBinOp.eval .pshufb
      (Nat.repeat Spec.Gcm.inc32 i x) VG.Proof.Gcm.X86.revMask) := by
  apply VG.Proof.Aes.X86.AesNi.st_ext
  intro k hk
  rw [VG.Proof.Aes.ctrState, VG.Proof.Aes.X86.AesNi.getD_ofFn hk, VG.Proof.Aes.X86.AesNi.getD_st _ hk,
    VG.Proof.Gcm.X86.byte_pshufb_rev _ hk, VG.Proof.Aes.toBytes_getD _ hk]
  rfl

/-- The cached memory prefix has the standard's first twelve bytes. -/
theorem memory_prefix (m : Mem) (p : Addr) {k : Nat} (hk : k < 12) :
    ((m.readW p 128).extractLsb' 0 96).extractLsb' (8 * k) 8 =
      (Spec.Gcm.toBytes (Spec.Gcm.blockAt m p)).getD k 0 := by
  rw [VG.Proof.Aes.toBytes_blockAt m p (by omega),
    ← VG.Proof.Gcm.X86.byte_readW m p (by omega : k < 16)]
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  simp [show 8 * k + r < 96 by omega]

theorem counter_one (b : XReg) (s : State) (hb : b ≠ .xmm7) :
    WP isa (.block (ctrs [b])) s fun s' =>
      s'.xmm b = VG.Proof.Aes.X86.AesNi.counterLane (s.gpr .ebx) (s.xmm .xmm7) ∧
      s'.gpr .ebx = s.gpr .ebx + 1 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [ctrs, List.append_nil]
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, VG.X86.readSrc, XOp.exec, execAlu, VG.Proof.Aes.X86.AesNi.counterLane, gpr_setReg,
    gpr_setXmm, xmm_setReg, xmm_setXmm, xmm_arithFlags, mem_setReg, rd_setReg,
    wr_setReg, Ne.symm hb, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · intro r heax hebx
    simp only [hebx, ite_false, gpr_arithFlags, gpr_setXmm, gpr_setReg, heax]
  · simp only [mem_arithFlags, mem_setXmm, mem_setReg]
  · simp only [rd_arithFlags, rd_setXmm, rd_setReg]
  · simp only [wr_arithFlags, wr_setXmm, wr_setReg]
  · intro r hr
    simp only [hr, ite_false]

structure CounterFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem CounterFrame.refl (rs : List XReg) (s : State) : VG.Proof.Aes.X86.AesNi.CounterFrame rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem CounterFrame.comp {rs rs' : List XReg} {s s' s'' : State}
    (h : VG.Proof.Aes.X86.AesNi.CounterFrame rs s s') (h' : VG.Proof.Aes.X86.AesNi.CounterFrame rs' s' s'') :
    VG.Proof.Aes.X86.AesNi.CounterFrame (rs ++ rs') s s'' :=
  ⟨fun r h1 h2 => (h'.gpr r h1 h2).trans (h.gpr r h1 h2),
    h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem CounterFrame.mono {rs rs' : List XReg} {s s' : State}
    (h : VG.Proof.Aes.X86.AesNi.CounterFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Aes.X86.AesNi.CounterFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

theorem add_one_index (c : BitVec 32) (k : Nat) :
    c + 1 + BitVec.ofNat 32 k = c + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (1 : BitVec 32)]
  rfl

theorem counters_ok (regs : List XReg) (s : State) (hnd : regs.Nodup)
    (h7 : .xmm7 ∉ regs) :
    WP isa (.block (ctrs regs)) s fun s' =>
      (∀ k (h : k < regs.length), s'.xmm regs[k] =
        VG.Proof.Aes.X86.AesNi.counterLane (s.gpr .ebx + BitVec.ofNat 32 k) (s.xmm .xmm7)) ∧
      s'.gpr .ebx = s.gpr .ebx + BitVec.ofNat 32 regs.length ∧
      VG.Proof.Aes.X86.AesNi.CounterFrame regs s s' := by
  induction regs generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h (by simp),
      (BitVec.add_zero _).symm, CounterFrame.refl _ _⟩
  | cons b bs ih =>
    have hb7 : b ≠ .xmm7 := fun h => h7 (h ▸ List.mem_cons_self ..)
    have hb : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86.AesNi.counter_one b s hb7) fun s₁ ⟨hv₁, hc₁, hg₁, hm₁, hr₁, hw₁, hx₁⟩ => ?_
    have hf₁ : VG.Proof.Aes.X86.AesNi.CounterFrame [b] s s₁ :=
      ⟨hg₁, hm₁, hr₁, hw₁, fun r hr => hx₁ r (by simpa using hr)⟩
    refine WP.mono (ih s₁ (List.nodup_cons.mp hnd).2
      (fun h => h7 (List.mem_cons_of_mem _ h))) fun s' ⟨hv, hc, hf⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, BitVec.add_zero]
        rw [hf.xmm b hb, hv₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hv k (by simpa using hk), hc₁, hx₁ .xmm7 (Ne.symm hb7), VG.Proof.Aes.X86.AesNi.add_one_index]
    · rw [hc, hc₁, VG.Proof.Aes.X86.AesNi.add_one_index, List.length_cons]
    · exact (hf₁.comp hf).mono (by simp)

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyArith`. -/
section

section

section

/-!
# AES key expansion as 32-bit words

Untrusted: everything here is checked by Lean. `W m kp nk i` is word `w[i]`
of the key schedule of the `nk`-word key at `kp`, as the 32-bit value whose
bytes, least significant first, are the word's bytes (`wv`), which is how a
doubleword of an SSE register holds it. `expandKey_eq`: FIPS 197's
`KEYEXPANSION` is these words, in order; `bytesAt_eq`: memory holding them
as little-endian doublewords holds the schedule.
-/

namespace VG.Proof.Aes.X86.AesNi

open VG.X86
open VG.Spec.Aes (Word subWord rotWord rcon xorWord expandWords expandKey bytesAt rounds)

/-- The bytes of a word, least significant first. -/
def wv (d : BitVec 32) : Word := (List.range 4).map fun j => d.extractLsb' (8 * j) 8

/-- `SUBWORD`, as `aeskeygenassist` computes it. -/
def sub32 (x : BitVec 32) : BitVec 32 :=
  aesSbox (x.extractLsb' 24 8) ++ aesSbox (x.extractLsb' 16 8) ++
    aesSbox (x.extractLsb' 8 8) ++ aesSbox (x.extractLsb' 0 8)

/-- `temp` of `KEYEXPANSION` for word `i`, from `w[i − 1]`. -/
def temp32 (nk i : Nat) (x : BitVec 32) : BitVec 32 :=
  if i % nk = 0 then (VG.Proof.Aes.X86.AesNi.sub32 x).rotateRight 8 ^^^ (Impl.Aes.X86.AesNi.rc (i / nk)).setWidth 32
  else if nk > 6 ∧ i % nk = 4 then VG.Proof.Aes.X86.AesNi.sub32 x else x

/-- Word `i` of the key schedule of the `nk`-word key at `kp`. -/
def W (m : Mem) (kp : Addr) (nk : Nat) (i : Nat) : BitVec 32 :=
  if i < nk ∨ nk = 0 then m.readW (kp + BitVec.ofNat 64 (4 * i)) 32
  else VG.Proof.Aes.X86.AesNi.W m kp nk (i - nk) ^^^ VG.Proof.Aes.X86.AesNi.temp32 nk i (VG.Proof.Aes.X86.AesNi.W m kp nk (i - 1))
termination_by i
decreasing_by all_goals omega

theorem W_lt {m : Mem} {kp : Addr} {nk i : Nat} (h : i < nk) :
    VG.Proof.Aes.X86.AesNi.W m kp nk i = m.readW (kp + BitVec.ofNat 64 (4 * i)) 32 := by
  rw [VG.Proof.Aes.X86.AesNi.W]; simp [h]

theorem W_ge {m : Mem} {kp : Addr} {nk i : Nat} (h0 : 0 < nk) (h : nk ≤ i) :
    VG.Proof.Aes.X86.AesNi.W m kp nk i = VG.Proof.Aes.X86.AesNi.W m kp nk (i - nk) ^^^ VG.Proof.Aes.X86.AesNi.temp32 nk i (VG.Proof.Aes.X86.AesNi.W m kp nk (i - 1)) := by
  rw [VG.Proof.Aes.X86.AesNi.W]; simp only [show ¬ (i < nk ∨ nk = 0) by omega, ite_false]

/-! ## Words and bytes -/

theorem wv_eq (d : BitVec 32) :
    VG.Proof.Aes.X86.AesNi.wv d = [d.extractLsb' 0 8, d.extractLsb' 8 8, d.extractLsb' 16 8, d.extractLsb' 24 8] := rfl

theorem extract_xor (a b : BitVec 32) (k : Nat) :
    (a ^^^ b).extractLsb' k 8 = a.extractLsb' k 8 ^^^ b.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem wv_xor (a b : BitVec 32) : VG.Proof.Aes.X86.AesNi.wv (a ^^^ b) = xorWord (VG.Proof.Aes.X86.AesNi.wv a) (VG.Proof.Aes.X86.AesNi.wv b) := by
  simp only [VG.Proof.Aes.X86.AesNi.wv_eq, VG.Proof.Aes.X86.AesNi.extract_xor, xorWord, List.zipWith_cons_cons, List.zipWith_nil_left]

theorem extract_cat (a b c d : BitVec 8) :
    (a ++ b ++ c ++ d).extractLsb' 0 8 = d ∧ (a ++ b ++ c ++ d).extractLsb' 8 8 = c ∧
      (a ++ b ++ c ++ d).extractLsb' 16 8 = b ∧ (a ++ b ++ c ++ d).extractLsb' 24 8 = a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp (disch := omega) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
      Bool.true_and, ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem rot_cat (a b c d : BitVec 8) : (a ++ b ++ c ++ d).rotateRight 8 = d ++ a ++ b ++ c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi' : i < 32 := hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, hi', decide_true, Bool.true_and]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem wv_cat (a b c d : BitVec 8) : VG.Proof.Aes.X86.AesNi.wv (a ++ b ++ c ++ d) = [d, c, b, a] := by
  obtain ⟨e0, e1, e2, e3⟩ := VG.Proof.Aes.X86.AesNi.extract_cat a b c d
  rw [VG.Proof.Aes.X86.AesNi.wv_eq, e0, e1, e2, e3]

theorem sub_wv (x : BitVec 32) : subWord (VG.Proof.Aes.X86.AesNi.wv x) = VG.Proof.Aes.X86.AesNi.wv (VG.Proof.Aes.X86.AesNi.sub32 x) := by
  rw [VG.Proof.Aes.X86.AesNi.sub32, VG.Proof.Aes.X86.AesNi.wv_cat, VG.Proof.Aes.X86.AesNi.wv_eq, subWord, VG.Proof.Aes.X86.AesNi.sbox_eq]; rfl

theorem subRot_wv (x : BitVec 32) : subWord (rotWord (VG.Proof.Aes.X86.AesNi.wv x)) = VG.Proof.Aes.X86.AesNi.wv ((VG.Proof.Aes.X86.AesNi.sub32 x).rotateRight 8) := by
  rw [VG.Proof.Aes.X86.AesNi.sub32, VG.Proof.Aes.X86.AesNi.rot_cat, VG.Proof.Aes.X86.AesNi.wv_cat, VG.Proof.Aes.X86.AesNi.wv_eq, rotWord, subWord, VG.Proof.Aes.X86.AesNi.sbox_eq]; rfl

theorem rcon_wv (j : Nat) : rcon j = VG.Proof.Aes.X86.AesNi.wv ((Impl.Aes.X86.AesNi.rc j).setWidth 32) := by
  rw [show (Impl.Aes.X86.AesNi.rc j).setWidth 32 = 0#8 ++ 0#8 ++ 0#8 ++ Impl.Aes.X86.AesNi.rc j by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_zero]
    by_cases h : i < 8
    · simp [h]; omega
    · simp [h]; exact fun _ => BitVec.getLsbD_of_ge _ _ (by omega), VG.Proof.Aes.X86.AesNi.wv_cat]
  rfl

theorem temp_wv (nk i : Nat) (x : BitVec 32) :
    (if i % nk = 0 then xorWord (subWord (rotWord (VG.Proof.Aes.X86.AesNi.wv x))) (rcon (i / nk))
      else if nk > 6 ∧ i % nk = 4 then subWord (VG.Proof.Aes.X86.AesNi.wv x) else VG.Proof.Aes.X86.AesNi.wv x) = VG.Proof.Aes.X86.AesNi.wv (VG.Proof.Aes.X86.AesNi.temp32 nk i x) := by
  unfold VG.Proof.Aes.X86.AesNi.temp32
  by_cases h1 : i % nk = 0
  · simp only [h1, ite_true, VG.Proof.Aes.X86.AesNi.wv_xor, VG.Proof.Aes.X86.AesNi.subRot_wv, VG.Proof.Aes.X86.AesNi.rcon_wv]
  · by_cases h2 : nk > 6 ∧ i % nk = 4
    · have h2' : (nk > 6 ∧ i % nk = 4) = True := eq_true h2
      simp only [h1, h2', ite_true, ite_false, VG.Proof.Aes.X86.AesNi.sub_wv]
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
    ((VG.Spec.Aes.bytesAt m kp L).drop (4 * i)).take 4 = VG.Proof.Aes.X86.AesNi.wv (m.readW (kp + BitVec.ofNat 64 (4 * i)) 32) := by
  apply List.ext_getElem
  · simp [VG.Spec.Aes.bytesAt, VG.Proof.Aes.X86.AesNi.wv]; omega
  · intro j h₁ h₂
    have hj : j < 4 := by simpa [VG.Proof.Aes.X86.AesNi.wv] using h₂
    simp only [List.getElem_take, List.getElem_drop, VG.Spec.Aes.bytesAt, List.getElem_map, List.getElem_range,
      VG.Proof.Aes.X86.AesNi.wv]
    rw [VG.Proof.Aes.X86.AesNi.ofNat_add', Mem.readW_byte m (kp + BitVec.ofNat 64 (4 * i)) hj]

theorem expandWords_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    ∀ n, expandWords (VG.Spec.Aes.bytesAt m kp (4 * nk)) nk n = (List.range n).map fun i => VG.Proof.Aes.X86.AesNi.wv (VG.Proof.Aes.X86.AesNi.W m kp nk i)
  | 0 => rfl
  | i + 1 => by
    rw [expandWords, VG.Proof.Aes.X86.AesNi.expandWords_eq m kp h0 i, List.range_succ, List.map_append, List.map_singleton]
    by_cases h : i < nk
    · simp only [h, ite_true]
      rw [VG.Proof.Aes.X86.AesNi.keyWord _ _ (by omega), VG.Proof.Aes.X86.AesNi.W_lt h]
    · simp only [h, ite_false]
      rw [VG.Proof.Aes.X86.AesNi.getD_mapRange _ _ (by omega), VG.Proof.Aes.X86.AesNi.getD_mapRange _ _ (by omega), VG.Proof.Aes.X86.AesNi.temp_wv, ← VG.Proof.Aes.X86.AesNi.wv_xor,
        ← VG.Proof.Aes.X86.AesNi.W_ge h0 (by omega)]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Aes.bytesAt m p n).length = n := by
  simp [VG.Spec.Aes.bytesAt]

/-- `KEYEXPANSION`, as words. -/
theorem expandKey_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    VG.Spec.Aes.expandKey (VG.Spec.Aes.bytesAt m kp (4 * nk)) =
      ((List.range (4 * (rounds nk + 1))).map fun i => VG.Proof.Aes.X86.AesNi.wv (VG.Proof.Aes.X86.AesNi.W m kp nk i)).flatten := by
  rw [VG.Spec.Aes.expandKey, VG.Proof.Aes.X86.AesNi.length_bytesAt, show 4 * nk / 4 = nk by omega, VG.Proof.Aes.X86.AesNi.expandWords_eq m kp h0]

/-- Memory holding the words `f 0 … f (K − 1)` as little-endian doublewords. -/
theorem bytesAt_eq (m : Mem) (p : Addr) (f : Nat → BitVec 32) :
    ∀ K, (∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i) →
      VG.Spec.Aes.bytesAt m p (4 * K) = ((List.range K).map fun i => VG.Proof.Aes.X86.AesNi.wv (f i)).flatten
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.map_append, List.flatten_append, ← VG.Proof.Aes.X86.AesNi.bytesAt_eq m p f K
      fun i hi => h i (by omega), List.map_singleton, List.flatten_singleton, ← h K (by omega),
      show 4 * (K + 1) = 4 * K + 4 by omega, VG.Spec.Aes.bytesAt, VG.Spec.Aes.bytesAt, List.range_add, List.map_append,
      List.map_map]
    congr 1
    simp only [VG.Proof.Aes.X86.AesNi.wv]
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [VG.Proof.Aes.X86.AesNi.ofNat_add', Mem.readW_byte m (p + BitVec.ofNat 64 (4 * K)) hj]

end VG.Proof.Aes.X86.AesNi

end

/-!
# AES-NI key expansion: the steps

Untrusted: everything here is checked by Lean. What `kstep` and `kstepB6`
compute, as doublewords (one symbolic execution of each, for any registers
and offsets), and `good_store`: storing a register whose first `n`
doublewords are the next `n` words of the schedule extends the stored
prefix of the schedule by `n` words.
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86
open VG.Impl.Aes.X86.AesNi (at_ kstep kstepB6)

/-! ## Doublewords -/

/-- `pslldq x, 4`. -/
def sh (x : BitVec 128) : BitVec 128 := x <<< 32

theorem pslldq4 (x : BitVec 128) : XShiftOp.eval .pslldq x 4 = VG.Proof.Aes.X86.AesNi.sh x := rfl

theorem eval_pxor' (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem dword_xor (a b : BitVec 128) (j : Nat) : dword (a ^^^ b) j = dword a j ^^^ dword b j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]

theorem dword_sh0 (x : BitVec 128) : dword (VG.Proof.Aes.X86.AesNi.sh x) 0 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, VG.Proof.Aes.X86.AesNi.sh, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_zero]
  simp; omega

theorem dword_sh (x : BitVec 128) {j : Nat} (hj : j < 3) : dword (VG.Proof.Aes.X86.AesNi.sh x) (j + 1) = dword x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, VG.Proof.Aes.X86.AesNi.sh, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rw [decide_eq_true (by omega), decide_eq_false (by omega), Bool.not_false, Bool.true_and,
    Bool.true_and]
  exact congrArg _ (by omega)

theorem dword_sh1 (x : BitVec 128) : dword (VG.Proof.Aes.X86.AesNi.sh x) 1 = dword x 0 := VG.Proof.Aes.X86.AesNi.dword_sh x (j := 0) (by decide)
theorem dword_sh2 (x : BitVec 128) : dword (VG.Proof.Aes.X86.AesNi.sh x) 2 = dword x 1 := VG.Proof.Aes.X86.AesNi.dword_sh x (j := 1) (by decide)
theorem dword_sh3 (x : BitVec 128) : dword (VG.Proof.Aes.X86.AesNi.sh x) 3 = dword x 2 := VG.Proof.Aes.X86.AesNi.dword_sh x (j := 2) (by decide)

/-- `prefixXor(x) ⊕ t`, as `kstep` computes it. -/
def kv (x t : BitVec 128) : BitVec 128 := x ^^^ VG.Proof.Aes.X86.AesNi.sh x ^^^ VG.Proof.Aes.X86.AesNi.sh (VG.Proof.Aes.X86.AesNi.sh x) ^^^ VG.Proof.Aes.X86.AesNi.sh (VG.Proof.Aes.X86.AesNi.sh (VG.Proof.Aes.X86.AesNi.sh x)) ^^^ t

theorem dword_kv (x t : BitVec 128) :
    dword (VG.Proof.Aes.X86.AesNi.kv x t) 0 = dword x 0 ^^^ dword t 0 ∧
    dword (VG.Proof.Aes.X86.AesNi.kv x t) 1 = dword x 1 ^^^ (dword x 0 ^^^ dword t 1) ∧
    dword (VG.Proof.Aes.X86.AesNi.kv x t) 2 = dword x 2 ^^^ (dword x 1 ^^^ (dword x 0 ^^^ dword t 2)) ∧
    dword (VG.Proof.Aes.X86.AesNi.kv x t) 3 = dword x 3 ^^^ (dword x 2 ^^^ (dword x 1 ^^^ (dword x 0 ^^^ dword t 3))) := by
  simp only [VG.Proof.Aes.X86.AesNi.kv, VG.Proof.Aes.X86.AesNi.dword_xor, VG.Proof.Aes.X86.AesNi.dword_sh0, VG.Proof.Aes.X86.AesNi.dword_sh1, VG.Proof.Aes.X86.AesNi.dword_sh2, VG.Proof.Aes.X86.AesNi.dword_sh3, BitVec.zero_xor,
    BitVec.xor_assoc, and_self]

/-- `[b₀, b₀ ⊕ b₁, …] ⊕ t`, as `kstepB6` computes it. -/
def kb (b t : BitVec 128) : BitVec 128 := b ^^^ VG.Proof.Aes.X86.AesNi.sh b ^^^ t

theorem dword_kb (b t : BitVec 128) :
    dword (VG.Proof.Aes.X86.AesNi.kb b t) 0 = dword b 0 ^^^ dword t 0 ∧
    dword (VG.Proof.Aes.X86.AesNi.kb b t) 1 = dword b 1 ^^^ (dword b 0 ^^^ dword t 1) := by
  simp only [VG.Proof.Aes.X86.AesNi.kb, VG.Proof.Aes.X86.AesNi.dword_xor, VG.Proof.Aes.X86.AesNi.dword_sh0, VG.Proof.Aes.X86.AesNi.dword_sh1, BitVec.zero_xor, BitVec.xor_assoc, and_self]

theorem shuf_ff (x : BitVec 128) :
    shufDwords x 0xff = ofDwords (dword x 3) (dword x 3) (dword x 3) (dword x 3) := rfl
theorem shuf_55 (x : BitVec 128) :
    shufDwords x 0x55 = ofDwords (dword x 1) (dword x 1) (dword x 1) (dword x 1) := rfl
theorem shuf_aa (x : BitVec 128) :
    shufDwords x 0xaa = ofDwords (dword x 2) (dword x 2) (dword x 2) (dword x 2) := rfl

theorem kga1 (x : BitVec 128) (r : BitVec 8) :
    dword (aesKeygenAssist x r) 1 = (VG.Proof.Aes.X86.AesNi.sub32 (dword x 1)).rotateRight 8 ^^^ r.setWidth 32 := by
  simp only [aesKeygenAssist, dword_ofDwords_1]; rfl

theorem kga2 (x : BitVec 128) (r : BitVec 8) : dword (aesKeygenAssist x r) 2 = VG.Proof.Aes.X86.AesNi.sub32 (dword x 3) := by
  simp only [aesKeygenAssist, dword_ofDwords_2]; rfl

theorem kga3 (x : BitVec 128) (r : BitVec 8) :
    dword (aesKeygenAssist x r) 3 = (VG.Proof.Aes.X86.AesNi.sub32 (dword x 3)).rotateRight 8 ^^^ r.setWidth 32 := by
  simp only [aesKeygenAssist, dword_ofDwords_3]; rfl

/-! ## The stored words -/

/-- Words `0 … K − 1` of `f` are stored at `p`, as little-endian doublewords. -/
def Good (m : Mem) (p : Addr) (f : Nat → BitVec 32) (K : Nat) : Prop :=
  ∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i

theorem good_store {m : Mem} {p : Addr} {f : Nat → BitVec 32} {K : Nat} (hG : VG.Proof.Aes.X86.AesNi.Good m p f K)
    (v : BitVec 128) {n : Nat} (hn : n ≤ 4) (hv : ∀ j < n, dword v j = f (K + j))
    (hK : 4 * K + 16 ≤ 240) :
    VG.Proof.Aes.X86.AesNi.Good (m.writeW (p + BitVec.ofNat 64 (4 * K)) v) p f (K + n) := by
  intro i hi
  by_cases h : i < K
  · rw [Mem.readW_writeW_sep (Offset.sep p (d := 4 * i) (n := 4) (e := 4 * K)
      (k := 16) (Or.inl (by omega)) (by omega) (by omega)) (by decide)]
    exact hG i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = K + j := ⟨i - K, by omega⟩
    rw [show 4 * (K + j) = 4 * K + 4 * j by omega, VG.Proof.Aes.X86.AesNi.ofNat_add', readW_writeW128 _ _ _ (by omega)]
    exact hv j (by omega)

theorem Good.mono {m : Mem} {p : Addr} {f : Nat → BitVec 32} {K K' : Nat} (h : VG.Proof.Aes.X86.AesNi.Good m p f K)
    (hK : K' ≤ K) : VG.Proof.Aes.X86.AesNi.Good m p f K' := fun i hi => h i (by omega)

end VG.Proof.Aes.X86.AesNi

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeySteps`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ kstep kstepB6)

theorem ea_setXmm (st : State) (d : XReg) (v : BitVec 128) (a : MemOp) :
    (st.setXmm d v).ea a = st.ea a := rfl

theorem kstep_exec (d s : XReg) (sel r : BitVec 8) (off : Nat) (st : State) (hd3 : d ≠ .xmm3)
    (hd4 : d ≠ .xmm4) (hw : InRegions st.wr (st.ea (VG.Impl.Aes.X86.AesNi.at_ .edx off)) 16) :
    WP isa (.block (kstep d s sel r off)) st fun st' =>
      st'.xmm d = VG.Proof.Aes.X86.AesNi.kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel) ∧
      st'.mem = st.mem.writeW (st.ea (VG.Impl.Aes.X86.AesNi.at_ .edx off))
        (VG.Proof.Aes.X86.AesNi.kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel)) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, kstep, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, State.store128, VG.Proof.Aes.X86.AesNi.ea_setXmm, hw, hd3, hd4, Ne.symm hd3, Ne.symm hd4,
    Option.some.injEq, exists_eq_left', eval_movdqa, VG.Proof.Aes.X86.AesNi.pslldq4, VG.Proof.Aes.X86.AesNi.eval_pxor']
  exact ⟨rfl, rfl, trivial, trivial, trivial, fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

theorem kstepB6_exec (off : Nat) (st : State)
    (hw : InRegions st.wr (st.ea (VG.Impl.Aes.X86.AesNi.at_ .edx off)) 16) :
    WP isa (.block (kstepB6 off)) st fun st' =>
      st'.xmm .xmm2 = VG.Proof.Aes.X86.AesNi.kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff) ∧
      st'.mem = st.mem.writeW (st.ea (VG.Impl.Aes.X86.AesNi.at_ .edx off))
        (VG.Proof.Aes.X86.AesNi.kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, kstepB6, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, State.store128, VG.Proof.Aes.X86.AesNi.ea_setXmm, hw,
    Option.some.injEq, exists_eq_left', eval_movdqa, VG.Proof.Aes.X86.AesNi.pslldq4, VG.Proof.Aes.X86.AesNi.eval_pxor']
  exact ⟨rfl, rfl, trivial, trivial, trivial, fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩


end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Proof.Aes.X86 (EPre keyP keyLen keyR ekSchP ekSchR ekArgR)

/-- A vector load changes no GPR, memory, or access region. -/
theorem key_load_exec (s : State) (x : XReg) (a : MemOp)
    (h : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    exec (.movdquLoad x a) s = some (s.setXmm x (s.mem.readW (s.ea a) 128)) := by
  simp only [exec, State.load128, h, ite_true, Option.map_some]

/-- A schedule vector store extends the exact little-endian word prefix. -/
theorem key_good_store (s : State) (p : Addr) (f : Nat → BitVec 32) (K n : Nat)
    (hG : VG.Proof.Aes.X86.AesNi.Good s.mem p f K) (v : BitVec 128) (hn : n ≤ 4)
    (hv : ∀ j < n, dword v j = f (K + j)) (hK : 4 * K + 16 ≤ 240) :
    VG.Proof.Aes.X86.AesNi.Good (s.mem.writeW (p + BitVec.ofNat 64 (4 * K)) v) p f (K + n) :=
  VG.Proof.Aes.X86.AesNi.good_store hG v hn hv hK

/-- Every key schedule store stays within its declared writable region. -/
theorem key_store_frame (m : Mem) (p : Addr) (d : Nat) (v : BitVec 128)
    (hd : d + 16 ≤ 240) :
    Frame [⟨p, 240⟩] m (m.writeW (p + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ _).writeW (v := v) (List.mem_singleton_self _)
    (Offset.contains_base p hd (by omega))

/-- Loading an initial key lane yields its four expansion words. -/
theorem key_initial_words (m : Mem) (p : Addr) (nk off : Nat)
    (h : off + 4 ≤ nk) :
    ∀ j < 4, dword (m.readW (p + BitVec.ofNat 64 (4 * off)) 128) j = VG.Proof.Aes.X86.AesNi.W m p nk (off + j) := by
  intro j hj
  rw [dword_readW _ _ hj, VG.Proof.Aes.X86.AesNi.W_lt (by omega),
    show 4 * (off + j) = 4 * off + 4 * j by omega, BitVec.ofNat_add, BitVec.add_assoc]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPrologue`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Proof.Aes.X86 (EPre keyP keyLen ekSchP ekArgR)

structure KeySetup (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

structure KeyReady (s₀ s : State) : Prop extends VG.Proof.Aes.X86.AesNi.KeySetup s₀ s where
  eax : s.gpr .eax = keyP s₀
  ecx : s.gpr .ecx = VG.X86.arg s₀ 1
  edx : s.gpr .edx = ekSchP s₀
  callee : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r

structure KeyStart (s₀ s : State) : Prop extends VG.Proof.Aes.X86.AesNi.KeyReady s₀ s where
  zf : s.zf = some (decide (VG.X86.arg s₀ 1 = 24#32))

theorem KeySetup.setReg {s₀ s : State} (h : VG.Proof.Aes.X86.AesNi.KeySetup s₀ s) (d : Reg) (v : BitVec 32)
    (hd : .esp ≠ d) : VG.Proof.Aes.X86.AesNi.KeySetup s₀ (s.setReg d v) :=
  ⟨by rw [gpr_setReg_of_ne _ _ hd]; exact h.esp,
    (mem_setReg _ _ _).trans h.mem, (rd_setReg _ _ _).trans h.rd,
    (wr_setReg _ _ _).trans h.wr⟩

theorem key_arg_contains {s : State} (hp : EPre s) {i : Nat} (hi : i < 4) :
    (ekArgR s).Contains (argAddr s i) 4 := by
  have hf := hp.fSp
  change (⟨addr (s.gpr .esp) 4, 16⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4
  rw [addr_eq (by omega), addr_eq (by omega)]
  rw [show (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) =
      ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4) + BitVec.ofNat 64 (4 * i) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  exact Offset.contains_base _ (by omega) (by omega)

theorem key_arg_exec {s₀ s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeySetup s₀ s)
    {i : Nat} (hi : i < 4) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (VG.X86.arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hs.esp]
  have hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
    refine ⟨ekArgR s₀, ?_, VG.Proof.Aes.X86.AesNi.key_arg_contains hp hi⟩
    simp only [hs.rd, hp.rd, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_true, true_or]
  simp only [exec, readSrc, State.load32, he, hin, ite_true, hs.mem, VG.X86.arg, Option.map_some]

def keyHead : List Instr :=
  [.mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
    .mov .edx (.mem (argOp 2)), .alu .cmp .ecx (.imm 24)]

theorem keyHead_ok (s₀ : State) (hp : EPre s₀) :
    WP isa (.block VG.Proof.Aes.X86.AesNi.keyHead) s₀ (VG.Proof.Aes.X86.AesNi.KeyStart s₀) := by
  have h₀ : VG.Proof.Aes.X86.AesNi.KeySetup s₀ s₀ := ⟨rfl, rfl, rfl, rfl⟩
  have h₁ := h₀.setReg .eax (VG.X86.arg s₀ 0) (by decide)
  have h₂ := h₁.setReg .ecx (VG.X86.arg s₀ 1) (by decide)
  apply WP.of_runBlock
  simp only [VG.Proof.Aes.X86.AesNi.keyHead]
  rw [runBlock_cons, VG.Proof.Aes.X86.AesNi.key_arg_exec hp h₀ (by decide), runStep_some,
    runBlock_cons, VG.Proof.Aes.X86.AesNi.key_arg_exec hp h₁ (by decide), runStep_some,
    runBlock_cons, VG.Proof.Aes.X86.AesNi.key_arg_exec hp h₂ (by decide), runStep_some]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, exec, execAlu, readSrc,
    gpr_setReg, Option.bind_some, runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · simp only [mem_arithFlags, mem_setReg]
  · simp only [rd_arithFlags, rd_setReg]
  · simp only [wr_arithFlags, wr_setReg]
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · simp only [gpr_arithFlags, gpr_setReg]; rfl
  · intro r h1 h2 h3
    simp only [gpr_arithFlags, gpr_setReg, h1, h2, h3, ite_false]
  · rw [zf_arithFlags]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
    rw [show (0 : BitVec 32) + 24 = 24#32 by decide]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Impl.Aes.X86.AesNi (rc)

/-- A broadcast supplies the same schedule temporary to every lane. -/
theorem broadcast_dword (x : BitVec 32) {j : Nat} (hj : j < 4) :
    dword (ofDwords x x x x) j = x := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · exact dword_ofDwords_0 _ _ _ _
  · exact dword_ofDwords_1 _ _ _ _
  · exact dword_ofDwords_2 _ _ _ _
  · exact dword_ofDwords_3 _ _ _ _

/-- Prefix XOR implements four consecutive recurrence words. -/
theorem kv_recurrence (f : Nat → BitVec 32) (B N : Nat) (a t : BitVec 128) (T : BitVec 32)
    (ha : ∀ j < 4, dword a j = f (B + j))
    (ht : ∀ j < 4, dword t j = T)
    (hr : ∀ j < 4, f (N + j) = f (B + j) ^^^ if j = 0 then T else f (N + j - 1)) :
    ∀ j < 4, dword (VG.Proof.Aes.X86.AesNi.kv a t) j = f (N + j) := by
  have h0 : f N = f B ^^^ T := by simpa only [Nat.add_zero, ite_true] using hr 0 (by decide)
  have h1 : f (N + 1) = f (B + 1) ^^^ f N := by simpa using hr 1 (by decide)
  have h2 : f (N + 2) = f (B + 2) ^^^ f (N + 1) := by simpa using hr 2 (by decide)
  have h3 : f (N + 3) = f (B + 3) ^^^ f (N + 2) := by simpa using hr 3 (by decide)
  have a0 : dword a 0 = f B := by simpa only [Nat.add_zero] using ha 0 (by decide)
  obtain ⟨v0, v1, v2, v3⟩ := VG.Proof.Aes.X86.AesNi.dword_kv a t
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rw [v0, a0, ht 0 (by decide)]
    simpa only [Nat.add_zero] using h0.symm
  · rw [v1, ha 1 (by decide), a0, ht 1 (by decide), Nat.add_zero, ← h0, ← h1]
  · rw [v2, ha 2 (by decide), ha 1 (by decide), a0, ht 2 (by decide),
      Nat.add_zero, ← h0, ← h1, ← h2]
  · rw [v3, ha 3 (by decide), ha 2 (by decide), ha 1 (by decide), a0,
      ht 3 (by decide), Nat.add_zero, ← h0, ← h1, ← h2, ← h3]

/-- AES-128 generates the next four schedule words. -/
theorem key128_next {m : Mem} {kp : Addr} (k : Nat) (a : BitVec 128)
    (ha : ∀ j < 4, dword a j = VG.Proof.Aes.X86.AesNi.W m kp 4 (4 * k + j)) :
    ∀ j < 4,
      dword (VG.Proof.Aes.X86.AesNi.kv a (shufDwords (aesKeygenAssist a (rc (k + 1))) 0xff)) j =
        VG.Proof.Aes.X86.AesNi.W m kp 4 (4 * (k + 1) + j) := by
  apply VG.Proof.Aes.X86.AesNi.kv_recurrence (VG.Proof.Aes.X86.AesNi.W m kp 4) (4 * k) (4 * (k + 1)) a _
    ((VG.Proof.Aes.X86.AesNi.sub32 (VG.Proof.Aes.X86.AesNi.W m kp 4 (4 * k + 3))).rotateRight 8 ^^^ (rc (k + 1)).setWidth 32) ha
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.shuf_ff, VG.Proof.Aes.X86.AesNi.broadcast_dword _ hj, VG.Proof.Aes.X86.AesNi.kga3, ha 3 (by decide)]
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.W_ge (by decide) (by omega)]
    rw [show 4 * (k + 1) + j - 4 = 4 * k + j by omega]
    by_cases h : j = 0
    · subst j
      simp only [VG.Proof.Aes.X86.AesNi.temp32, show (4 * (k + 1)) % 4 = 0 by omega, ite_true,
        show (4 * (k + 1)) / 4 = k + 1 by omega,
        show 4 * (k + 1) - 1 = 4 * k + 3 by omega, Nat.add_zero]
    · have hmod : (4 * (k + 1) + j) % 4 = j := by omega
      simp only [VG.Proof.Aes.X86.AesNi.temp32, hmod, h, ite_false, show ¬ (4 > 6 ∧ j = 4) by omega]

/-- AES-192 generates the next four schedule words. -/
theorem key192_first {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * k + j))
    (hb : ∀ j < 2, dword b j = VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * k + 4 + j)) :
    ∀ j < 4,
      dword (VG.Proof.Aes.X86.AesNi.kv a (shufDwords (aesKeygenAssist b (rc (k + 1))) 0x55)) j =
        VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + j) := by
  apply VG.Proof.Aes.X86.AesNi.kv_recurrence (VG.Proof.Aes.X86.AesNi.W m kp 6) (6 * k) (6 * (k + 1)) a _
    ((VG.Proof.Aes.X86.AesNi.sub32 (VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * k + 5))).rotateRight 8 ^^^ (rc (k + 1)).setWidth 32) ha
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.shuf_55, VG.Proof.Aes.X86.AesNi.broadcast_dword _ hj, VG.Proof.Aes.X86.AesNi.kga1, hb 1 (by decide)]
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.W_ge (by decide) (by omega)]
    rw [show 6 * (k + 1) + j - 6 = 6 * k + j by omega]
    by_cases h : j = 0
    · subst j
      simp only [VG.Proof.Aes.X86.AesNi.temp32, show (6 * (k + 1)) % 6 = 0 by omega, ite_true,
        show (6 * (k + 1)) / 6 = k + 1 by omega,
        show 6 * (k + 1) - 1 = 6 * k + 5 by omega, Nat.add_zero]
    · have hmod : (6 * (k + 1) + j) % 6 = j := by omega
      simp only [VG.Proof.Aes.X86.AesNi.temp32, hmod, h, ite_false, show ¬ (6 > 6 ∧ j = 4) by omega]

/-- AES-256 generates the next four schedule words. -/
theorem key256_first {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * k + j))
    (hb : ∀ j < 4, dword b j = VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * k + 4 + j)) :
    ∀ j < 4,
      dword (VG.Proof.Aes.X86.AesNi.kv a (shufDwords (aesKeygenAssist b (rc (k + 1))) 0xff)) j =
        VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * (k + 1) + j) := by
  apply VG.Proof.Aes.X86.AesNi.kv_recurrence (VG.Proof.Aes.X86.AesNi.W m kp 8) (8 * k) (8 * (k + 1)) a _
    ((VG.Proof.Aes.X86.AesNi.sub32 (VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * k + 7))).rotateRight 8 ^^^ (rc (k + 1)).setWidth 32) ha
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.shuf_ff, VG.Proof.Aes.X86.AesNi.broadcast_dword _ hj, VG.Proof.Aes.X86.AesNi.kga3, hb 3 (by decide)]
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.W_ge (by decide) (by omega)]
    rw [show 8 * (k + 1) + j - 8 = 8 * k + j by omega]
    by_cases h : j = 0
    · subst j
      simp only [VG.Proof.Aes.X86.AesNi.temp32, show (8 * (k + 1)) % 8 = 0 by omega, ite_true,
        show (8 * (k + 1)) / 8 = k + 1 by omega,
        show 8 * (k + 1) - 1 = 8 * k + 7 by omega, Nat.add_zero]
    · have hmod : (8 * (k + 1) + j) % 8 = j := by omega
      simp only [VG.Proof.Aes.X86.AesNi.temp32, hmod, h, ite_false, show ¬ (8 > 6 ∧ j = 4) by omega]

/-- AES-192's trailing pair continues the four newly generated words. -/
theorem key192_second {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + j))
    (hb : ∀ j < 2, dword b j = VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * k + 4 + j)) :
    ∀ j < 2, dword (VG.Proof.Aes.X86.AesNi.kb b (shufDwords a 0xff)) j = VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + 4 + j) := by
  obtain ⟨v0, v1⟩ := VG.Proof.Aes.X86.AesNi.dword_kb b (shufDwords a 0xff)
  have t0 : dword (shufDwords a 0xff) 0 = VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + 3) := by
    rw [VG.Proof.Aes.X86.AesNi.shuf_ff, VG.Proof.Aes.X86.AesNi.broadcast_dword _ (by decide), ha 3 (by decide)]
  have t1 : dword (shufDwords a 0xff) 1 = VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + 3) := by
    rw [VG.Proof.Aes.X86.AesNi.shuf_ff, VG.Proof.Aes.X86.AesNi.broadcast_dword _ (by decide), ha 3 (by decide)]
  have h0 : VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + 4) =
      VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * k + 4) ^^^ VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + 3) := by
    rw [VG.Proof.Aes.X86.AesNi.W_ge (by decide) (by omega)]
    rw [show 6 * (k + 1) + 4 - 6 = 6 * k + 4 by omega,
      show 6 * (k + 1) + 4 - 1 = 6 * (k + 1) + 3 by omega]
    simp only [VG.Proof.Aes.X86.AesNi.temp32, show (6 * (k + 1) + 4) % 6 = 4 by omega]
    rfl
  have h1 : VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + 4 + 1) =
      VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * k + 4 + 1) ^^^ VG.Proof.Aes.X86.AesNi.W m kp 6 (6 * (k + 1) + 4) := by
    rw [VG.Proof.Aes.X86.AesNi.W_ge (by decide) (by omega)]
    rw [show 6 * (k + 1) + 4 + 1 - 6 = 6 * k + 4 + 1 by omega,
      show 6 * (k + 1) + 4 + 1 - 1 = 6 * (k + 1) + 4 by omega]
    simp only [VG.Proof.Aes.X86.AesNi.temp32, show (6 * (k + 1) + 4 + 1) % 6 = 5 by omega]
    rfl
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · rw [v0, hb 0 (by decide), t0]
    simpa only [Nat.add_zero] using h0.symm
  · rw [v1, hb 1 (by decide), hb 0 (by decide), t1]
    simp only [Nat.add_zero]
    rw [← h0, ← h1]

/-- AES-256's alternating half-group uses the unrotated substitution. -/
theorem key256_second {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * (k + 1) + j))
    (hb : ∀ j < 4, dword b j = VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * k + 4 + j)) :
    ∀ j < 4, dword (VG.Proof.Aes.X86.AesNi.kv b (shufDwords (aesKeygenAssist a 0) 0xaa)) j =
      VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * (k + 1) + 4 + j) := by
  apply VG.Proof.Aes.X86.AesNi.kv_recurrence (VG.Proof.Aes.X86.AesNi.W m kp 8) (8 * k + 4) (8 * (k + 1) + 4) b _
    (VG.Proof.Aes.X86.AesNi.sub32 (VG.Proof.Aes.X86.AesNi.W m kp 8 (8 * (k + 1) + 3))) hb
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.shuf_aa, VG.Proof.Aes.X86.AesNi.broadcast_dword _ hj, VG.Proof.Aes.X86.AesNi.kga2, ha 3 (by decide)]
  · intro j hj
    rw [VG.Proof.Aes.X86.AesNi.W_ge (by decide) (by omega)]
    rw [show 8 * (k + 1) + 4 + j - 8 = 8 * k + 4 + j by omega]
    have hmod : (8 * (k + 1) + 4 + j) % 8 = 4 + j := by omega
    by_cases h : j = 0
    · subst j
      simp only [VG.Proof.Aes.X86.AesNi.temp32, hmod, Nat.add_zero, show ¬ (4 = 0) by decide, ite_false,
        show 8 > 6 ∧ 4 = 4 by decide, and_self, ite_true,
        show 8 * (k + 1) + 4 - 1 = 8 * (k + 1) + 3 by omega]
    · simp only [VG.Proof.Aes.X86.AesNi.temp32, hmod, show ¬ (4 + j = 0) by omega,
        show ¬ (8 > 6 ∧ 4 + j = 4) by omega, h, ite_false]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyContext`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (keyP ekSchP ekSchR)

/-- A complete schedule, with the unchanged body-entry GPRs and declared frame. -/
structure KeyDone (s₀ entry : State) (nk : Nat) (s : State) : Prop where
  words : VG.Proof.Aes.X86.AesNi.Good s.mem ((ekSchP s₀).setWidth 64)
    (VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) nk) (4 * (nk + 7))
  gpr : s.gpr = entry.gpr
  rd : s.rd = entry.rd
  wr : s.wr = entry.wr
  frame : Frame [ekSchR s₀] s₀.mem s.mem

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (EPre keyP keyLen keyR ekSchP ekSchR)
open VG.Impl.Aes.X86.AesNi (at_ rc kstep kstepB6 expand128 expand192 expand256)

/-- The stored schedule prefix and unchanged entry pointers. -/
structure KeyBody (s₀ entry : State) (nk K : Nat) (s : State) : Prop where
  words : VG.Proof.Aes.X86.AesNi.Good s.mem ((ekSchP s₀).setWidth 64) (VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) nk) K
  gpr : s.gpr = entry.gpr
  rd : s.rd = entry.rd
  wr : s.wr = entry.wr
  frame : Frame [ekSchR s₀] s₀.mem s.mem

theorem KeyBody.initial {s₀ entry : State} (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (nk : Nat) :
    VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk 0 entry :=
  ⟨fun i hi => False.elim (by omega), rfl, rfl, rfl, by rw [hs.mem]; exact Frame.refl _ _⟩

theorem KeyBody.ea {s₀ entry s : State} {nk K d : Nat} (hp : EPre s₀)
    (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s) (hd : d < 240) :
    s.ea (at_ .edx d) = (ekSchP s₀).setWidth 64 + BitVec.ofNat 64 d := by
  change addr (s.gpr .edx) d = _
  rw [h.gpr, hs.edx, addr_eq (by have hf := hp.fS; omega)]

theorem KeyBody.writable {s₀ entry s : State} {nk K d : Nat} (hp : EPre s₀)
    (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s) (hd : d + 16 ≤ 240) :
    InRegions s.wr (s.ea (at_ .edx d)) 16 := by
  rw [h.ea hp hs (by omega), h.wr, hs.wr]
  exact ⟨ekSchR s₀, by simp only [hp.wr, List.mem_cons, true_or],
    Offset.contains_base _ hd (by omega)⟩

theorem KeyBody.stored {s₀ entry s : State} {nk K n : Nat} (hp : EPre s₀)
    (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s) (v : BitVec 128)
    (hn : n ≤ 4) (hv : ∀ j < n, dword v j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) nk (K + j))
    (hK : 4 * K + 16 ≤ 240) {s' : State}
    (mem : s'.mem = s.mem.writeW (s.ea (at_ .edx (4 * K))) v)
    (gpr : s'.gpr = s.gpr) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk (K + n) s' := by
  have ea := h.ea hp hs (d := 4 * K) (by omega)
  refine ⟨?_, gpr.trans h.gpr, rd.trans h.rd, wr.trans h.wr, ?_⟩
  · rw [mem, ea]; exact VG.Proof.Aes.X86.AesNi.good_store h.words v hn hv hK
  · rw [mem, ea]
    exact h.frame.writeW (v := v) (List.mem_singleton_self _)
      (Offset.contains_base _ hK (by omega))

theorem key_store_ok {s₀ entry s : State} {nk K n : Nat} (hp : EPre s₀)
    (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s) (x : XReg)
    (hn : n ≤ 4) (hv : ∀ j < n, dword (s.xmm x) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) nk (K + j))
    (hK : 4 * K + 16 ≤ 240) :
    WP isa (.block [.movdquStore (at_ .edx (4 * K)) x]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk (K + n) s' ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  have hw := h.writable hp hs hK
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128,
    hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨h.stored hp hs _ hn hv hK rfl rfl rfl rfl, trivial⟩

theorem key_step_ok {s₀ entry s : State} {nk K n : Nat} (hp : EPre s₀)
    (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s)
    (d src : XReg) (sel r : BitVec 8) (hd3 : d ≠ .xmm3) (hd4 : d ≠ .xmm4)
    (hn : n ≤ 4)
    (hv : ∀ j < n, dword (VG.Proof.Aes.X86.AesNi.kv (s.xmm d) (shufDwords (aesKeygenAssist (s.xmm src) r) sel)) j =
      VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) nk (K + j))
    (hK : 4 * K + 16 ≤ 240) :
    WP isa (.block (kstep d src sel r (4 * K))) s fun s' =>
      VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk (K + n) s' ∧
      s'.xmm d = VG.Proof.Aes.X86.AesNi.kv (s.xmm d) (shufDwords (aesKeygenAssist (s.xmm src) r) sel) ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → s'.xmm x = s.xmm x := by
  refine WP.mono (VG.Proof.Aes.X86.AesNi.kstep_exec d src sel r (4 * K) s hd3 hd4 (h.writable hp hs hK))
    fun s' ⟨val, mem, gpr, rd, wr, other⟩ => ?_
  exact ⟨h.stored hp hs _ hn hv hK mem gpr rd wr, val, other⟩


theorem key_load_ok {s₀ entry s : State} {nk K off : Nat} (hp : EPre s₀)
    (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s) (x : XReg)
    (hoff : off + 16 ≤ keyLen s₀) :
    WP isa (.block [.movdquLoad x (at_ .eax off)]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s' ∧
      s'.xmm x = s₀.mem.readW ((keyP s₀).setWidth 64 + BitVec.ofNat 64 off) 128 ∧
      ∀ y, y ≠ x → s'.xmm y = s.xmm y := by
  have ea : s.ea (at_ .eax off) = (keyP s₀).setWidth 64 + BitVec.ofNat 64 off := by
    change addr (s.gpr .eax) off = _
    rw [h.gpr, hs.eax, addr_eq (by have hf := hp.fK; omega)]
  have hc : (keyR s₀).Contains (s.ea (at_ .eax off)) 16 := by
    rw [ea]; exact Offset.contains_base _ hoff (by have hf := hp.fK; omega)
  have hr : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax off)) 16 := by
    refine ⟨keyR s₀, ?_, hc⟩
    simp only [h.rd, hs.rd, hp.rd, List.mem_append, List.mem_cons, true_or]
  have hm : s.mem.readW (s.ea (at_ .eax off)) 128 = s₀.mem.readW (s.ea (at_ .eax off)) 128 := h.frame.readW hc (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r; exact hp.dKS) (by decide)
  apply WP.of_runBlock
  rw [runBlock_cons, VG.Proof.Aes.X86.AesNi.key_load_exec s x _ hr, runStep_some, runBlock_nil]
  refine ⟨s.setXmm x _, rfl, ?_⟩
  refine ⟨⟨h.words, h.gpr, h.rd, h.wr, h.frame⟩, ?_, ?_⟩
  · rw [xmm_setXmm_self, hm, ea]
  · intro y hy; exact xmm_setXmm_of_ne _ _ hy

structure KeyInv128 (s₀ entry : State) (k : Nat) (s : State) : Prop extends VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry 4 (4 * (k + 1)) s where
  a : ∀ j < 4, dword (s.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 4 (4 * k + j)

theorem key128_step {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    {k : Nat} (hk : k < 10) (h : VG.Proof.Aes.X86.AesNi.KeyInv128 s₀ entry k s) :
    WP isa (.block (kstep .xmm1 .xmm1 0xff (rc (k + 1)) (16 * (k + 1)))) s
      (VG.Proof.Aes.X86.AesNi.KeyInv128 s₀ entry (k + 1)) := by
  have hv := VG.Proof.Aes.X86.AesNi.key128_next k (s.xmm .xmm1) h.a
  have he : 16 * (k + 1) = 4 * (4 * (k + 1)) := by omega
  rw [he]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_step_ok hp hs h.toKeyBody .xmm1 .xmm1 0xff (rc (k + 1))
    (by decide) (by decide) (n := 4) (by decide) hv (by omega))
    fun s' ⟨body, val, _⟩ => ?_
  refine ⟨?_, ?_⟩
  · rw [show 4 * (k + 1 + 1) = 4 * (k + 1) + 4 by omega]
    exact body
  · rw [val]; exact hv

theorem key128_rounds {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (n : Nat) (hn : n ≤ 10) (h : VG.Proof.Aes.X86.AesNi.KeyInv128 s₀ entry 0 s) :
    WP isa (.block ((List.range n).flatMap fun k =>
      kstep .xmm1 .xmm1 0xff (rc (k + 1)) (16 * (k + 1)))) s (VG.Proof.Aes.X86.AesNi.KeyInv128 s₀ entry n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega)) fun _ hn' => VG.Proof.Aes.X86.AesNi.key128_step hp hs (by omega) hn'

theorem expand128_ok (s₀ entry : State) (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (hlen : keyLen s₀ = 16) : WP isa (.block expand128) entry (VG.Proof.Aes.X86.AesNi.KeyDone s₀ entry 4) := by
  unfold expand128
  rw [show ([.movdquLoad .xmm1 (at_ .eax 0), .movdquStore (at_ .edx 0) .xmm1] : List Instr) =
    [.movdquLoad .xmm1 (at_ .eax 0)] ++ [.movdquStore (at_ .edx 0) .xmm1] by rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_load_ok hp hs (KeyBody.initial hs 4) .xmm1 (by omega))
    fun s₁ ⟨h₁, a, _⟩ => ?_
  have ha : ∀ j < 4, dword (s₁.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 4 j := by
    have av : s₁.xmm .xmm1 = s₀.mem.readW ((keyP s₀).setWidth 64) 128 := by
      simpa only [BitVec.add_zero] using a
    intro j hj
    rw [av]
    have init := VG.Proof.Aes.X86.AesNi.key_initial_words s₀.mem ((keyP s₀).setWidth 64) 4 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at init
    exact init j hj
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_store_ok hp hs h₁ .xmm1 (n := 4) (by decide)
    (by simpa only [Nat.zero_add] using ha) (by decide)) fun s₂ ⟨h₂, x₂⟩ => ?_
  have hI : VG.Proof.Aes.X86.AesNi.KeyInv128 s₀ entry 0 s₂ := ⟨h₂, by rw [x₂]; simpa only [Nat.mul_zero, Nat.zero_add] using ha⟩
  exact WP.mono (VG.Proof.Aes.X86.AesNi.key128_rounds hp hs 10 (by decide) hI) fun _ hfin =>
    ⟨hfin.words, hfin.gpr, hfin.rd, hfin.wr, hfin.frame⟩


theorem key_load_words {s₀ entry s : State} {nk K off : Nat} (hp : EPre s₀)
    (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry) (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s) (x : XReg)
    (hoff : off + 4 ≤ nk) (hlen : keyLen s₀ = 4 * nk) :
    WP isa (.block [.movdquLoad x (at_ .eax (4 * off))]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry nk K s' ∧
      (∀ j < 4, dword (s'.xmm x) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) nk (off + j)) ∧
      ∀ y, y ≠ x → s'.xmm y = s.xmm y := by
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_load_ok hp hs h x (by omega)) fun s' ⟨body, val, other⟩ => ?_
  refine ⟨body, ?_, other⟩
  intro j hj
  rw [val]
  exact VG.Proof.Aes.X86.AesNi.key_initial_words _ _ nk off hoff j hj

structure KeyInv256 (s₀ entry : State) (k : Nat) (s : State) : Prop extends VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry 8 (8 * (k + 1)) s where
  a : ∀ j < 4, dword (s.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * k + j)
  b : ∀ j < 4, dword (s.xmm .xmm2) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * k + 4 + j)

def key256_pair (k : Nat) : List Instr :=
  kstep .xmm1 .xmm2 0xff (rc (k + 1)) (32 * (k + 1)) ++
    kstep .xmm2 .xmm1 0xaa 0 (32 * (k + 1) + 16)

theorem key256_step {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    {k : Nat} (hk : k < 6) (h : VG.Proof.Aes.X86.AesNi.KeyInv256 s₀ entry k s) :
    WP isa (.block (VG.Proof.Aes.X86.AesNi.key256_pair k)) s (VG.Proof.Aes.X86.AesNi.KeyInv256 s₀ entry (k + 1)) := by
  unfold VG.Proof.Aes.X86.AesNi.key256_pair
  rw [WP.block_append_iff, show 32 * (k + 1) = 4 * (8 * (k + 1)) by omega]
  have hv := VG.Proof.Aes.X86.AesNi.key256_first k (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0xff (rc (k + 1))
    (by decide) (by decide) (n := 4) (by decide) hv (by omega))
    fun s₁ ⟨h₁, a₁, oth₁⟩ => ?_
  have ha : ∀ j < 4, dword (s₁.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * (k + 1) + j) := by
    rw [a₁]; exact hv
  have hb : ∀ j < 4, dword (s₁.xmm .xmm2) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * k + 4 + j) := by
    rw [oth₁ .xmm2 (by decide) (by decide) (by decide)]; exact h.b
  have hv₂ := VG.Proof.Aes.X86.AesNi.key256_second k (s₁.xmm .xmm1) (s₁.xmm .xmm2) ha hb
  rw [show 4 * (8 * (k + 1)) + 16 = 4 * (8 * (k + 1) + 4) by omega]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_step_ok hp hs h₁ .xmm2 .xmm1 0xaa 0
    (by decide) (by decide) (n := 4) (by decide) hv₂ (by omega))
    fun s₂ ⟨h₂, b₂, oth₂⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [show 8 * (k + 1 + 1) = 8 * (k + 1) + 4 + 4 by omega]; exact h₂
  · rw [oth₂ .xmm1 (by decide) (by decide) (by decide)]; exact ha
  · rw [b₂]; exact hv₂

theorem key256_rounds {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (n : Nat) (hn : n ≤ 6) (h : VG.Proof.Aes.X86.AesNi.KeyInv256 s₀ entry 0 s) :
    WP isa (.block ((List.range n).flatMap VG.Proof.Aes.X86.AesNi.key256_pair)) s (VG.Proof.Aes.X86.AesNi.KeyInv256 s₀ entry n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega)) fun _ hn' => VG.Proof.Aes.X86.AesNi.key256_step hp hs (by omega) hn'

theorem key256_last {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (h : VG.Proof.Aes.X86.AesNi.KeyInv256 s₀ entry 6 s) :
    WP isa (.block (kstep .xmm1 .xmm2 0xff (rc 7) 224)) s (VG.Proof.Aes.X86.AesNi.KeyDone s₀ entry 8) := by
  have hv := VG.Proof.Aes.X86.AesNi.key256_first 6 (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  exact WP.mono (VG.Proof.Aes.X86.AesNi.key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0xff (rc 7)
    (by decide) (by decide) (n := 4) (by decide) hv (by decide))
    fun _ ⟨hf, _, _⟩ => ⟨hf.words, hf.gpr, hf.rd, hf.wr, hf.frame⟩

/-- Initial AES-256 key lanes are loaded before any schedule stores. -/
theorem key256_initial (s₀ entry : State) (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (hlen : keyLen s₀ = 32) :
    WP isa (.block [.movdquLoad .xmm1 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16),
      .movdquStore (at_ .edx 0) .xmm1, .movdquStore (at_ .edx 16) .xmm2]) entry (VG.Proof.Aes.X86.AesNi.KeyInv256 s₀ entry 0) := by
  change WP isa (.block (([.movdquLoad .xmm1 (at_ .eax (4 * 0))] : List Instr) ++
    ([.movdquLoad .xmm2 (at_ .eax (4 * 4))] : List Instr) ++
    ([.movdquStore (at_ .edx 0) .xmm1] : List Instr) ++
    ([.movdquStore (at_ .edx 16) .xmm2] : List Instr))) entry _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_load_words hp hs (KeyBody.initial hs 8) .xmm1 (off := 0) (by decide) hlen)
    fun s₁ ⟨h₁, a₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_load_words hp hs h₁ .xmm2 (off := 4) (by decide) hlen)
    fun s₂ ⟨h₂, b₂, oth₂⟩ => ?_
  have ha : ∀ j < 4, dword (s₂.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 8 j := by
    rw [oth₂ .xmm1 (by decide)]; simpa only [Nat.zero_add] using a₁
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_store_ok hp hs h₂ .xmm1 (n := 4) (by decide) (by simpa only [Nat.zero_add] using ha) (by decide))
    fun s₃ ⟨h₃, x₃⟩ => ?_
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_store_ok hp hs h₃ .xmm2 (n := 4) (by decide)
    (by rw [x₃]; exact b₂) (by decide)) fun s₄ ⟨h₄, x₄⟩ => ?_
  refine ⟨h₄, ?_, ?_⟩
  · rw [x₄, x₃]; simpa only [Nat.mul_zero, Nat.zero_add] using ha
  · rw [x₄, x₃]; simpa only [Nat.mul_zero, Nat.zero_add] using b₂

theorem expand256_ok (s₀ entry : State) (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (hlen : keyLen s₀ = 32) : WP isa (.block expand256) entry (VG.Proof.Aes.X86.AesNi.KeyDone s₀ entry 8) := by
  unfold expand256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key256_initial s₀ entry hp hs hlen) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (VG.Proof.Aes.X86.AesNi.key256_rounds hp hs 6 (by decide) h₁) fun _ hfin => VG.Proof.Aes.X86.AesNi.key256_last hp hs hfin


structure KeyInv192 (s₀ entry : State) (k : Nat) (s : State) : Prop extends VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry 6 (6 * (k + 1)) s where
  a : ∀ j < 4, dword (s.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * k + j)
  b : ∀ j < 2, dword (s.xmm .xmm2) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * k + 4 + j)

def key192_pair (k : Nat) : List Instr :=
  kstep .xmm1 .xmm2 0x55 (rc (k + 1)) (24 * (k + 1)) ++ kstepB6 (24 * (k + 1) + 16)

theorem key192_step {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    {k : Nat} (hk : k < 7) (h : VG.Proof.Aes.X86.AesNi.KeyInv192 s₀ entry k s) :
    WP isa (.block (VG.Proof.Aes.X86.AesNi.key192_pair k)) s (VG.Proof.Aes.X86.AesNi.KeyInv192 s₀ entry (k + 1)) := by
  unfold VG.Proof.Aes.X86.AesNi.key192_pair
  rw [WP.block_append_iff, show 24 * (k + 1) = 4 * (6 * (k + 1)) by omega]
  have hv := VG.Proof.Aes.X86.AesNi.key192_first k (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0x55 (rc (k + 1))
    (by decide) (by decide) (n := 4) (by decide) hv (by omega))
    fun s₁ ⟨h₁, a₁, oth₁⟩ => ?_
  have ha : ∀ j < 4, dword (s₁.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * (k + 1) + j) := by
    rw [a₁]; exact hv
  have hb : ∀ j < 2, dword (s₁.xmm .xmm2) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * k + 4 + j) := by
    rw [oth₁ .xmm2 (by decide) (by decide) (by decide)]; exact h.b
  have hv₂ := VG.Proof.Aes.X86.AesNi.key192_second k (s₁.xmm .xmm1) (s₁.xmm .xmm2) ha hb
  rw [show 4 * (6 * (k + 1)) + 16 = 4 * (6 * (k + 1) + 4) by omega]
  have hK : 4 * (6 * (k + 1) + 4) + 16 ≤ 240 := by omega
  refine WP.mono (VG.Proof.Aes.X86.AesNi.kstepB6_exec (4 * (6 * (k + 1) + 4)) s₁ (h₁.writable hp hs hK))
    fun s₂ ⟨b₂, mem, gpr, rd, wr, oth₂⟩ => ?_
  have h₂ := h₁.stored hp hs _ (n := 2) (by decide) hv₂ hK mem gpr rd wr
  refine ⟨?_, ?_, ?_⟩
  · rw [show 6 * (k + 1 + 1) = 6 * (k + 1) + 4 + 2 by omega]; exact h₂
  · rw [oth₂ .xmm1 (by decide) (by decide) (by decide)]; exact ha
  · rw [b₂]; exact hv₂

theorem key192_rounds {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (n : Nat) (hn : n ≤ 7) (h : VG.Proof.Aes.X86.AesNi.KeyInv192 s₀ entry 0 s) :
    WP isa (.block ((List.range n).flatMap VG.Proof.Aes.X86.AesNi.key192_pair)) s (VG.Proof.Aes.X86.AesNi.KeyInv192 s₀ entry n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega)) fun _ hn' => VG.Proof.Aes.X86.AesNi.key192_step hp hs (by omega) hn'

theorem key192_last {s₀ entry s : State} (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (h : VG.Proof.Aes.X86.AesNi.KeyInv192 s₀ entry 7 s) :
    WP isa (.block (kstep .xmm1 .xmm2 0x55 (rc 8) 192)) s (VG.Proof.Aes.X86.AesNi.KeyDone s₀ entry 6) := by
  have hv := VG.Proof.Aes.X86.AesNi.key192_first 7 (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  exact WP.mono (VG.Proof.Aes.X86.AesNi.key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0x55 (rc 8)
    (by decide) (by decide) (n := 4) (by decide) hv (by decide))
    fun _ ⟨hf, _, _⟩ => ⟨hf.words, hf.gpr, hf.rd, hf.wr, hf.frame⟩

/-- The upper two key words are moved into the low two SIMD lanes. -/
theorem dword_psrldq8 (v : BitVec 128) (j : Nat) :
    dword (XShiftOp.eval .psrldq v 8) j = dword v (j + 2) := by
  change dword (v >>> 64) j = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  exact congrArg _ (by omega)

theorem key192_shift {s₀ entry s : State} (h : VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry 6 0 s)
    (ha : ∀ j < 4, dword (s.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 j)
    (hb : ∀ j < 4, dword (s.xmm .xmm2) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 (2 + j)) :
    WP isa (.block [.xop (.shift .psrldq .xmm2 8)]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.KeyBody s₀ entry 6 0 s' ∧
      (∀ j < 4, dword (s'.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 j) ∧
      ∀ j < 2, dword (s'.xmm .xmm2) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 (4 + j) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.words, h.gpr, h.rd, h.wr, h.frame⟩, ?_, ?_⟩
  · rw [xmm_setXmm_of_ne _ _ (by decide)]; exact ha
  · intro j hj
    rw [xmm_setXmm_self, VG.Proof.Aes.X86.AesNi.dword_psrldq8 _ j, hb (j + 2) (by omega),
      show 2 + (j + 2) = 4 + j by omega]

theorem key192_initial (s₀ entry : State) (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (hlen : keyLen s₀ = 24) :
    WP isa (.block [.movdquLoad .xmm1 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 8),
      .xop (.shift .psrldq .xmm2 8), .movdquStore (at_ .edx 0) .xmm1,
      .movdquStore (at_ .edx 16) .xmm2]) entry (VG.Proof.Aes.X86.AesNi.KeyInv192 s₀ entry 0) := by
  change WP isa (.block (([.movdquLoad .xmm1 (at_ .eax (4 * 0))] : List Instr) ++
    ([.movdquLoad .xmm2 (at_ .eax (4 * 2))] : List Instr) ++
    ([.xop (.shift .psrldq .xmm2 8)] : List Instr) ++
    ([.movdquStore (at_ .edx 0) .xmm1] : List Instr) ++
    ([.movdquStore (at_ .edx 16) .xmm2] : List Instr))) entry _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_load_words hp hs (KeyBody.initial hs 6) .xmm1 (off := 0) (by decide) hlen)
    fun s₁ ⟨h₁, a₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_load_words hp hs h₁ .xmm2 (off := 2) (by decide) hlen)
    fun s₂ ⟨h₂, b₂, oth₂⟩ => ?_
  have ha : ∀ j < 4, dword (s₂.xmm .xmm1) j = VG.Proof.Aes.X86.AesNi.W s₀.mem ((keyP s₀).setWidth 64) 6 j := by
    rw [oth₂ .xmm1 (by decide)]; simpa only [Nat.zero_add] using a₁
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key192_shift h₂ ha b₂) fun s₃ ⟨h₃, a₃, b₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_store_ok hp hs h₃ .xmm1 (n := 4) (by decide)
    (by simpa only [Nat.zero_add] using a₃) (by decide)) fun s₄ ⟨h₄, x₄⟩ => ?_
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key_store_ok hp hs h₄ .xmm2 (n := 2) (by decide)
    (by rw [x₄]; exact b₃) (by decide)) fun s₅ ⟨h₅, x₅⟩ => ?_
  refine ⟨h₅, ?_, ?_⟩
  · rw [x₅, x₄]; simpa only [Nat.mul_zero, Nat.zero_add] using a₃
  · rw [x₅, x₄]; simpa only [Nat.mul_zero, Nat.zero_add] using b₃

theorem expand192_ok (s₀ entry : State) (hp : EPre s₀) (hs : VG.Proof.Aes.X86.AesNi.KeyReady s₀ entry)
    (hlen : keyLen s₀ = 24) : WP isa (.block expand192) entry (VG.Proof.Aes.X86.AesNi.KeyDone s₀ entry 6) := by
  unfold expand192
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.key192_initial s₀ entry hp hs hlen) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (VG.Proof.Aes.X86.AesNi.key192_rounds hp hs 7 (by decide) h₁) fun _ hfin => VG.Proof.Aes.X86.AesNi.key192_last hp hs hfin

end VG.Proof.Aes.X86.AesNi

end
