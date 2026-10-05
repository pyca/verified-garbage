import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Impl.Aes.X86_64.AesNi
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds`. -/
section

section

/-!
# AES-NI: the instructions are FIPS 197's rounds

An SSE register holds an AES state as its 16 bytes in memory order (`st`):
byte `r + 4c` is `s[r, c]`, as FIPS 197 §3.4 lays the state out and as the
SDM's AES instructions read it. On such registers `pxor`, `aesenc` and
`aesenclast` are `AddRoundKey`, a full round and the last round of
`Spec.Aes.cipher` (`pxor_st`, `aesenc_st`, `aesenclast_st`); the S-box of the
ISA model, computed by repeated squaring, is the one of `Spec/Aes.lean`
(`sbox_eq`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey sbox roundKey cipher bytesAt)

/-! ## GF(2⁸) -/

theorem mul_eq : aesMul = Spec.Aes.mul := rfl

/-- Both square and multiply `b²`, `b⁴`, …, `b¹²⁸` in the same order: unfolded
to the same term (no evaluation left for the kernel). -/
theorem inv_eq (b : BitVec 8) : aesInv b = Spec.Aes.inv b := by
  simp (config := {decide := true}) only [aesInv, Spec.Aes.inv, Spec.Aes.pow, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, VG.Proof.Aes.X86_64.AesNi.mul_eq,
    ite_true, ite_false]

theorem sbox_eq : aesSbox = sbox := by
  funext b
  simp only [aesSbox, sbox, VG.Proof.Aes.X86_64.AesNi.inv_eq, ofBits8]

theorem mul_one' : ∀ b : BitVec 8, Spec.Aes.mul 1 b = b := by decide +kernel

/-! ## States in registers -/

/-- The AES state held by a register. -/
def st (v : BitVec 128) : Spec.Aes.State := Vector.ofFn fun i => byte v i

theorem getD_ofFn {f : Fin 16 → Byte} {i : Nat} (h : i < 16) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

theorem getD_st (v : BitVec 128) {i : Nat} (h : i < 16) : (VG.Proof.Aes.X86_64.AesNi.st v).getD i 0 = byte v i := by
  rw [VG.Proof.Aes.X86_64.AesNi.st, VG.Proof.Aes.X86_64.AesNi.getD_ofFn h]

theorem st_ext {s t : Spec.Aes.State} (h : ∀ i < 16, s.getD i 0 = t.getD i 0) : s = t := by
  apply Vector.ext; intro i hi
  have := h i hi
  simpa [Vector.getD, hi] using this

theorem st_inj {a b : BitVec 128} (h : VG.Proof.Aes.X86_64.AesNi.st a = VG.Proof.Aes.X86_64.AesNi.st b) : a = b :=
  VG.Proof.Gcm.X86_64.ext_byte fun i hi => by rw [← VG.Proof.Aes.X86_64.AesNi.getD_st a hi, ← VG.Proof.Aes.X86_64.AesNi.getD_st b hi, h]

theorem byte_xor (a b : BitVec 128) (i : Nat) : byte (a ^^^ b) i = byte a i ^^^ byte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

/-! ## FIPS 197's transformations, byte by byte -/

theorem getD_addRoundKey (s : Spec.Aes.State) (rk : List Byte) {i : Nat} (h : i < 16) :
    (addRoundKey s rk).getD i 0 = s.getD i 0 ^^^ rk.getD i 0 := by
  rw [addRoundKey, VG.Proof.Aes.X86_64.AesNi.getD_ofFn h]

theorem getD_subBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (subBytes s).getD i 0 = sbox (s.getD i 0) := by
  simp [subBytes, Vector.getD, h]

theorem getD_shiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (shiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [shiftRows, VG.Proof.Aes.X86_64.AesNi.getD_ofFn h]

theorem getD_mixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (mixColumns s).getD i 0 =
      Spec.Aes.mul 0x02 (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x03 (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0 ^^^ s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0 := by
  rw [mixColumns, VG.Proof.Aes.X86_64.AesNi.getD_ofFn h]

theorem byte_mapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMapBytes f x) i = f (byte x i) := by
  rw [aesMapBytes, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_shiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesShiftRows x) i = byte x (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  rw [aesShiftRows, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_mixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMixColumns x) i =
      aesMul 0x02 (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x03 (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesMixColumns, aesMixWith, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

/-! ## The instructions -/

/-- `pxor` with a round key is `AddRoundKey`. -/
theorem pxor_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86_64.AesNi.st (XBinOp.eval .pxor v k) = addRoundKey (VG.Proof.Aes.X86_64.AesNi.st v) rk := by
  apply VG.Proof.Aes.X86_64.AesNi.st_ext; intro i hi
  rw [VG.Proof.Aes.X86_64.AesNi.getD_st _ hi, VG.Proof.Aes.X86_64.AesNi.getD_addRoundKey _ _ hi, VG.Proof.Aes.X86_64.AesNi.getD_st _ hi, ← hk i hi]
  exact VG.Proof.Aes.X86_64.AesNi.byte_xor v k i

/-- `aesenc` is a round. -/
theorem aesenc_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86_64.AesNi.st (XBinOp.eval .aesenc v k) = addRoundKey (mixColumns (shiftRows (subBytes (VG.Proof.Aes.X86_64.AesNi.st v)))) rk := by
  apply VG.Proof.Aes.X86_64.AesNi.st_ext; intro i hi
  rw [VG.Proof.Aes.X86_64.AesNi.getD_st _ hi, VG.Proof.Aes.X86_64.AesNi.getD_addRoundKey _ _ hi, VG.Proof.Aes.X86_64.AesNi.getD_mixColumns _ hi, ← hk i hi]
  simp only [XBinOp.eval, VG.Proof.Aes.X86_64.AesNi.byte_xor]
  rw [VG.Proof.Aes.X86_64.AesNi.byte_mixColumns _ hi]
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [VG.Proof.Aes.X86_64.AesNi.byte_mapBytes _ _ (hr _), VG.Proof.Aes.X86_64.AesNi.getD_shiftRows _ (hr _), VG.Proof.Aes.X86_64.AesNi.byte_shiftRows _ (hr _), VG.Proof.Aes.X86_64.AesNi.sbox_eq,
    VG.Proof.Aes.X86_64.AesNi.mul_eq, VG.Proof.Aes.X86_64.AesNi.mul_one', VG.Proof.Aes.X86_64.AesNi.getD_subBytes _ (hs _), VG.Proof.Aes.X86_64.AesNi.getD_st _ (hs _)]

/-- `aesenclast` is the last round. -/
theorem aesenclast_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86_64.AesNi.st (XBinOp.eval .aesenclast v k) = addRoundKey (shiftRows (subBytes (VG.Proof.Aes.X86_64.AesNi.st v))) rk := by
  apply VG.Proof.Aes.X86_64.AesNi.st_ext; intro i hi
  rw [VG.Proof.Aes.X86_64.AesNi.getD_st _ hi, VG.Proof.Aes.X86_64.AesNi.getD_addRoundKey _ _ hi, ← hk i hi]
  simp only [XBinOp.eval, VG.Proof.Aes.X86_64.AesNi.byte_xor]
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [VG.Proof.Aes.X86_64.AesNi.byte_mapBytes _ _ hi, VG.Proof.Aes.X86_64.AesNi.getD_shiftRows _ hi, VG.Proof.Aes.X86_64.AesNi.byte_shiftRows _ hi, VG.Proof.Aes.X86_64.AesNi.sbox_eq,
    VG.Proof.Aes.X86_64.AesNi.getD_subBytes _ (hs _), VG.Proof.Aes.X86_64.AesNi.getD_st _ (hs _)]

/-! ## The cipher -/

/-- The state after `AddRoundKey` and `k` full rounds. -/
def rnds (w : List Byte) (x : Spec.Aes.State) (k : Nat) : Spec.Aes.State :=
  (List.range k).foldl
    (fun s j => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (j + 1)))
    (addRoundKey x (roundKey w 0))

theorem rnds_zero (w : List Byte) (x : Spec.Aes.State) :
    VG.Proof.Aes.X86_64.AesNi.rnds w x 0 = addRoundKey x (roundKey w 0) := rfl

theorem rnds_succ (w : List Byte) (x : Spec.Aes.State) (k : Nat) :
    VG.Proof.Aes.X86_64.AesNi.rnds w x (k + 1) =
      addRoundKey (mixColumns (shiftRows (subBytes (VG.Proof.Aes.X86_64.AesNi.rnds w x k)))) (roundKey w (k + 1)) := by
  simp only [VG.Proof.Aes.X86_64.AesNi.rnds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem cipher_eq (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher nr w x = addRoundKey (shiftRows (subBytes (VG.Proof.Aes.X86_64.AesNi.rnds w x (nr - 1)))) (roundKey w nr) := rfl

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
  rw [VG.Proof.Gcm.X86_64.byte_readW _ _ hi, VG.Proof.Aes.X86_64.AesNi.roundKey_getD _ _ hi hj, VG.Proof.Aes.X86_64.AesNi.ofInt_natCast,
    BitVec.add_assoc, BitVec.ofNat_add]

theorem st_toList (r : BitVec 128) : (VG.Proof.Aes.X86_64.AesNi.st r).toList = (List.range 16).map (byte r) := by
  apply List.ext_getElem <;> simp [VG.Proof.Aes.X86_64.AesNi.st]

/-- `CIPH_K` of a block, as `Spec.Gcm.aesWith` states it, from the register
`r` that encrypting the block's bytes left. -/
theorem aesWith_eq (nr : Nat) (w : List Byte) (x r : BitVec 128)
    (h : VG.Proof.Aes.X86_64.AesNi.st r = cipher nr w (VG.Proof.Aes.X86_64.AesNi.st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86_64.revMask))) :
    Spec.Gcm.aesWith nr w x = XBinOp.eval .pshufb r VG.Proof.Gcm.X86_64.revMask := by
  have e : (Vector.ofFn fun i => (Spec.Gcm.toBytes x).getD i 0) =
      VG.Proof.Aes.X86_64.AesNi.st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86_64.revMask) := by
    apply VG.Proof.Aes.X86_64.AesNi.st_ext; intro i hi
    rw [VG.Proof.Aes.X86_64.AesNi.getD_ofFn hi, VG.Proof.Aes.X86_64.AesNi.getD_st _ hi, VG.Proof.Gcm.X86_64.byte_pshufb_rev _ hi]
    simp [Spec.Gcm.toBytes, List.getD, hi, byte]
  rw [Spec.Gcm.aesWith, e, ← h, VG.Proof.Aes.X86_64.AesNi.st_toList, VG.Proof.Gcm.X86_64.gcmOfBytes_eq,
    VG.Proof.Gcm.X86_64.pshufb_rev]

end VG.Proof.Aes.X86_64.AesNi

end

/-!
# AES-NI: encrypting the block registers

`aes_ok`: `Impl.Aes.X86_64.AesNi.aes regs` encrypts each register of `regs`
with the key schedule at `rdi` (10, 12 or 14 rounds, as `rsi` says), whatever
the list of registers; the rounds are composed by induction, one symbolic
execution per instruction.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open Spec.Gcm

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_ctr32_aesni(schedule: *const [u8; 240], rounds:
usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut
[u64; 256])`: XORs the AES counter-mode keystream from the counter block at
`counter` into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes). These may not
overlap each other, nor the return address on the stack, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block
and the data are secret. -/
def ctr32X86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let counter : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 2048⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := VG.Spec.Gcm.aesWith (s.gpr .rsi).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
    VG.Spec.Gcm.blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
        ctr32 ciph (VG.Spec.Gcm.blockAt s.mem (s.gpr .rdx)) (VG.Spec.Gcm.blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) ∧
      VG.Spec.Gcm.blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 (s.gpr .r8).toNat (VG.Spec.Gcm.blockAt s.mem (s.gpr .rdx))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_expand_key_aesni(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: for a key of 16, 24 or 32
bytes at `key`, writes its key schedule (`16 (Nr + 1)` bytes) to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes), which may not overlap the return
address on the stack. The pointers and `key_len` are public; the key is
secret. -/
def expandKeyX86_64 : Contract X86_64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let sched : Region := ⟨s.gpr .rdx, 240⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ ret.Disjoint sched ∧
    ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) (16 * (Spec.Aes.rounds ((s.gpr .rsi).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.Aes.X86_64.AesNi

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ keyOp round aes)
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey roundKey cipher bytesAt)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

/-- An address relative to `p + o`, as a distance from `p`. -/
theorem off_toNat (a p : Addr) {o : Nat} (ho : o < 2 ^ 64) :
    (a - (p + BitVec.ofNat 64 o)).toNat = ((a - p).toNat + (2 ^ 64 - o)) % 2 ^ 64 := by
  rw [show a - (p + BitVec.ofNat 64 o) = (a - p) - BitVec.ofNat 64 o by
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc],
    BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho, Nat.add_comm]

/-- `s'` is `s` but for the SSE registers `rs` (and the flags). -/
structure XFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem XFrame.refl (rs : List XReg) (s : State) : VG.Proof.Aes.X86_64.AesNi.XFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XFrame.trans {rs : List XReg} {s s' s'' : State} (h : VG.Proof.Aes.X86_64.AesNi.XFrame rs s s') (h' : VG.Proof.Aes.X86_64.AesNi.XFrame rs s' s'') :
    VG.Proof.Aes.X86_64.AesNi.XFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem XFrame.comp {rs rs' : List XReg} {s s' s'' : State} (h : VG.Proof.Aes.X86_64.AesNi.XFrame rs s s')
    (h' : VG.Proof.Aes.X86_64.AesNi.XFrame rs' s' s'') : VG.Proof.Aes.X86_64.AesNi.XFrame (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem XFrame.mono {rs rs' : List XReg} {s s' : State} (h : VG.Proof.Aes.X86_64.AesNi.XFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.Aes.X86_64.AesNi.XFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- `op b, xmm8` for each `b` of `regs`. -/
theorem map_ok (op : XBinOp) : ∀ (regs : List XReg) (s : State), regs.Nodup → .xmm8 ∉ regs →
    WP isa (.block (regs.map fun b => .xop (.bin op b .xmm8))) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.xmm .xmm8)) ∧ VG.Proof.Aes.X86_64.AesNi.XFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, XFrame.refl _ _⟩
  | b :: bs, s, hnd, h8 => by
    have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ List.mem_cons_self ..)
    have h8' : .xmm8 ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨s.setXmm b (op.eval (s.xmm b) (s.xmm .xmm8)), rfl, ?_⟩
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.map_ok op bs _ (List.nodup_cons.mp hnd).2 h8') fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.xmm _ hbs]; simp [State.setXmm]
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc]; simp [State.setXmm, hcb, Ne.symm hb8]
    · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.xmm r hr.2]; simp [State.setXmm, hr.1]

/-- A round key into `xmm8`, then `op b, xmm8` for each `b` of `regs`. -/
theorem keyOp_ok (regs : List XReg) (op : XBinOp) (a : MemOp) (s : State) (hnd : regs.Nodup)
    (h8 : .xmm8 ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    WP isa (.block (keyOp regs op a)) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.mem.readW (s.ea a) 128)) ∧
      VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm8 :: regs) s s' := by
  rw [keyOp, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm8 (s.mem.readW (s.ea a) 128), by
    simp [isa, exec, State.load128, hin], ?_⟩
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.map_ok op regs _ hnd h8) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, ?_⟩
  · have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ hb)
    rw [hv b hb]; simp [State.setXmm, hb8]
  · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.xmm r hr.2]; simp [State.setXmm, hr.1]

/-! ## The rounds -/

/-- Each register `b` of `regs` holds the state after `k` rounds of the
cipher, from the state `x b`. -/
def RInv (regs : List XReg) (w : List Byte) (x : XReg → Spec.Aes.State) (k : Nat) (s : State) : Prop :=
  ∀ b ∈ regs, VG.Proof.Aes.X86_64.AesNi.st (s.xmm b) = VG.Proof.Aes.X86_64.AesNi.rnds w (x b) k

/-- What the rounds need of the state: the key schedule at `rdi`, readable. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  sched : w = VG.Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1))
  le : nr ≤ 14
  keys : ∀ j ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : VG.Proof.Aes.X86_64.AesNi.Keys nr w s)
    (hf : VG.Proof.Aes.X86_64.AesNi.XFrame rs s s') : VG.Proof.Aes.X86_64.AesNi.Keys nr w s' :=
  ⟨by rw [hf.mem, hf.gpr]; exact h.sched, h.le, by rw [hf.rd, hf.wr, hf.gpr]; exact h.keys⟩

theorem round_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {k : Nat} (hk : k + 1 ≤ nr) {s : State}
    (hK : VG.Proof.Aes.X86_64.AesNi.Keys nr w s) (hI : VG.Proof.Aes.X86_64.AesNi.RInv regs w x k s) :
    WP isa (.block (round regs (k + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.RInv regs w x (k + 1) s' ∧ VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm8 :: regs) s s' := by
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.keyOp_ok regs .aesenc _ s hnd h8 (by rw [VG.Proof.Aes.X86_64.AesNi.ea_at]; exact hK.keys _ hk))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, VG.Proof.Aes.X86_64.AesNi.aesenc_st _ _ (roundKey w (k + 1)) (by
    rw [hK.sched, VG.Proof.Aes.X86_64.AesNi.ea_at]; exact VG.Proof.Aes.X86_64.AesNi.byte_roundKey _ _ (by omega)), hI b hb, VG.Proof.Aes.X86_64.AesNi.rnds_succ]

theorem rounds_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (s : State) (hk : k ≤ nr)
    (hK : VG.Proof.Aes.X86_64.AesNi.Keys nr w s) (hI : VG.Proof.Aes.X86_64.AesNi.RInv regs w x 0 s) :
    WP isa (.block ((List.range k).flatMap fun j => round regs (j + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.RInv regs w x k s' ∧ VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm8 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (VG.Proof.Aes.X86_64.AesNi.round_ok regs hnd h8 (k := k) (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

/-- `cmp rsi, c` with `rsi = nr`. -/
theorem cmpRsi_ok (s : State) (c : BitVec 32) (nr : Nat) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ VG.Proof.Aes.X86_64.AesNi.XFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, arithFlags,
    State.setFlags, isa, hrsi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem aes_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : VG.Proof.Aes.X86_64.AesNi.Keys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (VG.Impl.Aes.X86_64.AesNi.aes regs) s fun s' =>
      (∀ b ∈ regs, VG.Proof.Aes.X86_64.AesNi.st (s'.xmm b) = cipher nr w (VG.Proof.Aes.X86_64.AesNi.st (s.xmm b))) ∧ VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm8 :: regs) s s' := by
  let x : XReg → Spec.Aes.State := fun b => VG.Proof.Aes.X86_64.AesNi.st (s.xmm b)
  have k0 := VG.Proof.Aes.X86_64.AesNi.byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  -- `AddRoundKey` and rounds 1–9.
  have h₁ : WP isa (.block (keyOp regs .pxor (at_ .rdi 0) ++
      (List.range 9).flatMap fun j => round regs (j + 1))) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.RInv regs w x 9 s' ∧ VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm8 :: regs) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.keyOp_ok regs .pxor _ s hnd h8 (by rw [VG.Proof.Aes.X86_64.AesNi.ea_at]; exact hK.keys 0 (by omega)))
      fun s₁ ⟨hv₁, hf₁⟩ => ?_
    have hI₁ : VG.Proof.Aes.X86_64.AesNi.RInv regs w x 0 s₁ := fun b hb => by
      rw [hv₁ b hb, VG.Proof.Aes.X86_64.AesNi.pxor_st _ _ (roundKey w 0) (by rw [hK.sched, VG.Proof.Aes.X86_64.AesNi.ea_at]; exact k0), VG.Proof.Aes.X86_64.AesNi.rnds_zero]
    exact WP.mono (VG.Proof.Aes.X86_64.AesNi.rounds_ok regs hnd h8 9 s₁ (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  -- Rounds 10 to `nr - 1`.
  have h₂ : ∀ s₁, VG.Proof.Aes.X86_64.AesNi.RInv regs w x 9 s₁ → VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm8 :: regs) s s₁ →
      s₁.zf = some (BitVec.ofNat 64 nr - (10 : BitVec 32).signExtend 64 == 0) →
      WP isa (.ite .e (.block [])
        (.seq (.block (round regs 10 ++ round regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (round regs 12 ++ round regs 13))))) s₁ fun s' =>
        VG.Proof.Aes.X86_64.AesNi.RInv regs w x (nr - 1) s' ∧ VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm8 :: regs) s s' := by
    intro s₁ hI₁ hf₁ hz₁
    have hK₁ := hK.of_frame hf₁
    have hrsi₁ : s₁.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁, hf₁⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      rw [WP.block_append_iff, WP.block_append_iff]
      refine WP.mono (VG.Proof.Aes.X86_64.AesNi.round_ok regs hnd h8 (k := 9) (by omega) hK₁ hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
      refine WP.mono (VG.Proof.Aes.X86_64.AesNi.round_ok regs hnd h8 (k := 10) (by omega) (hK₁.of_frame hf₂) hI₂)
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      have hrsi₃ : s₃.gpr .rsi = s₁.gpr .rsi := by rw [hf₃.gpr, hf₂.gpr]
      refine WP.mono (VG.Proof.Aes.X86_64.AesNi.cmpRsi_ok s₃ 12 _ (hrsi₃.trans hrsi₁)) fun s₄ ⟨hz₄, hf₄⟩ => ?_
      have hf₁₄ := hf₁.trans (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
    · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil
        ⟨fun b hb => by rw [hf₄.xmm b (by simp)]; exact hI₃ b hb, hf₁₄⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
      rw [WP.block_append_iff]
      have hK₄ := hK₁.of_frame (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
      have hI₄ : VG.Proof.Aes.X86_64.AesNi.RInv regs w x 11 s₄ := fun b hb => by rw [hf₄.xmm b (by simp)]; exact hI₃ b hb
      refine WP.mono (VG.Proof.Aes.X86_64.AesNi.round_ok regs hnd h8 (k := 11) (by omega) hK₄ hI₄) fun s₅ ⟨hI₅, hf₅⟩ => ?_
      exact WP.mono (VG.Proof.Aes.X86_64.AesNi.round_ok regs hnd h8 (k := 12) (by omega) (hK₄.of_frame hf₅) hI₅)
        fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁₄.trans (hf₅.trans hf')⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  refine WP.seq (WP.mono (h₂ s₁' (fun b hb => by rw [hf₁'.xmm b (by simp)]; exact hI₁ b hb) hf₁₁ hz₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  have hea : s₂.ea (at_ .r10 0) = s₂.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [VG.Proof.Aes.X86_64.AesNi.ea_at, hf₂.gpr, hr10, VG.Proof.Aes.X86_64.AesNi.ofInt_natCast, VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]; exact BitVec.add_zero _
  have hK₂ := hK.of_frame hf₂
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.keyOp_ok regs .aesenclast _ s₂ hnd h8 (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans hf'⟩
  rw [hv b hb, VG.Proof.Aes.X86_64.AesNi.aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact VG.Proof.Aes.X86_64.AesNi.byte_roundKey _ _ (by omega)), hI₂ b hb, VG.Proof.Aes.X86_64.AesNi.cipher_eq]
end VG.Proof.Aes.X86_64.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32`. -/
section

section

/-!
# AES-NI counter mode: the counter blocks and the data

`ctrs_ok`: `ctrs regs` puts the counter blocks `CB`, `inc₃₂(CB)`, … into the
registers `regs`, as bytes; `xorData_ok`: `xorData regs j` XORs the registers
into the data blocks `j`, `j + 1`, …; both for any list of registers, by
induction.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ ctrs xorData)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-- `xmm11`: 1 in doubleword 0. -/
abbrev one : BitVec 128 := (0 : BitVec 64) ++ (1 : BitVec 64)

theorem paddd_one (c : VG.Spec.Gcm.Block) : XBinOp.eval .paddd c VG.Proof.Aes.X86_64.AesNi.one = inc32 c := by
  have z : ∀ x : BitVec 32, x + 0 = x := fun x => BitVec.add_zero x
  have e0 : dword VG.Proof.Aes.X86_64.AesNi.one 0 = 1 := by decide
  have e1 : dword VG.Proof.Aes.X86_64.AesNi.one 1 = 0 := by decide
  have e2 : dword VG.Proof.Aes.X86_64.AesNi.one 2 = 0 := by decide
  have e3 : dword VG.Proof.Aes.X86_64.AesNi.one 3 = 0 := by decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, e0, e1, e2, e3, z, getLsbD_ofDwords, getLsbD_dword, inc32,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  first
  | rfl
  | exact congrArg _ (by omega)

theorem rep_succ' {α : Type} (f : α → α) (a : α) : ∀ k, Nat.repeat f k (f a) = Nat.repeat f (k + 1) a
  | 0 => rfl
  | k + 1 => congrArg f (VG.Proof.Aes.X86_64.AesNi.rep_succ' f a k)

theorem rep_add {α : Type} (f : α → α) (a : α) (i : Nat) :
    ∀ k, Nat.repeat f k (Nat.repeat f i a) = Nat.repeat f (i + k) a
  | 0 => rfl
  | k + 1 => congrArg f (VG.Proof.Aes.X86_64.AesNi.rep_add f a i k)

/-- One counter block into `b`. -/
theorem ctr1_ok (b : XReg) (s : State) (h9 : b ≠ .xmm9) (h10 : b ≠ .xmm10) (h11 : b ≠ .xmm11)
    (hr : s.xmm .xmm10 = revMask) (ho : s.xmm .xmm11 = VG.Proof.Aes.X86_64.AesNi.one) :
    WP isa (.block [.xop (.bin .movdqa b .xmm9), .xop (.bin .pshufb b .xmm10),
        .xop (.bin .paddd .xmm9 .xmm11)]) s fun s' =>
      s'.xmm b = XBinOp.eval .pshufb (s.xmm .xmm9) revMask ∧ s'.xmm .xmm9 = inc32 (s.xmm .xmm9) ∧
      VG.Proof.Aes.X86_64.AesNi.XFrame [b, .xmm9] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_movdqa, h9, Ne.symm h9, Ne.symm h10,
    Ne.symm h11, hr, ho, VG.Proof.Aes.X86_64.AesNi.paddd_one,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

theorem ctrs_ok (regs : List XReg) (s : State) (hnd : regs.Nodup)
    (hx : ∀ r ∈ regs, r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm11)
    (hr : s.xmm .xmm10 = revMask) (ho : s.xmm .xmm11 = VG.Proof.Aes.X86_64.AesNi.one) :
    WP isa (.block (ctrs regs)) s fun s' =>
      (∀ k (h : k < regs.length),
        s'.xmm regs[k] = XBinOp.eval .pshufb (Nat.repeat inc32 k (s.xmm .xmm9)) revMask) ∧
      s'.xmm .xmm9 = Nat.repeat inc32 regs.length (s.xmm .xmm9) ∧ VG.Proof.Aes.X86_64.AesNi.XFrame (.xmm9 :: regs) s s' := by
  induction regs generalizing s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, XFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨h9, h10, h11⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.ctr1_ok b s h9 h10 h11 hr ho) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      (by rw [f₁.xmm _ (by simp [Ne.symm h10])]; exact hr)
      (by rw [f₁.xmm _ (by simp [Ne.symm h11])]; exact ho)) fun s' ⟨e, c, f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [f.xmm _ (by simp [h9, hbs]), e₁]; rfl
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk), c₁, VG.Proof.Aes.X86_64.AesNi.rep_succ']
    · rw [c, c₁, VG.Proof.Aes.X86_64.AesNi.rep_succ', List.length_cons]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-! ## The data -/

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem blockAt_writeW_sep (m : Mem) {p q : Addr} (v : BitVec 128) (h : Mem.Sep q 16 p 16) :
    VG.Spec.Gcm.blockAt (m.writeW p v) q = VG.Spec.Gcm.blockAt m q := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_sep h (by decide)]

/-- The block at `p` after XORing `x` (as bytes) into it. -/
theorem blockAt_writeW_xor (m : Mem) (p : Addr) (x : BitVec 128) :
    VG.Spec.Gcm.blockAt (m.writeW p (XBinOp.eval .pxor x (m.readW p 128))) p =
      VG.Spec.Gcm.blockAt m p ^^^ XBinOp.eval .pshufb x revMask := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_self m p 16 _ (by decide), VG.Proof.Aes.X86_64.AesNi.eval_pxor,
    pshufb_rev_xor, BitVec.xor_comm]

/-- A block of a region disjoint from the frame's is unchanged. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : VG.Spec.Gcm.blockAt m' p = VG.Spec.Gcm.blockAt m p :=
  Proof.Gcm.blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem inRegions_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- XOR `b` into the block at `rcx + d`. -/
theorem xor1_ok (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ .xmm8)
    (hin : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad .xmm8 (at_ .rcx d), .xop (.bin .pxor b .xmm8),
        .movdquStore (at_ .rcx d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 (d : Int))
        (XBinOp.eval .pxor (s.xmm b) (s.mem.readW (s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm8 → s'.xmm r = s.xmm r) := by
  have hin' := VG.Proof.Aes.X86_64.AesNi.inRegions_wr hin
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, State.store128, VG.Proof.Aes.X86_64.AesNi.ea_at, hin, hin', hb8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩

theorem xorData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hw : (s.gpr .rcx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), VG.Spec.Gcm.blockAt s'.mem (s.gpr .rcx + BitVec.ofNat 64 (16 * (j + k))) =
        VG.Spec.Gcm.blockAt s.mem (s.gpr .rcx + BitVec.ofNat 64 (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.xmm regs[k]) revMask) ∧
      Frame [⟨s.gpr .rcx + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm8 → r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : .xmm8 ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hw
    rw [xorData, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.xor1_ok b (16 * j) s hb8 hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrcx : s₁.gpr .rcx = s.gpr .rcx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8' (fun k hk => by
        rw [wr₁, hrcx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrcx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrcx] at hb hf
    have ofs : ∀ a : Nat, (s.gpr .rcx + BitVec.ofInt 64 (a : Int)) = s.gpr .rcx + BitVec.ofNat 64 a :=
      fun a => by rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]
    rw [ofs] at m₁
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ r ∈ [(⟨s.gpr .rcx + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .rcx + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [VG.Proof.Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .rcx).isLt
      omega
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf hdj, m₁, VG.Proof.Aes.X86_64.AesNi.blockAt_writeW_xor]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', m₁, VG.Proof.Aes.X86_64.AesNi.blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [VG.Proof.Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr .rcx).isLt
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk'))]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rcx + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [VG.Proof.Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .rcx).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2, x₁ r hr'.1 hr]

end VG.Proof.Aes.X86_64.AesNi

end

/-!
# AES-NI counter mode: the whole function

`ctr32_verified` proves `Impl.Aes.X86_64.AesNi.ctr32` against `ctr32X86_64`.
The loops keep, after `c` blocks, the counter block `inc₃₂ᶜ(CB)` in `xmm9` and
the first `c` data blocks encrypted; the eight-block and one-block bodies are
the same code for different lists of registers (`blocks_ok`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ ctrs xorData aes regs8 body8 body1 ctrLoad ctrStore ctrTail ctr32)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq blockAt_store)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev sp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev cp : Addr := s₀.gpr .rdx
abbrev dp : Addr := s₀.gpr .rcx
abbrev nb : Nat := (s₀.gpr .r8).toNat
abbrev sR : Region := ⟨VG.Proof.Aes.X86_64.AesNi.sp s₀, 240⟩
abbrev cR : Region := ⟨VG.Proof.Aes.X86_64.AesNi.cp s₀, 16⟩
abbrev dR : Region := ⟨VG.Proof.Aes.X86_64.AesNi.dp s₀, 16 * VG.Proof.Aes.X86_64.AesNi.nb s₀⟩
abbrev scrR : Region := ⟨s₀.gpr .r9, 2048⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (VG.Proof.Aes.X86_64.AesNi.sp s₀) (16 * (VG.Proof.Aes.X86_64.AesNi.nr s₀ + 1))
/-- `CIPH_K`. -/
abbrev ciph : VG.Spec.Gcm.Block → VG.Spec.Gcm.Block := VG.Spec.Gcm.aesWith (VG.Proof.Aes.X86_64.AesNi.nr s₀) (VG.Proof.Aes.X86_64.AesNi.sch s₀)
abbrev cb : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (VG.Proof.Aes.X86_64.AesNi.cp s₀)
/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := VG.Proof.Aes.X86_64.AesNi.dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (VG.Proof.Aes.X86_64.AesNi.bAddr s₀ k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Aes.X86_64.AesNi.sR s₀]
  wr : s₀.wr = [VG.Proof.Aes.X86_64.AesNi.cR s₀, VG.Proof.Aes.X86_64.AesNi.dR s₀, VG.Proof.Aes.X86_64.AesNi.scrR s₀]
  s_c : (VG.Proof.Aes.X86_64.AesNi.sR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.cR s₀)
  s_d : (VG.Proof.Aes.X86_64.AesNi.sR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.dR s₀)
  s_scr : (VG.Proof.Aes.X86_64.AesNi.sR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.scrR s₀)
  c_d : (VG.Proof.Aes.X86_64.AesNi.cR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.dR s₀)
  c_scr : (VG.Proof.Aes.X86_64.AesNi.cR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.scrR s₀)
  d_scr : (VG.Proof.Aes.X86_64.AesNi.dR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.scrR s₀)
  ret_c : (VG.Proof.Aes.X86_64.AesNi.retR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.cR s₀)
  ret_d : (VG.Proof.Aes.X86_64.AesNi.retR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.dR s₀)
  ret_scr : (VG.Proof.Aes.X86_64.AesNi.retR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.scrR s₀)
  wrap : (VG.Proof.Aes.X86_64.AesNi.dp s₀).toNat + 16 * VG.Proof.Aes.X86_64.AesNi.nb s₀ ≤ 2 ^ 64
  rounds : VG.Proof.Aes.X86_64.AesNi.nr s₀ = 10 ∨ VG.Proof.Aes.X86_64.AesNi.nr s₀ = 12 ∨ VG.Proof.Aes.X86_64.AesNi.nr s₀ = 14

theorem pre_of (s₀ : State) (h : ctr32X86_64.pre s₀) : VG.Proof.Aes.X86_64.AesNi.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀)
include hp

theorem keys (j : Nat) (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Aes.X86_64.AesNi.sp s₀ + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 :=
  ⟨VG.Proof.Aes.X86_64.AesNi.sR s₀, by simp [hp.rd], by rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]; exact VG.Proof.Aes.X86_64.AesNi.contains_offset (by omega) (by omega)⟩

/-- Block `k` is in the data. -/
theorem in_blk {k : Nat} (hk : k < VG.Proof.Aes.X86_64.AesNi.nb s₀) : (VG.Proof.Aes.X86_64.AesNi.dR s₀).Contains (VG.Proof.Aes.X86_64.AesNi.bAddr s₀ k) 16 :=
  VG.Proof.Aes.X86_64.AesNi.contains_offset (by omega) (by have := hp.wrap; omega)

theorem out_blk {k : Nat} (hk : k < VG.Proof.Aes.X86_64.AesNi.nb s₀) : InRegions s₀.wr (VG.Proof.Aes.X86_64.AesNi.bAddr s₀ k) 16 :=
  ⟨VG.Proof.Aes.X86_64.AesNi.dR s₀, by simp [hp.wr], hp.in_blk hk⟩

/-- Memory that the data does not overlap. -/
theorem sch_frame {m : Mem} (hf : Frame [VG.Proof.Aes.X86_64.AesNi.dR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (VG.Proof.Aes.X86_64.AesNi.sp s₀) (16 * (VG.Proof.Aes.X86_64.AesNi.nr s₀ + 1)) = VG.Proof.Aes.X86_64.AesNi.sch s₀ := by
  have hn : 16 * (VG.Proof.Aes.X86_64.AesNi.nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [VG.Proof.Aes.X86_64.AesNi.sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨VG.Proof.Aes.X86_64.AesNi.sp s₀, 16 * (VG.Proof.Aes.X86_64.AesNi.nr s₀ + 1)⟩) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.s_d.sub_left (Region.sub_prefix hn)) (by show 16 * (VG.Proof.Aes.X86_64.AesNi.nr s₀ + 1) ≤ 2 ^ 64; omega) hi

end Pre

/-! ## The loop invariant -/

/-- After `c` blocks, with `rcx` and `r8` at block `p`. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ VG.Proof.Aes.X86_64.AesNi.nb s₀
  x9 : s.xmm .xmm9 = Nat.repeat inc32 c (VG.Proof.Aes.X86_64.AesNi.cb s₀)
  x10 : s.xmm .xmm10 = revMask
  x11 : s.xmm .xmm11 = VG.Proof.Aes.X86_64.AesNi.one
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  r10 : s.gpr .r10 = VG.Proof.Aes.X86_64.AesNi.sp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86_64.AesNi.nr s₀)
  rcx : s.gpr .rcx = VG.Proof.Aes.X86_64.AesNi.bAddr s₀ p
  r8 : s.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.nb s₀ - p)
  frame : Frame [VG.Proof.Aes.X86_64.AesNi.dR s₀] s₀.mem s.mem
  blocks : ∀ k < VG.Proof.Aes.X86_64.AesNi.nb s₀,
    VG.Spec.Gcm.blockAt s.mem (VG.Proof.Aes.X86_64.AesNi.bAddr s₀ k) = if k < c then VG.Proof.Aes.X86_64.AesNi.blk s₀ k ^^^ VG.Proof.Aes.X86_64.AesNi.ciph s₀ (Nat.repeat inc32 k (VG.Proof.Aes.X86_64.AesNi.cb s₀))
      else VG.Proof.Aes.X86_64.AesNi.blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem regs_nodup (rs : List XReg) (h : rs = regs8 ∨ rs = [.xmm0]) :
    rs.Nodup ∧ .xmm8 ∉ rs ∧ ∀ r ∈ rs, r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm11 := by
  rcases h with rfl | rfl <;> decide

/-- Blocks `c … c + n − 1` of the data are in the data. -/
theorem run_in {d a : Addr} {nb c n : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hc : c + n ≤ nb)
    (ha : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : (a - d).toNat < 16 * nb := by
  rw [VG.Proof.Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at ha
  have := (a - d).isLt
  omega

/-- Block `k` of the data is not in blocks `c … c + n − 1`. -/
theorem run_sep {d a : Addr} {nb c n k : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hk : k < nb)
    (hc : c + n ≤ nb) (hn : ¬ (c ≤ k ∧ k < c + n))
    (h₁ : (a - (d + BitVec.ofNat 64 (16 * k))).toNat < 16)
    (h₂ : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : False := by
  rw [VG.Proof.Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at h₁ h₂
  have := (a - d).isLt
  omega

/-- The counter blocks, AES and the XOR into the data, for the blocks
`c … c + N - 1` (`N` the number of registers). -/
theorem blocks_ok {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) (rs : List XReg) (hrs : rs = regs8 ∨ rs = [.xmm0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ VG.Proof.Aes.X86_64.AesNi.nb s₀) {s : State}
    (hI : VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s) (hQ : ∀ s', VG.Proof.Aes.X86_64.AesNi.Inv s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrs rs)) (.seq (VG.Impl.Aes.X86_64.AesNi.aes rs) (.block (xorData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h8, hx⟩ := VG.Proof.Aes.X86_64.AesNi.regs_nodup rs hrs
  have hlen : 0 < rs.length := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.wrap
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.ctrs_ok rs s hnd hx hI.x10 hI.x11) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  rw [hI.x9, VG.Proof.Aes.X86_64.AesNi.rep_add] at c₁
  have ek : ∀ k (h : k < rs.length),
      s₁.xmm rs[k] = XBinOp.eval .pshufb (Nat.repeat inc32 (c + k) (VG.Proof.Aes.X86_64.AesNi.cb s₀)) revMask := by
    intro k h; rw [e₁ k h, hI.x9, VG.Proof.Aes.X86_64.AesNi.rep_add]
  have hg₁ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → s₁.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 => by rw [f₁.gpr, hI.gpr r h1 h2 h3 h4]
  have hK : VG.Proof.Aes.X86_64.AesNi.Keys (VG.Proof.Aes.X86_64.AesNi.nr s₀) (VG.Proof.Aes.X86_64.AesNi.sch s₀) s₁ :=
    ⟨by rw [f₁.mem, f₁.gpr, hI.gpr .rdi (by decide) (by decide) (by decide) (by decide),
        hp.sch_frame hI.frame],
      by rcases hp.rounds with h | h | h <;> omega,
      fun j hj => by
        rw [f₁.rd, f₁.wr, f₁.gpr, hI.rd, hI.wr, hI.gpr .rdi (by decide) (by decide) (by decide)
          (by decide)]
        exact hp.keys j (by rcases hp.rounds with h | h | h <;> omega)⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.aes_ok rs hnd h8 hp.rounds s₁ hK
    (by rw [hg₁ .rsi (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [f₁.gpr, hI.r10, hI.gpr .rdi (by decide) (by decide) (by decide) (by decide)]))
    fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s₂.xmm rs[k]) revMask =
      VG.Proof.Aes.X86_64.AesNi.ciph s₀ (Nat.repeat inc32 (c + k) (VG.Proof.Aes.X86_64.AesNi.cb s₀)) := fun k h =>
    (VG.Proof.Aes.X86_64.AesNi.aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h), ek k h])).symm
  have hrcx₂ : s₂.gpr .rcx = VG.Proof.Aes.X86_64.AesNi.bAddr s₀ c := by rw [f₂.gpr, f₁.gpr, hI.rcx]
  have hrcxN : (s₂.gpr .rcx).toNat = (VG.Proof.Aes.X86_64.AesNi.dp s₀).toNat + 16 * c := by
    rw [hrcx₂, VG.Proof.Aes.X86_64.AesNi.bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have addr : ∀ k, s₂.gpr .rcx + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int) = VG.Proof.Aes.X86_64.AesNi.bAddr s₀ (c + k) :=
    fun k => by
      rw [hrcx₂, VG.Proof.Aes.X86_64.AesNi.ofInt_natCast, VG.Proof.Aes.X86_64.AesNi.bAddr, VG.Proof.Aes.X86_64.AesNi.bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  have addr' : ∀ k, s₂.gpr .rcx + BitVec.ofNat 64 (16 * (0 + k)) = VG.Proof.Aes.X86_64.AesNi.bAddr s₀ (c + k) :=
    fun k => by rw [← addr, VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.xorData_ok rs 0 s₂ hnd h8 (fun k hk => by
      rw [addr, f₂.wr, f₁.wr, hI.wr]; exact hp.out_blk (by omega)) (by rw [hrcxN]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂] at b₃ fr₃
  rw [hrcx₂, Nat.mul_zero, BitVec.add_zero] at fr₃
  simp only [addr'] at b₃
  have kx : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → r ∉ rs → s₃.xmm r = s.xmm r := fun r h8' h9 hr => by
    rw [x₃ r h8' hr, f₂.xmm r (by simp [h8', hr]), f₁.xmm r (by simp [h9, hr])]
  refine ⟨Nat.le_trans (by omega) hc, ?_, ?_, ?_, fun r h1 h2 h3 h4 => by rw [g₃, f₂.gpr, hg₁ r h1 h2 h3 h4], ?_,
    by rw [g₃, hrcx₂], by rw [g₃, f₂.gpr, f₁.gpr, hI.r8], ?_, ?_, by rw [rd₃, f₂.rd, f₁.rd, hI.rd],
    by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩
  · rw [x₃ _ (by decide) (fun h => (hx _ h).1 rfl), f₂.xmm _ (by
      simp only [List.mem_cons, not_or]; exact ⟨by decide, fun h => (hx _ h).1 rfl⟩), c₁]
  · rw [kx _ (by decide) (by decide) (fun h => (hx _ h).2.1 rfl), hI.x10]
  · rw [kx _ (by decide) (by decide) (fun h => (hx _ h).2.2 rfl), hI.x11]
  · rw [g₃, f₂.gpr, f₁.gpr, hI.r10]
  · -- The data written is only in the data.
    refine hI.frame.trans (fr₃.sub fun r hr => ⟨VG.Proof.Aes.X86_64.AesNi.dR s₀, List.mem_singleton_self _, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + rs.length) → VG.Spec.Gcm.blockAt s₃.mem (VG.Proof.Aes.X86_64.AesNi.bAddr s₀ k) = VG.Spec.Gcm.blockAt s.mem (VG.Proof.Aes.X86_64.AesNi.bAddr s₀ k) :=
      fun hn => VG.Proof.Aes.X86_64.AesNi.blockAt_frame fr₃ fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + rs.length by omega, ite_true]
    · by_cases hhi : k < c + rs.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
        have hj : j < rs.length := by omega
        rw [b₃ j hj, hI.blocks _ hk, ks j hj]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem nb_lt {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) : 16 * VG.Proof.Aes.X86_64.AesNi.nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

/-- The eight-block body. -/
theorem body8_ok {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) {c : Nat} (hc : c + 8 ≤ VG.Proof.Aes.X86_64.AesNi.nb s₀) {s : State}
    (hI : VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s) :
    WP isa body8 s fun s' => VG.Proof.Aes.X86_64.AesNi.Inv s₀ (c + 8) (c + 8) s' ∧ s'.cf = some (decide (VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 8) < 8)) := by
  have hn := VG.Proof.Aes.X86_64.AesNi.nb_lt hp
  refine VG.Proof.Aes.X86_64.AesNi.blocks_ok hp regs8 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hrcx := hI₁.rcx
  have hr8 := hI₁.r8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_true, ite_false, e128, e8, hrcx, hr8,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c) - 8 = BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 8)) := by
    have := (s₀.gpr .r8).isLt; bv_omega
  refine ⟨{ hI₁ with
    gpr := fun r h1 h2 h3 h4 => by simp [h2, h3, hI₁.gpr r h1 h2 h3 h4]
    r10 := by simp [hI₁.r10]
    rcx := by simp (config := {decide := true}) only [VG.Proof.Aes.X86_64.AesNi.bAddr, ite_false, ite_true]; bv_omega
    r8 := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 8) < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The one-block body. -/
theorem body1_ok {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) {c : Nat} (hc : c < VG.Proof.Aes.X86_64.AesNi.nb s₀) {s : State}
    (hI : VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s) :
    WP isa body1 s fun s' => VG.Proof.Aes.X86_64.AesNi.Inv s₀ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 1) = 0)) := by
  have hn := VG.Proof.Aes.X86_64.AesNi.nb_lt hp
  refine VG.Proof.Aes.X86_64.AesNi.blocks_ok hp [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrcx := hI₁.rcx
  have hr8 := hI₁.r8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, ite_false, e16, e1, hrcx, hr8,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c) - 1 = BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 1)) := by
    have := (s₀.gpr .r8).isLt; bv_omega
  refine ⟨{ hI₁ with
    gpr := fun r h1 h2 h3 h4 => by simp [h2, h3, hI₁.gpr r h1 h2 h3 h4]
    r10 := by simp [hI₁.r10]
    rcx := by simp (config := {decide := true}) only [VG.Proof.Aes.X86_64.AesNi.bAddr, ite_false, ite_true]; bv_omega
    r8 := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  rw [hsub, VG.Proof.Aes.X86_64.AesNi.beq_ofNat_zero (by omega)]

/-! ## The prologue and the epilogue -/

theorem ctrLoad_ok {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) :
    WP isa (.block ctrLoad) s₀ fun s => VG.Proof.Aes.X86_64.AesNi.Inv s₀ 0 0 s ∧ s.cf = some (decide (VG.Proof.Aes.X86_64.AesNi.nb s₀ < 8)) := by
  have hin : InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Aes.X86_64.AesNi.cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨VG.Proof.Aes.X86_64.AesNi.cR s₀, by simp [hp.wr], by rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]; exact VG.Proof.Aes.X86_64.AesNi.contains_offset (by omega) (by omega)⟩
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  apply WP.of_runBlock
  simp only [ctrLoad, Impl.Aes.X86_64.AesNi.const, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setXmm, State.setReg, State.load128,
    VG.Proof.Aes.X86_64.AesNi.ea_at, hin, ite_true, ite_false, movq_const, e8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨Nat.zero_le _, ?_, rfl, rfl, fun r h1 h2 h3 h4 => by simp [h1, h4], ?_, ?_, ?_,
    Frame.refl _ _, fun k _ => by simp, rfl, rfl⟩, ?_⟩ <;>
    try simp (config := {decide := true}) only [ite_true, ite_false]
  · rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]
    simp only [BitVec.add_zero]
    exact (blockAt_eq _ _).symm
  · simp only [VG.Proof.Aes.X86_64.AesNi.nr, VG.Proof.Aes.X86_64.AesNi.sp]; bv_omega
  · simp [VG.Proof.Aes.X86_64.AesNi.bAddr]
  · simp [VG.Proof.Aes.X86_64.AesNi.nb]
  · simp

theorem test_ok {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) {c : Nat} {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s) :
    WP isa (.block [.alu .test .r8 (.reg .r8)]) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s' ∧ s'.zf = some (decide (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c = 0)) := by
  have hn := VG.Proof.Aes.X86_64.AesNi.nb_lt hp
  have hr8 := hI.r8
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hr8, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with }, by rw [VG.Proof.Aes.X86_64.AesNi.beq_ofNat_zero (by omega)]⟩

theorem ctrStore_ok {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.Inv s₀ (VG.Proof.Aes.X86_64.AesNi.nb s₀) (VG.Proof.Aes.X86_64.AesNi.nb s₀) s) :
    WP isa (.block ctrStore) s fun s' => gprPreserved s₀ s' ∧ ctr32X86_64.post s₀ s' := by
  have hrdx : s.gpr .rdx = VG.Proof.Aes.X86_64.AesNi.cp s₀ := hI.gpr .rdx (by decide) (by decide) (by decide) (by decide)
  have hout : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨VG.Proof.Aes.X86_64.AesNi.cR s₀, by simp [hI.wr, hp.wr], by
      rw [hrdx, VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]; exact VG.Proof.Aes.X86_64.AesNi.contains_offset (by omega) (by omega)⟩
  have h10 := hI.x10
  have h9 := hI.x9
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ctrStore, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, VG.Proof.Aes.X86_64.AesNi.ea_at, hout, ite_true, h10, h9,
    Option.some.injEq, exists_eq_left']
  rw [hrdx, VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have sep : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86_64.AesNi.cR s₀) → ∀ {a : Addr} {n : Nat}, r.Contains a n →
      Mem.Sep a n (VG.Proof.Aes.X86_64.AesNi.cp s₀) 16 := fun h _ _ ha => h.sep ha (Region.contains_self _ _)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [Mem.readW_writeW_sep (sep hp.ret_c (Region.contains_self _ _)) (by decide),
      hI.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_d) (by decide)]
  · apply List.ext_getElem
    · simp [VG.Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
    · intro k h₁ h₂
      have hk : k < VG.Proof.Aes.X86_64.AesNi.nb s₀ := by simpa [VG.Spec.Gcm.blocksAt] using h₁
      have := hI.blocks k hk
      simp only [hk, ite_true] at this
      simp only [VG.Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map, List.getElem_range,
        List.getElem_zipWith, List.length_map, List.length_range]
      rw [VG.Proof.Aes.X86_64.AesNi.blockAt_writeW_sep _ _ (by
        refine sep (hp.c_d.symm) ?_
        exact hp.in_blk hk), this]
  · exact blockAt_store _ _ _

/-! ## The whole function -/

/-- The blocks left after `c`, eight and then one at a time, and the counter
stored: what follows `ctrLoad` here, and the sixteen-block loop of
`vg_aes_ctr32_vaes`. -/
theorem tail_ok {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) {c₀ : Nat} {s₁ : State} (hI₁ : VG.Proof.Aes.X86_64.AesNi.Inv s₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c₀ < 8))) :
    WP isa ctrTail s₁ fun s' => gprPreserved s₀ s' ∧ ctr32X86_64.post s₀ s' := by
  have hn := VG.Proof.Aes.X86_64.AesNi.nb_lt hp
  refine WP.seq (WP.mono (Q := fun s => ∃ c, VG.Proof.Aes.X86_64.AesNi.nb s₀ - c < 8 ∧ VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c₀ < 8)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.X86_64.AesNi.nb s₀ - c ∧ c + 8 ≤ VG.Proof.Aes.X86_64.AesNi.nb s₀ ∧ VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa body8 s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, VG.Proof.Aes.X86_64.AesNi.nb s₀ - c < 8 ∧ VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (VG.Proof.Aes.X86_64.AesNi.body8_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.X86_64.AesNi.Inv s₀ (VG.Proof.Aes.X86_64.AesNi.nb s₀) (VG.Proof.Aes.X86_64.AesNi.nb s₀)) ?_ fun s₄ hI₄ => VG.Proof.Aes.X86_64.AesNi.ctrStore_ok hp hI₄)
  refine WP.ite (decide (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = VG.Proof.Aes.X86_64.AesNi.nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.X86_64.AesNi.nb s₀ - c ∧ c < VG.Proof.Aes.X86_64.AesNi.nb s₀ ∧ VG.Proof.Aes.X86_64.AesNi.Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa body1 s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Aes.X86_64.AesNi.Inv s₀ (VG.Proof.Aes.X86_64.AesNi.nb s₀) (VG.Proof.Aes.X86_64.AesNi.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (VG.Proof.Aes.X86_64.AesNi.body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 1) = 0
      · have : c + 1 = VG.Proof.Aes.X86_64.AesNi.nb s₀ := by omega
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], VG.Proof.Aes.X86_64.AesNi.nb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < VG.Proof.Aes.X86_64.AesNi.nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (VG.Proof.Aes.X86_64.AesNi.nb s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

theorem correct {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Pre s₀) :
    WP isa ctr32 s₀ fun s' => gprPreserved s₀ s' ∧ ctr32X86_64.post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.ctrLoad_ok hp) fun _ ⟨hI₁, hcf⟩ => VG.Proof.Aes.X86_64.AesNi.tail_ok hp hI₁ (by simpa using hcf))

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000
    | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : ctr32X86_64.pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ ctr32X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Aes.X86_64.AesNi.correct (VG.Proof.Aes.X86_64.AesNi.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem ctr32_ct : ConstantTime isa ctr32X86_64.pre ctr32X86_64.pub ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.ctr32 (Spec.Gcm.ctr32Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.Aes.X86_64.AesNi.ctr32_correct VG.Proof.Aes.X86_64.AesNi.ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.X86_64.AesNi.ctr32X86_64,
      X86_64.abi, X86_64.argRegs] [Proof.Aes.X86_64.AesNi.satState] using
      Proof.Aes.X86_64.AesNi.satState)

end VG.Proof.Aes.X86_64.AesNi

end
