module

public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Ecb
public import VerifiedGarbage.Impl.TripleDes.Arm.Wide
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Triple DES-CBC and -CFB64 decryption on ARMv7, a batch at a time: the batches

Blocks as pairs of little-endian words (`wb`), which the code loads, XORs
and stores: the bitsliced kernel takes the block of the state words `b` and
`32 + b` to its encryption or decryption (`kernel_block`). `cbcBatch_ok`
and `cfbBatch_ok`: a batch of `k = min(n, 32)` blocks becomes what CBC or
CFB decryption makes of it from the chaining value, which becomes the
batch's last ciphertext block.
-/

-- separate module: builds in parallel with `FunctionsLit`, which `WideVerified` evaluates and this does not import

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

open VG VG.Arm VG.Arm.Straight VG.Spec.TripleDes VG.Impl.TripleDes.Arm.Bitslice VG.Impl.TripleDes.Arm.Wide
open VG.Proof.TripleDes.Bitslice (tdeaW blockOut wAt)
open VG.Proof.X25519.Arm (dpVal op2_imm op2_reg)

/-! ## Blocks as pairs of words -/

/-- A memory whose first two words are `lo` and `hi`. -/
def wordsMem (lo hi : BitVec 32) : Mem :=
  Mem.writeW (Mem.writeW (fun _ => 0) 0 lo) (0 + BitVec.ofNat 64 4) hi

/-- The block whose little-endian words are `lo` and `hi`. -/
def wb (lo hi : BitVec 32) : Block := blockAt (wordsMem lo hi) 0

theorem wordsMem_lo (lo hi : BitVec 32) : (wordsMem lo hi).readW 0 32 = lo := by
  have h := Offset.sep (0 : Addr) (d := 0) (n := 4) (e := 4) (k := 4) (by decide) (by decide) (by decide)
  rw [BitVec.add_zero] at h
  rw [wordsMem, Mem.readW_writeW_sep (w := 32) (w' := 32) h (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

theorem wordsMem_hi (lo hi : BitVec 32) : (wordsMem lo hi).readW (0 + BitVec.ofNat 64 4) 32 = hi :=
  Mem.readW_writeW_self32 _ _ _

/-- Byte `r` of the bytes `lo` and `hi` are the words of. -/
def wbyte (lo hi : BitVec 32) (r : Nat) : Byte :=
  if r < 4 then lo.extractLsb' (8 * r) 8 else hi.extractLsb' (8 * (r - 4)) 8

/-- A byte of a block, from its words. -/
theorem block_byte (m : Mem) (p : Addr) {r : Nat} (hr : r < 8) :
    m (p + BitVec.ofNat 64 r) = wbyte (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32) r := by
  unfold wbyte
  by_cases h : r < 4
  · rw [ite_eq_left h]; exact Mem.readW_byte m p h
  · rw [ite_eq_right h, ← Mem.readW_byte m (p + BitVec.ofNat 64 4) (i := r - 4) (by omega_using [hr]),
      Offset.add_add, show 4 + (r - 4) = r by omega_using [h]]

/-- Byte `r` of a block. -/
def bbyte (B : Block) (r : Nat) : Byte := B.toList.getD r 0

theorem bbyte_blockAt (m : Mem) (p : Addr) {r : Nat} (hr : r < 8) :
    bbyte (blockAt m p) r = m (p + BitVec.ofNat 64 r) := by
  simp [bbyte, blockAt, List.getD_eq_getElem?_getD, hr]

theorem bbyte_wb (lo hi : BitVec 32) {r : Nat} (hr : r < 8) : bbyte (wb lo hi) r = wbyte lo hi r := by
  rw [wb, bbyte_blockAt _ _ hr, block_byte (wordsMem lo hi) 0 hr, wordsMem_lo, wordsMem_hi]

/-- A block is that of its words. -/
theorem blockAt_wb (m : Mem) (p : Addr) : blockAt m p = wb (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32) := by
  apply Vector.ext
  intro i hi
  have e₁ : (blockAt m p)[i] = m (p + BitVec.ofNat 64 i) := by simp [blockAt]
  have e₂ : (wb (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32))[i] =
      wordsMem (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32) (0 + BitVec.ofNat 64 i) := by
    simp [wb, blockAt]
  rw [e₁, e₂, block_byte m p hi, block_byte (wordsMem _ _) 0 hi, wordsMem_lo, wordsMem_hi]

/-- The words' XOR is the blocks'. -/
theorem bbyte_wb_xor (a b c d : BitVec 32) {r : Nat} (hr : r < 8) :
    bbyte (wb (a ^^^ c) (b ^^^ d)) r = bbyte (wb a b) r ^^^ bbyte (wb c d) r := by
  rw [bbyte_wb _ _ hr, bbyte_wb _ _ hr, bbyte_wb _ _ hr]
  unfold wbyte
  split <;> exact BitVec.extractLsb'_xor

/-- The kernel on the block of the state words `b` and `32 + b`. -/
theorem kernel_block (K : Schedule) (d : Direction) (W₃ W₄ W₅ W₆ : Nat → BitVec 32) {b : Nat} (hb : b < 32)
    (h₄ : ∀ x < 64, W₄ x = transposeW W₃ x) (h₅ : ∀ x < 64, W₅ x = tdeaW K d W₄ x)
    (h₆ : ∀ x < 64, W₆ x = transposeW W₅ x) :
    wb (W₆ b) (W₆ (32 + b)) = blockOut K d (wb (W₃ b) (W₃ (32 + b))) := by
  have e := batch_block K d (wordsMem (W₃ b) (W₃ (32 + b))) (wordsMem (W₆ b) (W₆ (32 + b))) 0 W₃ W₄ W₅ W₆ hb
    (wordsMem_lo _ _).symm (wordsMem_hi _ _).symm h₄ h₅ h₆ (wordsMem_lo _ _) (wordsMem_hi _ _)
  exact e

/-- The words of block `b` of the data, as a block. -/
theorem wb_dw (m : Mem) {D : BitVec 32} {b n : Nat} (hf : D.toNat + 8 * n ≤ 2 ^ 32) (hb : b < n) :
    wb (dw m D (8 * b)) (dw m D (8 * b + 4)) = blockAt m (wAt (State.addr D) b) := by
  rw [blockAt_wb, dw_lo m hf hb, dw_hi m hf hb]

/-! ## The chaining value -/

/-- A word of the data is not in the chaining value. -/
theorem dw_frame_iv {D I : BitVec 32} {n : Nat} (hf : D.toNat + 8 * n ≤ 2 ^ 32)
    (hap : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr D, 8 * n⟩) {m m' : Mem}
    (hfr : Frame [⟨State.addr I, 8 * 1⟩] m m') {x : Nat} (hx : x + 4 ≤ 8 * n) : dw m' D x = dw m D x :=
  hfr.readW (contains_off hf hx (by decide)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hap.symm) (by decide)

/-- The chaining value's words into `r9` and `r10`. -/
theorem prevLoad_ok {s : State} {I : BitVec 32} (hi : Data s I 1) (h8 : s.gpr .r8 = I) :
    ∃ s', runBlock isa prevLoad s = some s' ∧ s'.gpr .r9 = dw s.mem I 0 ∧ s'.gpr .r10 = dw s.mem I 4 ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := exec_ldrData hi (t := .r9) (r := .r8) (off := 0) (x := 0) (by rw [h8]) (by decide) (by decide)
  let s₁ := s.setReg .r9 (dw s.mem I 0)
  have k₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have e₂ := exec_ldrData (hi.congr (k₁ _ (by decide)) rfl) (t := .r10) (r := .r8) (off := 4) (x := 4)
    (by rw [k₁ _ (by decide), h8]) (by decide) (by decide)
  refine ⟨s₁.setReg .r10 (dw s₁.mem I 4), by
    rw [prevLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil], ?_,
    RegUpd.gpr_setReg_self _ _ _, fun r h9 h10 => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact RegUpd.gpr_setReg_self _ _ _
  · rw [RegUpd.gpr_setReg_of_ne _ _ h10]; exact k₁ r h9

/-- `r9` and `r10` to the chaining value's words. -/
theorem prevStore_ok {s : State} {I : BitVec 32} (hi : Data s I 1) (h8 : s.gpr .r8 = I) :
    ∃ s', runBlock isa prevStore s = some s' ∧ dw s'.mem I 0 = s.gpr .r9 ∧ dw s'.mem I 4 = s.gpr .r10 ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨State.addr I, 8 * 1⟩] s.mem s'.mem := by
  have e₁ := exec_strData hi (t := .r9) (r := .r8) (off := 0) (x := 0) (by rw [h8]) (by decide) (by decide)
  let s₁ := stD s I 0 (s.gpr .r9)
  have hi₁ : Data s₁ I 1 := hi.congr rfl rfl
  have e₂ := exec_strData hi₁ (t := .r10) (r := .r8) (off := 4) (x := 4)
    (by rw [gpr_stD, h8]) (by decide) (by decide)
  refine ⟨stD s₁ I 4 (s₁.gpr .r10), by
    rw [prevStore, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil], ?_,
    dw_stD_self _ _ _ _, fun _ => rfl, rfl, rfl,
    (stD_frame hi (by decide) _).trans (stD_frame hi₁ (by decide) _)⟩
  exact (dw_stD hi₁ _ (by decide) (by decide) (by decide)).trans (dw_stD_self _ _ _ _)

/-- The chaining value's address to the working space. -/
theorem ivStash_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa ivStash s = some s' ∧ fw s' 89 = s.gpr .r8 ∧ (∀ j < 256, j ≠ 89 → fw s' j = fw s j) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [headR s 90] s.mem s'.mem := by
  have e₁ := exec_strFw h (t := .r8) (off := ivOff) 89 rfl (by decide)
  refine ⟨stFw s 89 (s.gpr .r8), by rw [ivStash, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some,
    runBlock_nil], ?_, fun j hj hne => ?_, fun _ => rfl, rfl, rfl, stFw_frame h (by decide) (by decide) _⟩
  · rw [fw_stFw h (by decide) (by decide), ite_eq_left rfl]
  · rw [fw_stFw h (by decide) hj, ite_eq_right hne]

/-- The chaining value's address back. -/
theorem ivUnstash_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa ivUnstash s = some s' ∧ s'.gpr .r8 = fw s 89 ∧ (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := exec_ldrFw h (t := .r8) (off := ivOff) 89 rfl (by decide)
  exact ⟨s.setReg .r8 (fw s 89), by rw [ivUnstash, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some,
    runBlock_nil], RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

/-! ## CBC decryption's blocks out -/

/-- A state word, XORed with `q`, to a word of the data. -/
theorem xorOut_ok {v : State} (hv : Room v) {D : BitVec 32} {k : Nat} (hd : Data v D k) {q : Reg}
    (hq : q ≠ .r7) {a c slot x : Nat}
    (h4 : v.gpr .r4 + BitVec.ofNat 32 a = v.gpr .r3 + BitVec.ofNat 32 (4 * slot)) (ha : a < 4096)
    (hs : slot < 256) (h5 : v.gpr .r5 + BitVec.ofNat 32 c = D + BitVec.ofNat 32 x) (hc : c < 4096)
    (hx : x + 4 ≤ 8 * k) :
    ∃ v', runBlock isa [.ldr .r7 .r4 a, .dp .eor .r7 .r7 (.reg q), .str .r7 .r5 c] v = some v' ∧
      dw v'.mem D x = fw v slot ^^^ v.gpr q ∧
      (∀ y, y + 4 ≤ 8 * k → x + 4 ≤ y ∨ y + 4 ≤ x → dw v'.mem D y = dw v.mem D y) ∧
      (∀ r, r ≠ .r7 → v'.gpr r = v.gpr r) ∧ (∀ j < 256, fw v' j = fw v j) ∧
      v'.rd = v.rd ∧ v'.wr = v.wr ∧ Frame [⟨State.addr D, 8 * k⟩] v.mem v'.mem := by
  have e₁ := exec_ldrAt hv (t := .r7) (r := .r4) (off := a) (k := slot) h4 ha hs
  let v₁ := v.setReg .r7 (fw v slot)
  have k₁ : ∀ r, r ≠ .r7 → v₁.gpr r = v.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have e₂ := exec_dp (s := v₁) (op := .eor) (d := .r7) (n := .r7) (o := .reg q) (op2_reg _ _)
  let v₂ := v₁.setReg .r7 (dpVal .eor (v₁.gpr .r7) (v₁.gpr q))
  have k₂ : ∀ r, r ≠ .r7 → v₂.gpr r = v.gpr r := fun r hr =>
    (RegUpd.gpr_setReg_of_ne _ _ hr).trans (k₁ r hr)
  have val : v₂.gpr .r7 = fw v slot ^^^ v.gpr q := by
    rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, k₁ q hq]; rfl
  have hv₂ : Room v₂ := hv.congr (k₂ _ (by decide)) rfl
  have hd₂ : Data v₂ D k := hd.congr (k₂ _ (by decide)) rfl
  have e₃ := exec_strData hd₂ (t := .r7) (r := .r5) (off := c) (x := x) (by rw [k₂ _ (by decide), h5]) hc hx
  refine ⟨stD v₂ D x (v₂.gpr .r7), by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil], (dw_stD_self _ _ _ _).trans val, fun y hy hxy => dw_stD hd₂ _ hx hy hxy,
    fun r hr => (gpr_stD _ _ _ _ r).trans (k₂ r hr), fun j hj => ?_, rfl, rfl, stD_frame hd₂ hx _⟩
  rw [fw_stD hv₂ hd₂ hx _ hj]
  exact (fw_setReg _ (by decide) _ _).trans (fw_setReg _ (by decide) _ _)

/-- The body of CBC decryption's copy out, but for the count. -/
def cbcMove : List Instr :=
  [.ldr .r11 .r5 0, .ldr .lr .r5 4,
   .ldr .r7 .r4 0, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 0,
   .ldr .r7 .r4 128, .dp .eor .r7 .r7 (.reg .r10), .str .r7 .r5 4,
   .mov .r9 (.reg .r11), .mov .r10 (.reg .lr)]

theorem cbcOutBody_eq : cbcOutBody = cbcMove ++ copyNext := rfl

/-- The registers CBC decryption's copy out leaves alone. -/
abbrev cbcKept (r : Reg) : Prop :=
  r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .lr

theorem cbcMove_ok {v : State} (hv : Room v) {D : BitVec 32} {k : Nat} (hd : Data v D k) {i : Nat}
    (hi : i < 32) (hik : i < k) (h4 : v.gpr .r4 = v.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i)))
    (h5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)) :
    ∃ v', runBlock isa cbcMove v = some v' ∧
      v'.gpr .r9 = dw v.mem D (8 * i) ∧ v'.gpr .r10 = dw v.mem D (8 * i + 4) ∧
      dw v'.mem D (8 * i) = fw v (8 + i) ^^^ v.gpr .r9 ∧
      dw v'.mem D (8 * i + 4) = fw v (40 + i) ^^^ v.gpr .r10 ∧
      (∀ y, y + 4 ≤ 8 * k → y + 4 ≤ 8 * i ∨ 8 * i + 8 ≤ y → dw v'.mem D y = dw v.mem D y) ∧
      (∀ r, cbcKept r ∨ r = .r4 ∨ r = .r5 ∨ r = .r6 → v'.gpr r = v.gpr r) ∧
      v'.rd = v.rd ∧ v'.wr = v.wr ∧ Frame [⟨State.addr D, 8 * k⟩] v.mem v'.mem := by
  -- the block's ciphertext words
  have e₁ := exec_ldrData hd (t := .r11) (r := .r5) (off := 0) (x := 8 * i)
    (by rw [h5, BitVec.add_zero]) (by decide) (by omega_using [hik])
  let v₁ := v.setReg .r11 (dw v.mem D (8 * i))
  have k₁ : ∀ r, r ≠ .r11 → v₁.gpr r = v.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have e₂ := exec_ldrData (hd.congr (k₁ _ (by decide)) rfl) (t := .lr) (r := .r5) (off := 4) (x := 8 * i + 4)
    (by rw [k₁ _ (by decide), h5, add_ofNat_ofNat]) (by decide) (by omega_using [hik])
  let v₂ := v₁.setReg .lr (dw v₁.mem D (8 * i + 4))
  have k₂ : ∀ r, r ≠ .r11 → r ≠ .lr → v₂.gpr r = v.gpr r := fun r h11 hlr =>
    (RegUpd.gpr_setReg_of_ne _ _ hlr).trans (k₁ r h11)
  have c11 : v₂.gpr .r11 = dw v.mem D (8 * i) :=
    (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans (RegUpd.gpr_setReg_self _ _ _)
  have clr : v₂.gpr .lr = dw v.mem D (8 * i + 4) := RegUpd.gpr_setReg_self _ _ _
  have hv₂ : Room v₂ := hv.congr (k₂ _ (by decide) (by decide)) rfl
  have hd₂ : Data v₂ D k := hd.congr (k₂ _ (by decide) (by decide)) rfl
  have fw₂ : ∀ j, fw v₂ j = fw v j := fun j =>
    (fw_setReg _ (by decide) _ _).trans (fw_setReg _ (by decide) _ _)
  -- the two words out
  obtain ⟨v₃, run₃, d₃, o₃, k₃, f₃, rd₃, wr₃, fr₃⟩ := xorOut_ok hv₂ hd₂ (q := .r9) (by decide) (a := 0) (c := 0)
    (slot := 8 + i) (x := 8 * i)
    (by rw [k₂ _ (by decide) (by decide), k₂ _ (by decide) (by decide), h4, BitVec.add_zero]) (by decide)
    (by omega_using [hi]) (by rw [k₂ _ (by decide) (by decide), h5, BitVec.add_zero]) (by decide)
    (by omega_using [hik])
  have hv₃ : Room v₃ := hv₂.congr (k₃ _ (by decide)) wr₃
  have hd₃ : Data v₃ D k := hd₂.congr (k₃ _ (by decide)) wr₃
  obtain ⟨v₄, run₄, d₄, o₄, k₄, f₄, rd₄, wr₄, fr₄⟩ := xorOut_ok hv₃ hd₃ (q := .r10) (by decide) (a := 128)
    (c := 4) (slot := 40 + i) (x := 8 * i + 4)
    (by rw [k₃ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide), k₂ _ (by decide) (by decide), h4,
      ptr4hi]) (by decide) (by omega_using [hi])
    (by rw [k₃ _ (by decide), k₂ _ (by decide) (by decide), h5, add_ofNat_ofNat]) (by decide)
    (by omega_using [hik])
  -- the ciphertext words, for the next block
  have e₅ := exec_mov (s := v₄) (d := .r9) (o := .reg .r11) (op2_reg _ _)
  let v₅ := v₄.setReg .r9 (v₄.gpr .r11)
  have e₆ := exec_mov (s := v₅) (d := .r10) (o := .reg .lr) (op2_reg _ _)
  have k₄' : ∀ r, r ≠ .r7 → r ≠ .r11 → r ≠ .lr → v₄.gpr r = v.gpr r := fun r h7 h11 hlr =>
    (k₄ r h7).trans ((k₃ r h7).trans (k₂ r h11 hlr))
  refine ⟨v₅.setReg .r10 (v₅.gpr .lr), runBlock_cat_some (a := [.ldr .r11 .r5 0, .ldr .lr .r5 4]) (by
      rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil])
    (runBlock_cat_some (a := [.ldr .r7 .r4 0, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 0]) run₃
      (runBlock_cat_some (a := [.ldr .r7 .r4 128, .dp .eor .r7 .r7 (.reg .r10), .str .r7 .r5 4]) run₄ (by
        rw [runBlock_cons, e₅, runStep_some, runBlock_cons, e₆, runStep_some, runBlock_nil]))),
    ?_, ?_, ?_, ?_, fun y hy hsep => ?_, fun r hr => ?_, rd₄.trans rd₃, wr₄.trans wr₃, fr₃.trans fr₄⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, k₄ _ (by decide), k₃ _ (by decide), c11]
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), clr]
  · show dw v₄.mem D (8 * i) = _
    rw [o₄ _ (by omega_using [hik]) (by omega_using []), d₃, fw₂, k₂ _ (by decide) (by decide)]
  · show dw v₄.mem D (8 * i + 4) = _
    rw [d₄, f₃ _ (by omega_using [hi]), fw₂, k₃ _ (by decide), k₂ _ (by decide) (by decide)]
  · show dw v₄.mem D y = _
    rw [o₄ y hy (by omega_using [hsep]), o₃ y hy (by omega_using [hsep])]
    rfl
  · have h9 : r ≠ .r9 := by rcases hr with h | h | h | h <;> first | exact h.2.2.2.2.1 | (subst h; decide)
    have h10 : r ≠ .r10 := by rcases hr with h | h | h | h <;> first | exact h.2.2.2.2.2.1 | (subst h; decide)
    have h7 : r ≠ .r7 := by rcases hr with h | h | h | h <;> first | exact h.2.2.2.1 | (subst h; decide)
    have h11 : r ≠ .r11 := by rcases hr with h | h | h | h <;> first | exact h.2.2.2.2.2.2.1 | (subst h; decide)
    have hlr : r ≠ .lr := by rcases hr with h | h | h | h <;> first | exact h.2.2.2.2.2.2.2 | (subst h; decide)
    rw [RegUpd.gpr_setReg_of_ne _ _ h10, RegUpd.gpr_setReg_of_ne _ _ h9, k₄' r h7 h11 hlr]

/-- The chaining value before block `i` of the batch, as words: the chaining
value's, or the block before's. -/
def prevW (m : Mem) (D I : BitVec 32) (i : Nat) : BitVec 32 × BitVec 32 :=
  if i = 0 then (dw m I 0, dw m I 4) else (dw m D (8 * (i - 1)), dw m D (8 * (i - 1) + 4))

/-- After `i` blocks of CBC decryption's copy out from `s`. -/
structure CbcOut (s : State) (D I : BitVec 32) (k i : Nat) (v : State) : Prop where
  r4 : v.gpr .r4 = s.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i))
  r5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)
  r6 : v.gpr .r6 = BitVec.ofNat 32 (k - i)
  r9 : v.gpr .r9 = (prevW s.mem D I i).1
  r10 : v.gpr .r10 = (prevW s.mem D I i).2
  keep : ∀ r, cbcKept r → v.gpr r = s.gpr r
  put : ∀ b < i, dw v.mem D (8 * b) = fw s (8 + b) ^^^ (prevW s.mem D I b).1 ∧
    dw v.mem D (8 * b + 4) = fw s (40 + b) ^^^ (prevW s.mem D I b).2
  rest : ∀ y, 8 * i ≤ y → y + 4 ≤ 8 * k → dw v.mem D y = dw s.mem D y
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  frame : Frame [⟨State.addr D, 8 * k⟩] s.mem v.mem

theorem prevW_succ (m : Mem) (D I : BitVec 32) (i : Nat) :
    prevW m D I (i + 1) = (dw m D (8 * i), dw m D (8 * i + 4)) := by
  rw [prevW, ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel]

theorem cbcOut_step {s : State} (h : Room s) {D I : BitVec 32} {k : Nat} (hd : Data s D k) (hk : k ≤ 32)
    {i : Nat} (hi : i < k) {v : State} (J : CbcOut s D I k i v) :
    ∃ v', runBlock isa cbcOutBody v = some v' ∧ CbcOut s D I k (i + 1) v' ∧ v'.z = decide (i + 1 = k) := by
  have g3 : v.gpr .r3 = s.gpr .r3 := J.keep _ (by decide)
  have hv : Room v := h.congr g3 J.wr
  have hdv : Data v D k := hd.congr g3 J.wr
  have fwv : ∀ j < 256, fw v j = fw s j := fun j hj => hd.fw_frame h g3 J.frame hj
  obtain ⟨v₁, run₁, n9, n10, lo₁, hi₁, o₁, k₁, rd₁, wr₁, f₁⟩ := cbcMove_ok hv hdv (i := i)
    (by omega_using [hi, hk]) hi (by rw [J.r4, g3]) J.r5
  obtain ⟨v', run', n4, n5, n6, nz, nk, nm, nrd, nwr, _⟩ := copyNext_ok (s := v₁)
  refine ⟨v', by rw [cbcOutBody_eq]; exact runBlock_cat_some run₁ run',
    ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun b hb => ?_, fun y hy hyk => ?_, nrd.trans (rd₁.trans J.rd),
      nwr.trans (wr₁.trans J.wr), ?_⟩, ?_⟩
  · rw [n4, k₁ _ (.inr (.inl rfl)), J.r4, ptr4]
  · rw [n5, k₁ _ (.inr (.inr (.inl rfl))), J.r5, ptr5]
  · rw [n6, k₁ _ (.inr (.inr (.inr rfl))), J.r6,
      (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).1]
    congr 1
  · rw [nk _ (by decide) (by decide) (by decide), n9, prevW_succ, J.rest _ (Nat.le_refl _) (by omega_using [hi])]
  · rw [nk _ (by decide) (by decide) (by decide), n10, prevW_succ, J.rest _ (by omega_using []) (by omega_using [hi])]
  · rw [nk r hr.1 hr.2.1 hr.2.2.1, k₁ r (.inl hr), J.keep r hr]
  · rw [nm]
    by_cases e : b = i
    · subst e
      rw [lo₁, hi₁, fwv _ (by omega_using [hi, hk]), fwv _ (by omega_using [hi, hk]), J.r9, J.r10]
      exact ⟨rfl, rfl⟩
    · have hb' : b < i := by omega_using [hb, e]
      rw [o₁ _ (by omega_using [hi, hb']) (by omega_using [hb']),
        o₁ _ (by omega_using [hi, hb']) (by omega_using [hb'])]
      exact J.put b hb'
  · rw [nm, o₁ y hyk (by omega_using [hy])]
    exact J.rest y (by omega_using [hy]) hyk
  · rw [nm]; exact J.frame.trans f₁
  · rw [nz, k₁ _ (.inr (.inr (.inr rfl))), J.r6,
      (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).2]
    exact decide_eq_decide.mpr (by omega_using [hi])

/-- CBC decryption's copy out: the state words, each XORed with the block
before it, to the batch's blocks, and the last ciphertext block to the
chaining value. -/
theorem cbcOut_ok {s : State} (h : Room s) {D I : BitVec 32} {k : Nat} (hd : Data s D k) (hiv : Data s I 1)
    (hap : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr D, 8 * k⟩) (hD : s.gpr .r1 = D)
    (hI : s.gpr .r8 = I) (hc : s.gpr .r12 = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) (hk : k ≤ 32) :
    WP isa cbcOut s fun s' =>
      (∀ b < k, dw s'.mem D (8 * b) = fw s (8 + b) ^^^ (prevW s.mem D I b).1 ∧
        dw s'.mem D (8 * b + 4) = fw s (40 + b) ^^^ (prevW s.mem D I b).2) ∧
      dw s'.mem I 0 = dw s.mem D (8 * (k - 1)) ∧ dw s'.mem I 4 = dw s.mem D (8 * (k - 1) + 4) ∧
      (∀ r, cbcKept r → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨State.addr D, 8 * k⟩, ⟨State.addr I, 8 * 1⟩] s.mem s'.mem := by
  unfold cbcOut
  apply WP.seq
  obtain ⟨s₁, run₁, i4, i5, i6, ik, im, ird, iwr, _⟩ := copyStart_ok (s := s)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  obtain ⟨s₂, run₂, p9, p10, pk, pm, prd, pwr⟩ := prevLoad_ok (s := s₁)
    (hiv.congr (ik _ (by decide) (by decide) (by decide)) iwr) ((ik _ (by decide) (by decide) (by decide)).trans hI)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have I0 : CbcOut s D I k 0 s₂ :=
    ⟨by rw [pk _ (by decide) (by decide), i4], by rw [pk _ (by decide) (by decide), i5, hD],
      by rw [pk _ (by decide) (by decide), i6, hc]; rfl, by rw [p9, im]; rfl, by rw [p10, im]; rfl,
      fun r hr => (pk r hr.2.2.2.2.1 hr.2.2.2.2.2.1).trans (ik r hr.1 hr.2.1 hr.2.2.1),
      fun b hb => by omega, fun y _ _ => by rw [pm, im], prd.trans ird, pwr.trans iwr,
      by rw [pm, im]; exact Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := CbcOut s D I k k)
    (fun m v => ∃ i, i < k ∧ m = k - i ∧ CbcOut s D I k i v) ?_ k s₂ ⟨0, hk1, rfl, I0⟩) fun s₃ J => ?_
  · intro m v ⟨i, hi, hm, J⟩
    obtain ⟨v', run, J', z⟩ := cbcOut_step h hd hk hi J
    refine WP.of_runBlock ⟨v', run, ?_⟩
    rw [show isa.eval .ne v' = some !v'.z from rfl, z]
    by_cases e : i + 1 = k
    · left; exact ⟨by simp [e], e ▸ J'⟩
    · right
      exact ⟨by simp [e], k - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, e], rfl, J'⟩
  · have g3 : s₃.gpr .r3 = s.gpr .r3 := J.keep _ (by decide)
    obtain ⟨s₄, run₄, q0, q4, qk, qrd, qwr, qf⟩ := prevStore_ok (s := s₃) (hiv.congr g3 J.wr)
      ((J.keep _ (by decide)).trans hI)
    have fit := hd.fit
    have pw : prevW s.mem D I k = (dw s.mem D (8 * (k - 1)), dw s.mem D (8 * (k - 1) + 4)) := by
      rw [prevW, ite_eq_right (by omega_using [hk1])]
    refine WP.of_runBlock ⟨s₄, run₄, fun b hb => ?_, ?_, ?_, fun r hr => (qk r).trans (J.keep r hr),
      qrd.trans J.rd, qwr.trans J.wr,
      (frame_in J.frame List.mem_cons_self).trans (frame_in qf (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    · rw [dw_frame_iv fit hap qf (by omega_using [hb]), dw_frame_iv fit hap qf (by omega_using [hb])]
      exact J.put b hb
    · rw [q0, J.r9, pw]
    · rw [q4, J.r10, pw]

/-! ## The kernel -/

/-- The kernel of a batch: the block of the state words `b` and `32 + b`
becomes its encryption or decryption, and the batch's registers come back. -/
theorem kernel_ok (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32} (hs : Sched s Sb)
    (h0 : s.gpr .r0 = Sb) :
    WP isa (kernel d) s fun s' =>
      (∀ b < 32, wb (words s' b) (words s' (32 + b)) =
        blockOut (scheduleAt s.mem (State.addr Sb)) d (wb (words s b) (words s (32 + b)))) ∧
      (∀ r ∈ [Reg.r0, .r1, .r2, .r3, .r8, .r12], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [headR s 90] s.mem s'.mem := by
  unfold kernel
  -- the registers stashed
  apply WP.seq
  obtain ⟨s₃, run₃, a0, a1, a2, a12, o₃, g₃, rd₃, wr₃, f₃⟩ := stash_ok h
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have h₃ : Room s₃ := h.congr (g₃ _) wr₃
  apply WP.seq
  obtain ⟨t, runt, t8, to, tg, trd, twr, tf⟩ := ivStash_ok h₃
  refine WP.of_runBlock ⟨t, runt, ?_⟩
  have r3t : t.gpr .r3 = s.gpr .r3 := (tg _).trans (g₃ _)
  have ht : Room t := h.congr r3t (twr.trans wr₃)
  have Ft : Frame [headR s 90] s.mem t.mem :=
    (headR_mono (by decide) f₃).trans (by rw [← headR_congr (g₃ .r3)]; exact tf)
  have wt : ∀ x < 64, words t x = words s x := fun x hx =>
    (to _ (by unfold spills; omega_using [hx]) (by unfold spills; omega_using [hx])).trans
      (o₃ _ (by unfold spills; omega_using [hx]))
  -- the transposition
  apply WP.seq
  obtain ⟨s₄, run₄, w₄, r3₄, rd₄, wr₄, _, f₄⟩ := transpose_ok ht
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have r3₄' : s₄.gpr .r3 = s.gpr .r3 := r3₄.trans r3t
  have wr₄' : s₄.wr = s.wr := wr₄.trans (twr.trans wr₃)
  have rd₄' : s₄.rd = s.rd := rd₄.trans (trd.trans rd₃)
  have h₄ : Room s₄ := h.congr r3₄' wr₄'
  have G₄ : Frame [headR t 76] t.mem s₄.mem := headR_mono (by decide) f₄
  have F₄ : Frame [headR s 90] s.mem s₄.mem :=
    Ft.trans (by rw [← headR_congr r3t]; exact headR_mono (by decide) f₄)
  have st0 : fw t 76 = Sb := by rw [to _ (by decide) (by decide), a0, h0]
  -- the passes
  apply WP.seq
  refine WP.mono (passesCall_ok d h₄ (hs.congr r3₄' rd₄')
    ((fw_of_frame ht r3₄ G₄ (by decide) (by decide)).trans st0)) fun s₅ ⟨w₅, r3₅, rd₅, wr₅, _, f₅⟩ => ?_
  have r3₅' : s₅.gpr .r3 = s.gpr .r3 := r3₅.trans r3₄'
  have h₅ : Room s₅ := h.congr r3₅' (wr₅.trans wr₄')
  have G₅ : Frame [headR t 76] t.mem s₅.mem := G₄.trans (by rw [← headR_congr r3₄]; exact f₅)
  rw [scheduleAt_frame hs (n := 90) (by decide) F₄] at w₅
  -- the transposition back
  apply WP.seq
  obtain ⟨s₆, run₆, w₆, r3₆, rd₆, wr₆, _, f₆⟩ := transpose_ok h₅
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have r3₆t : s₆.gpr .r3 = t.gpr .r3 := r3₆.trans (r3₅.trans r3₄)
  have h₆ : Room s₆ := h.congr (r3₆.trans r3₅') (wr₆.trans (wr₅.trans wr₄'))
  have G₆ : Frame [headR t 76] t.mem s₆.mem :=
    G₅.trans (by rw [← headR_congr (r3₅.trans r3₄)]; exact headR_mono (by decide) f₆)
  have F₆ : Frame [headR s 90] s.mem s₆.mem :=
    Ft.trans (by rw [← headR_congr r3t]; exact headR_mono (by decide) G₆)
  have st : ∀ j, 76 ≤ j → j < 256 → fw s₆ j = fw t j := fun j h76 hj => fw_of_frame ht r3₆t G₆ h76 hj
  -- the registers back
  apply WP.seq
  obtain ⟨s₇, run₇, b0, b1, b2, b12, r3₇, m₇, rd₇, wr₇⟩ := unstash_ok h₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have h₇ : Room s₇ := h₆.congr r3₇ wr₇
  obtain ⟨s₈, run₈, c8, ck, m₈, rd₈, wr₈⟩ := ivUnstash_ok h₇
  refine WP.of_runBlock ⟨s₈, run₈, fun b hb => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have w₈ : ∀ x < 64, words s₈ x = words s₆ x := fun x _ => by
      rw [words, words, fw, fw, m₈, m₇, ck _ (by decide), r3₇]
    rw [w₈ _ (by omega_using [hb]), w₈ _ (by omega_using [hb]), ← wt _ (by omega_using [hb]),
      ← wt _ (by omega_using [hb])]
    exact kernel_block _ d (words t) (words s₄) (words s₅) (words s₆) hb w₄ w₅ w₆
  · have f7 : ∀ j < 256, fw s₇ j = fw s₆ j := fun j _ => by rw [fw, fw, m₇, r3₇]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ck _ (by decide), b0, st _ (by decide) (by decide), to _ (by decide) (by decide), a0]
    · rw [ck _ (by decide), b1, st _ (by decide) (by decide), to _ (by decide) (by decide), a1]
    · rw [ck _ (by decide), b2, st _ (by decide) (by decide), to _ (by decide) (by decide), a2]
    · rw [ck _ (by decide), r3₇, r3₆, r3₅']
    · rw [c8, f7 _ (by decide), st _ (by decide) (by decide), t8, g₃]
    · rw [ck _ (by decide), b12, st _ (by decide) (by decide), to _ (by decide) (by decide), a12]
  · rw [rd₈, rd₇, rd₆, rd₅, rd₄']
  · rw [wr₈, wr₇, wr₆, wr₅, wr₄']
  · rw [m₈, m₇]; exact F₆

/-! ## A batch of CBC decryption -/

/-- The block before block `b` of the data at `D`: the chaining value at
`I`, or block `b - 1`. -/
def prevBlock (m : Mem) (D I : Addr) (b : Nat) : Block :=
  if b = 0 then blockAt m I else blockAt m (wAt D (b - 1))

theorem wb_dw0 (m : Mem) {I : BitVec 32} (hf : I.toNat + 8 * 1 ≤ 2 ^ 32) :
    wb (dw m I 0) (dw m I 4) = blockAt m (State.addr I) := by
  rw [blockAt_wb, dw, dw, BitVec.add_zero, addr_add (by omega_using [hf])]

/-- The words before block `b`, as a block. -/
theorem wb_prevW (m : Mem) {D I : BitVec 32} {n : Nat} (hfD : D.toNat + 8 * n ≤ 2 ^ 32)
    (hfI : I.toNat + 8 * 1 ≤ 2 ^ 32) {b : Nat} (hb : b < n) :
    wb (prevW m D I b).1 (prevW m D I b).2 = prevBlock m (State.addr D) (State.addr I) b := by
  unfold prevW prevBlock
  by_cases h0 : b = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; exact wb_dw0 m hfI
  · rw [ite_eq_right h0, ite_eq_right h0]; exact wb_dw m hfD (by omega_using [hb])

/-- What a batch of CBC or CFB decryption needs: the working space, the
schedule, a block left, the data, and the chaining value apart from both. -/
structure WidePre (s : State) (Sb D I : BitVec 32) (n : Nat) : Prop where
  room : Room s
  sched : Sched s Sb
  data : Data s D n
  iv : Data s I 1
  apart : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr D, 8 * n⟩
  ki : (⟨State.addr Sb, 384⟩ : Region).Disjoint ⟨State.addr I, 8⟩
  r0 : s.gpr .r0 = Sb
  r1 : s.gpr .r1 = D
  r2 : s.gpr .r2 = BitVec.ofNat 32 n
  r8 : s.gpr .r8 = I
  pos : 1 ≤ n

/-- What a batch leaves: each of its blocks is `F` of the schedule, the block
and the block before it. -/
structure WidePost (s : State) (Sb D I : BitVec 32) (n k : Nat)
    (F : Schedule → Block → Block → Nat → Byte) (s' : State) : Prop where
  r0 : s'.gpr .r0 = Sb
  r1 : s'.gpr .r1 = D + BitVec.ofNat 32 (8 * k)
  r2 : s'.gpr .r2 = BitVec.ofNat 32 (n - k)
  r3 : s'.gpr .r3 = s.gpr .r3
  r8 : s'.gpr .r8 = I
  z : s'.z = decide (n = k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  out : ∀ b < k, ∀ r < 8, s'.mem (wAt (State.addr D) b + BitVec.ofNat 64 r) =
    F (scheduleAt s.mem (State.addr Sb)) (blockAt s.mem (wAt (State.addr D) b))
      (prevBlock s.mem (State.addr D) (State.addr I) b) r
  ivo : blockAt s'.mem (State.addr I) = blockAt s.mem (wAt (State.addr D) (k - 1))
  frame : Frame [headR s 90, ⟨State.addr D, 8 * k⟩, ⟨State.addr I, 8 * 1⟩] s.mem s'.mem

theorem blockOut_decrypt (K : Schedule) (B : Block) : blockOut K .decrypt B = decryptBlock K B := rfl
theorem blockOut_encrypt (K : Schedule) (B : Block) : blockOut K .encrypt B = encryptBlock K B := rfl

/-- Byte `r` of CBC decryption's block, from the block `B` and the block `P`
before it. -/
def cbcF (K : Schedule) (B P : Block) (r : Nat) : Byte := bbyte (decryptBlock K B) r ^^^ bbyte P r

theorem cbcBatch_ok {s : State} {Sb D I : BitVec 32} {n : Nat} (h : WidePre s Sb D I n) :
    WP isa cbcBatch s (WidePost s Sb D I n (min n 32) cbcF) := by
  have fit := h.data.fit
  have fitI := h.iv.fit
  have hn : n < 2 ^ 32 := by omega_using [fit]
  generalize hk : min n 32 = k
  have hk1 : 1 ≤ k := by have := h.pos; omega_using [hk, this]
  have hk32 : k ≤ 32 := by omega_using [hk]
  have hkn : k ≤ n := by omega_using [hk]
  have hkOf : kOf s = k := by rw [kOf, h.r2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, hk]
  unfold cbcBatch
  apply WP.seq
  refine WP.mono (batchCount_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_
  rw [hkOf] at c₁
  have r3₁ : s₁.gpr .r3 = s.gpr .r3 := g₁ _ (by decide)
  have h₁ : Room s₁ := h.room.congr r3₁ wr₁
  -- the copy in
  apply WP.seq
  refine WP.mono (copyIn_ok h₁ (h.data.congr r3₁ wr₁) ((g₁ _ (by decide)).trans h.r1) c₁ hk1 hkn hk32)
    fun s₂ I₂ => ?_
  have k₂ : ∀ r, copyKept r → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr h12 =>
    (I₂.keep r hr).trans (g₁ r h12)
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := k₂ _ (by decide) (by decide)
  have wr₂ : s₂.wr = s.wr := I₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := I₂.rd.trans rd₁
  have h₂ : Room s₂ := h.room.congr r3₂ wr₂
  have F₂ : Frame [headR s 90] s.mem s₂.mem := by
    have := I₂.frame
    rw [m₁, stR_congr r3₁] at this
    exact headR_mono (by decide) this
  -- the kernel
  apply WP.seq
  refine WP.mono (kernel_ok .decrypt h₂ (h.sched.congr r3₂ rd₂) ((k₂ _ (by decide) (by decide)).trans h.r0))
    fun s₃ ⟨ker, g₃, rd₃, wr₃, f₃⟩ => ?_
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := (g₃ _ (by decide)).trans r3₂
  have wr₃' : s₃.wr = s.wr := wr₃.trans wr₂
  have h₃ : Room s₃ := h.room.congr r3₃ wr₃'
  have F₃ : Frame [headR s 90] s.mem s₃.mem := F₂.trans (by rw [← headR_congr r3₂]; exact f₃)
  have d₃ : Data s₃ D k := (h.data.take hkn).congr r3₃ wr₃'
  have i₃ : Data s₃ I 1 := h.iv.congr r3₃ wr₃'
  have c12 : s₃.gpr .r12 = BitVec.ofNat 32 k := by rw [g₃ _ (by decide), I₂.keep _ (by decide), c₁]
  -- the copy out
  apply WP.seq
  refine WP.mono (cbcOut_ok h₃ d₃ i₃ (h.apart.sub_right (Region.sub_prefix (by omega_using [hkn])))
    ((g₃ _ (by decide)).trans ((k₂ _ (by decide) (by decide)).trans h.r1))
    ((g₃ _ (by decide)).trans ((k₂ _ (by decide) (by decide)).trans h.r8)) c12 hk1 hk32)
    fun s₄ ⟨put, iv0, iv4, k₄, rd₄, wr₄, f₄⟩ => ?_
  obtain ⟨s₅, run₅, n1, n2, nz, n0, n3, m₅, rd₅, wr₅, nk⟩ := advance_ok (s := s₄)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have e12 : s₄.gpr .r12 = BitVec.ofNat 32 k := (k₄ _ (by decide)).trans c12
  have e2 : s₄.gpr .r2 = BitVec.ofNat 32 n :=
    (k₄ _ (by decide)).trans ((g₃ _ (by decide)).trans ((k₂ _ (by decide) (by decide)).trans h.r2))
  obtain ⟨sub, subz⟩ := ofNat_sub hkn hn
  have dS : ∀ x, x + 4 ≤ 8 * n → dw s₃.mem D x = dw s.mem D x := fun x hx =>
    h.data.read_frame (c := 90) (by decide) F₃ hx
  have dI : ∀ x, x + 4 ≤ 8 * 1 → dw s₃.mem I x = dw s.mem I x := fun x hx =>
    h.iv.read_frame (c := 90) (by decide) F₃ hx
  have pW : ∀ b < k, prevW s₃.mem D I b = prevW s.mem D I b := fun b hb => by
    unfold prevW
    by_cases h0 : b = 0
    · rw [ite_eq_left h0, ite_eq_left h0, dI _ (by decide), dI _ (by decide)]
    · rw [ite_eq_right h0, ite_eq_right h0, dS _ (by omega_using [hb, hkn]), dS _ (by omega_using [hb, hkn])]
  refine ⟨by rw [n0, k₄ _ (by decide), g₃ _ (by decide), k₂ _ (by decide) (by decide), h.r0], ?_,
    by rw [n2, e2, e12, sub], by rw [n3, k₄ _ (by decide), r3₃], ?_, by rw [nz, e2, e12, subz],
    by rw [rd₅, rd₄, rd₃, rd₂], by rw [wr₅, wr₄, wr₃'], fun b hb r hr => ?_, ?_, ?_⟩
  · rw [n1, k₄ _ (by decide), g₃ _ (by decide), k₂ _ (by decide) (by decide), h.r1, e12,
      shl3 k (by omega_using [hk32])]
  · rw [nk _ (by decide) (by decide), k₄ _ (by decide), g₃ _ (by decide), k₂ _ (by decide) (by decide), h.r8]
  · have hb32 : b < 32 := by omega_using [hb, hk32]
    have hbn : b < n := by omega_using [hb, hkn]
    obtain ⟨p1, p2⟩ := put b hb
    obtain ⟨g1, g2⟩ := I₂.got b hb
    have w1 : fw s₃ (8 + b) = words s₃ b := rfl
    have w2 : fw s₃ (40 + b) = words s₃ (32 + b) := by
      rw [words, show spills + (32 + b) = 40 + b by unfold spills; omega_using []]
    have i1 : words s₂ b = dw s.mem D (8 * b) := g1.trans (by rw [m₁])
    have i2 : words s₂ (32 + b) = dw s.mem D (8 * b + 4) := by
      rw [words, show spills + (32 + b) = 40 + b by unfold spills; omega_using [], g2, m₁]
    have K₂ : scheduleAt s₂.mem (State.addr Sb) = scheduleAt s.mem (State.addr Sb) :=
      scheduleAt_frame h.sched (by decide) F₂
    unfold cbcF
    rw [m₅, ← bbyte_blockAt s₄.mem (wAt (State.addr D) b) hr, ← wb_dw s₄.mem fit hbn, p1, p2,
      bbyte_wb_xor _ _ _ _ hr, w1, w2, ker b hb32, i1, i2, wb_dw s.mem fit hbn, pW b hb,
      wb_prevW s.mem fit fitI hbn, K₂, blockOut_decrypt]
  · rw [m₅, ← wb_dw0 s₄.mem fitI, iv0, iv4, dS _ (by omega_using [hk1, hkn]), dS _ (by omega_using [hk1, hkn]),
      wb_dw s.mem fit (by omega_using [hk1, hkn])]
  · rw [m₅]
    refine (frame_in F₃ List.mem_cons_self).trans (f₄.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

/-! ## CFB decryption's blocks in -/

/-- A word of `A`'s blocks is not in a region apart from them. -/
theorem dw_frame_apart {A B : BitVec 32} {n l : Nat} (hf : A.toNat + 8 * n ≤ 2 ^ 32)
    (hap : (⟨State.addr A, 8 * n⟩ : Region).Disjoint ⟨State.addr B, l⟩) {m m' : Mem}
    (hfr : Frame [⟨State.addr B, l⟩] m m') {x : Nat} (hx : x + 4 ≤ 8 * n) : dw m' A x = dw m A x :=
  hfr.readW (contains_off hf hx (by decide)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hap) (by decide)

/-- The body of CFB decryption's copy in, but for the count. -/
def cfbMoveIn : List Instr := [.str .r9 .r4 0, .str .r10 .r4 128, .ldr .r9 .r5 0, .ldr .r10 .r5 4]

theorem cfbInBody_eq : cfbInBody = cfbMoveIn ++ copyNext := rfl

/-- The block before a block (`r9` and `r10`) into the state words `8 + i`
and `40 + i`, and the block into `r9` and `r10`. -/
theorem cfbMoveIn_ok {v : State} (hv : Room v) {D : BitVec 32} {n : Nat} (hd : Data v D n) {i : Nat}
    (hi : i < 32) (hin : i < n) (h4 : v.gpr .r4 = v.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i)))
    (h5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)) :
    ∃ v', runBlock isa cfbMoveIn v = some v' ∧
      fw v' (8 + i) = v.gpr .r9 ∧ fw v' (40 + i) = v.gpr .r10 ∧
      (∀ j < 256, j ≠ 8 + i → j ≠ 40 + i → fw v' j = fw v j) ∧
      v'.gpr .r9 = dw v.mem D (8 * i) ∧ v'.gpr .r10 = dw v.mem D (8 * i + 4) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → v'.gpr r = v.gpr r) ∧
      (∀ x, x + 4 ≤ 8 * n → dw v'.mem D x = dw v.mem D x) ∧
      v'.rd = v.rd ∧ v'.wr = v.wr ∧ Frame [stR v] v.mem v'.mem := by
  have e₁ := exec_strAt hv (t := .r9) (r := .r4) (off := 0) (k := 8 + i)
    (by rw [h4, BitVec.add_zero]) (by decide) (by omega_using [hi])
  let v₁ := stFw v (8 + i) (v.gpr .r9)
  have k₁ : ∀ r, v₁.gpr r = v.gpr r := fun r => gpr_stFw _ _ _ r
  have hv₁ : Room v₁ := hv.stFw _ _
  have hd₁ : Data v₁ D n := hd.congr (k₁ _) rfl
  have e₂ := exec_strAt hv₁ (t := .r10) (r := .r4) (off := 128) (k := 40 + i)
    (by rw [k₁, k₁, h4, ptr4hi]) (by decide) (by omega_using [hi])
  let v₂ := stFw v₁ (40 + i) (v₁.gpr .r10)
  have k₂ : ∀ r, v₂.gpr r = v.gpr r := fun r => (gpr_stFw _ _ _ r).trans (k₁ r)
  have hd₂ : Data v₂ D n := hd.congr (k₂ _) rfl
  have d₂ : ∀ x, x + 4 ≤ 8 * n → dw v₂.mem D x = dw v.mem D x := fun x hx =>
    (dw_stFw hv₁ hd₁ (by omega_using [hi]) _ hx).trans (dw_stFw hv hd (by omega_using [hi]) _ hx)
  have e₃ := exec_ldrData hd₂ (t := .r9) (r := .r5) (off := 0) (x := 8 * i)
    (by rw [k₂, h5, BitVec.add_zero]) (by decide) (by omega_using [hin])
  let v₃ := v₂.setReg .r9 (dw v₂.mem D (8 * i))
  have k₃ : ∀ r, r ≠ .r9 → v₃.gpr r = v₂.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have hd₃ : Data v₃ D n := hd₂.congr (k₃ _ (by decide)) rfl
  have e₄ := exec_ldrData hd₃ (t := .r10) (r := .r5) (off := 4) (x := 8 * i + 4)
    (by rw [k₃ _ (by decide), k₂, h5, add_ofNat_ofNat]) (by decide) (by omega_using [hin])
  have f₁ : Frame [stR v] v.mem v₁.mem :=
    stFw_frame (s := v) hv (n := spills + 64) (by unfold spills; omega_using [hi]) (by decide) _
  have f₂ : Frame [stR v] v₁.mem v₂.mem :=
    stFw_frame (s := v₁) hv₁ (n := spills + 64) (by unfold spills; omega_using [hi]) (by decide) _
  have w₁ : ∀ j, fw (v₃.setReg .r10 (dw v₃.mem D (8 * i + 4))) j = fw v₂ j := fun j =>
    (fw_setReg _ (by decide) _ _).trans (fw_setReg _ (by decide) _ _)
  refine ⟨v₃.setReg .r10 (dw v₃.mem D (8 * i + 4)), by
    rw [cfbMoveIn, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil], ?_, ?_, fun j hj h8 h40 => ?_, ?_, ?_,
    fun r h9 h10 => ?_, fun x hx => d₂ x hx, rfl, rfl, f₁.trans f₂⟩
  · rw [w₁, fw_stFw hv₁ (by omega_using [hi]) (by omega_using [hi]), ite_eq_right (by omega_using []),
      fw_stFw hv (by omega_using [hi]) (by omega_using [hi]), ite_eq_left rfl]
  · rw [w₁, fw_stFw hv₁ (by omega_using [hi]) (by omega_using [hi]), ite_eq_left rfl, k₁]
  · rw [w₁, fw_stFw hv₁ (by omega_using [hi]) hj, ite_eq_right h40, fw_stFw hv (by omega_using [hi]) hj,
      ite_eq_right h8]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self]
    exact d₂ _ (by omega_using [hin])
  · rw [RegUpd.gpr_setReg_self]
    exact d₂ _ (by omega_using [hin])
  · rw [RegUpd.gpr_setReg_of_ne _ _ h10, k₃ r h9, k₂]

/-- After `i` blocks of CFB decryption's copy in from `s`. -/
structure CfbIn (s : State) (D I : BitVec 32) (n k i : Nat) (v : State) : Prop where
  r4 : v.gpr .r4 = s.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i))
  r5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)
  r6 : v.gpr .r6 = BitVec.ofNat 32 (k - i)
  r9 : v.gpr .r9 = (prevW s.mem D I i).1
  r10 : v.gpr .r10 = (prevW s.mem D I i).2
  keep : ∀ r, cbcKept r → v.gpr r = s.gpr r
  got : ∀ b < i, fw v (8 + b) = (prevW s.mem D I b).1 ∧ fw v (40 + b) = (prevW s.mem D I b).2
  data : ∀ x, x + 4 ≤ 8 * n → dw v.mem D x = dw s.mem D x
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  frame : Frame [stR s] s.mem v.mem

theorem cfbIn_step {s : State} (h : Room s) {D I : BitVec 32} {n k : Nat} (hd : Data s D n)
    (hkn : k ≤ n) (hk : k ≤ 32) {i : Nat} (hi : i < k) {v : State} (J : CfbIn s D I n k i v) :
    ∃ v', runBlock isa cfbInBody v = some v' ∧ CfbIn s D I n k (i + 1) v' ∧ v'.z = decide (i + 1 = k) := by
  have g3 : v.gpr .r3 = s.gpr .r3 := J.keep _ (by decide)
  have hv : Room v := h.congr g3 J.wr
  have hdv : Data v D n := hd.congr g3 J.wr
  obtain ⟨v₁, run₁, lo₁, hi₁, fw₁, n9, n10, k₁, d₁, rd₁, wr₁, f₁⟩ := cfbMoveIn_ok hv hdv (i := i)
    (by omega_using [hi, hk]) (by omega_using [hi, hkn]) (by rw [J.r4, g3]) J.r5
  obtain ⟨v', run', n4, n5, n6, nz, nk, nm, nrd, nwr, _⟩ := copyNext_ok (s := v₁)
  have fwv : ∀ j < 256, fw v' j = fw v₁ j := fun j _ => by
    rw [fw, fw, nm, nk _ (by decide) (by decide) (by decide)]
  refine ⟨v', by rw [cfbInBody_eq]; exact runBlock_cat_some run₁ run',
    ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun b hb => ?_, fun x hx => ?_, nrd.trans (rd₁.trans J.rd),
      nwr.trans (wr₁.trans J.wr), ?_⟩, ?_⟩
  · rw [n4, k₁ _ (by decide) (by decide), J.r4, ptr4]
  · rw [n5, k₁ _ (by decide) (by decide), J.r5, ptr5]
  · rw [n6, k₁ _ (by decide) (by decide), J.r6,
      (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).1]
    congr 1
  · rw [nk _ (by decide) (by decide) (by decide), n9, prevW_succ, J.data _ (by omega_using [hi, hkn])]
  · rw [nk _ (by decide) (by decide) (by decide), n10, prevW_succ, J.data _ (by omega_using [hi, hkn])]
  · rw [nk r hr.1 hr.2.1 hr.2.2.1, k₁ r hr.2.2.2.2.1 hr.2.2.2.2.2.1, J.keep r hr]
  · rw [fwv _ (by omega_using [hb, hi, hk]), fwv _ (by omega_using [hb, hi, hk])]
    by_cases e : b = i
    · subst e
      rw [lo₁, hi₁, J.r9, J.r10]
      exact ⟨rfl, rfl⟩
    · have hb' : b < i := by omega_using [hb, e]
      rw [fw₁ _ (by omega_using [hb', hi, hk]) (by omega_using [e]) (by omega_using [hb']),
        fw₁ _ (by omega_using [hb', hi, hk]) (by omega_using [hi, hk]) (by omega_using [e])]
      exact J.got b hb'
  · rw [nm, d₁ x hx]; exact J.data x hx
  · rw [nm]; exact J.frame.trans (by rw [← stR_congr g3]; exact f₁)
  · rw [nz, k₁ _ (by decide) (by decide), J.r6,
      (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).2]
    exact decide_eq_decide.mpr (by omega_using [hi])

/-- CFB decryption's copy in: the block before each of the batch's blocks to
the state words, and the batch's last block to the chaining value. -/
theorem cfbIn_ok {s : State} (h : Room s) {D I : BitVec 32} {n k : Nat} (hd : Data s D n) (hiv : Data s I 1)
    (hap : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr D, 8 * n⟩) (hD : s.gpr .r1 = D)
    (hI : s.gpr .r8 = I) (hc : s.gpr .r12 = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hk : k ≤ 32) :
    WP isa cfbIn s fun s' =>
      (∀ b < k, fw s' (8 + b) = (prevW s.mem D I b).1 ∧ fw s' (40 + b) = (prevW s.mem D I b).2) ∧
      dw s'.mem I 0 = dw s.mem D (8 * (k - 1)) ∧ dw s'.mem I 4 = dw s.mem D (8 * (k - 1) + 4) ∧
      (∀ x, x + 4 ≤ 8 * n → dw s'.mem D x = dw s.mem D x) ∧
      (∀ r, cbcKept r → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stR s, ⟨State.addr I, 8 * 1⟩] s.mem s'.mem := by
  unfold cfbIn
  apply WP.seq
  obtain ⟨s₁, run₁, i4, i5, i6, ik, im, ird, iwr, _⟩ := copyStart_ok (s := s)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  obtain ⟨s₂, run₂, p9, p10, pk, pm, prd, pwr⟩ := prevLoad_ok (s := s₁)
    (hiv.congr (ik _ (by decide) (by decide) (by decide)) iwr) ((ik _ (by decide) (by decide) (by decide)).trans hI)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have I0 : CfbIn s D I n k 0 s₂ :=
    ⟨by rw [pk _ (by decide) (by decide), i4], by rw [pk _ (by decide) (by decide), i5, hD],
      by rw [pk _ (by decide) (by decide), i6, hc]; rfl, by rw [p9, im]; rfl, by rw [p10, im]; rfl,
      fun r hr => (pk r hr.2.2.2.2.1 hr.2.2.2.2.2.1).trans (ik r hr.1 hr.2.1 hr.2.2.1),
      fun b hb => by omega, fun x _ => by rw [pm, im], prd.trans ird, pwr.trans iwr,
      by rw [pm, im]; exact Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := CfbIn s D I n k k)
    (fun m v => ∃ i, i < k ∧ m = k - i ∧ CfbIn s D I n k i v) ?_ k s₂ ⟨0, hk1, rfl, I0⟩) fun s₃ J => ?_
  · intro m v ⟨i, hi, hm, J⟩
    obtain ⟨v', run, J', z⟩ := cfbIn_step h hd hkn hk hi J
    refine WP.of_runBlock ⟨v', run, ?_⟩
    rw [show isa.eval .ne v' = some !v'.z from rfl, z]
    by_cases e : i + 1 = k
    · left; exact ⟨by simp [e], e ▸ J'⟩
    · right
      exact ⟨by simp [e], k - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, e], rfl, J'⟩
  · have g3 : s₃.gpr .r3 = s.gpr .r3 := J.keep _ (by decide)
    have h₃ : Room s₃ := h.congr g3 J.wr
    have i₃ : Data s₃ I 1 := hiv.congr g3 J.wr
    obtain ⟨s₄, run₄, q0, q4, qk, qrd, qwr, qf⟩ := prevStore_ok (s := s₃) i₃ ((J.keep _ (by decide)).trans hI)
    have fit := hd.fit
    have pw : prevW s.mem D I k = (dw s.mem D (8 * (k - 1)), dw s.mem D (8 * (k - 1) + 4)) := by
      rw [prevW, ite_eq_right (by omega_using [hk1])]
    have fwq : ∀ j < 256, fw s₄ j = fw s₃ j := fun j hj => i₃.fw_frame h₃ (qk _) qf hj
    refine WP.of_runBlock ⟨s₄, run₄, fun b hb => ?_, ?_, ?_, fun x hx => ?_,
      fun r hr => (qk r).trans (J.keep r hr), qrd.trans J.rd, qwr.trans J.wr,
      (frame_in J.frame List.mem_cons_self).trans (frame_in qf (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    · rw [fwq _ (by omega_using [hb, hk]), fwq _ (by omega_using [hb, hk])]
      exact J.got b hb
    · rw [q0, J.r9, pw]
    · rw [q4, J.r10, pw]
    · rw [dw_frame_iv fit hap qf hx]; exact J.data x hx

/-! ## CFB decryption's blocks out -/

/-- A state word XORed into a word of the data. -/
theorem xorIn_ok {v : State} (hv : Room v) {D : BitVec 32} {k : Nat} (hd : Data v D k) {a c slot x : Nat}
    (h4 : v.gpr .r4 + BitVec.ofNat 32 a = v.gpr .r3 + BitVec.ofNat 32 (4 * slot)) (ha : a < 4096)
    (hs : slot < 256) (h5 : v.gpr .r5 + BitVec.ofNat 32 c = D + BitVec.ofNat 32 x) (hc : c < 4096)
    (hx : x + 4 ≤ 8 * k) :
    ∃ v', runBlock isa [.ldr .r7 .r5 c, .ldr .r9 .r4 a, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 c] v = some v' ∧
      dw v'.mem D x = dw v.mem D x ^^^ fw v slot ∧
      (∀ y, y + 4 ≤ 8 * k → x + 4 ≤ y ∨ y + 4 ≤ x → dw v'.mem D y = dw v.mem D y) ∧
      (∀ r, r ≠ .r7 → r ≠ .r9 → v'.gpr r = v.gpr r) ∧ (∀ j < 256, fw v' j = fw v j) ∧
      v'.rd = v.rd ∧ v'.wr = v.wr ∧ Frame [⟨State.addr D, 8 * k⟩] v.mem v'.mem := by
  have e₁ := exec_ldrData hd (t := .r7) (r := .r5) (off := c) (x := x) h5 hc hx
  let v₁ := v.setReg .r7 (dw v.mem D x)
  have k₁ : ∀ r, r ≠ .r7 → v₁.gpr r = v.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have hv₁ : Room v₁ := hv.congr (k₁ _ (by decide)) rfl
  have e₂ := exec_ldrAt hv₁ (t := .r9) (r := .r4) (off := a) (k := slot)
    (by rw [k₁ _ (by decide), k₁ _ (by decide), h4]) ha hs
  let v₂ := v₁.setReg .r9 (fw v₁ slot)
  have k₂ : ∀ r, r ≠ .r7 → r ≠ .r9 → v₂.gpr r = v.gpr r := fun r h7 h9 =>
    (RegUpd.gpr_setReg_of_ne _ _ h9).trans (k₁ r h7)
  have e₃ := exec_dp (s := v₂) (op := .eor) (d := .r7) (n := .r7) (o := .reg .r9) (op2_reg _ _)
  let v₃ := v₂.setReg .r7 (dpVal .eor (v₂.gpr .r7) (v₂.gpr .r9))
  have k₃ : ∀ r, r ≠ .r7 → r ≠ .r9 → v₃.gpr r = v.gpr r := fun r h7 h9 =>
    (RegUpd.gpr_setReg_of_ne _ _ h7).trans (k₂ r h7 h9)
  have c7 : v₂.gpr .r7 = dw v.mem D x :=
    (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans (RegUpd.gpr_setReg_self _ _ _)
  have c9 : v₂.gpr .r9 = fw v slot := (RegUpd.gpr_setReg_self _ _ _).trans (fw_setReg _ (by decide) _ _)
  have val : v₃.gpr .r7 = dw v.mem D x ^^^ fw v slot := by
    rw [RegUpd.gpr_setReg_self, c7, c9]; rfl
  have hv₃ : Room v₃ := hv.congr (k₃ _ (by decide) (by decide)) rfl
  have hd₃ : Data v₃ D k := hd.congr (k₃ _ (by decide) (by decide)) rfl
  have e₄ := exec_strData hd₃ (t := .r7) (r := .r5) (off := c) (x := x)
    (by rw [k₃ _ (by decide) (by decide), h5]) hc hx
  refine ⟨stD v₃ D x (v₃.gpr .r7), by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_nil], (dw_stD_self _ _ _ _).trans val,
    fun y hy hxy => dw_stD hd₃ _ hx hy hxy, fun r h7 h9 => (gpr_stD _ _ _ _ r).trans (k₃ r h7 h9),
    fun j hj => ?_, rfl, rfl, stD_frame hd₃ hx _⟩
  rw [fw_stD hv₃ hd₃ hx _ hj]
  exact (fw_setReg _ (by decide) _ _).trans ((fw_setReg _ (by decide) _ _).trans (fw_setReg _ (by decide) _ _))

/-- The body of CFB decryption's copy out, but for the count. -/
def cfbMove : List Instr :=
  [.ldr .r7 .r5 0, .ldr .r9 .r4 0, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 0,
   .ldr .r7 .r5 4, .ldr .r9 .r4 128, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 4]

theorem cfbOutBody_eq : cfbOutBody = cfbMove ++ copyNext := rfl

theorem cfbMove_ok {v : State} (hv : Room v) {D : BitVec 32} {k : Nat} (hd : Data v D k) {i : Nat}
    (hi : i < 32) (hik : i < k) (h4 : v.gpr .r4 = v.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i)))
    (h5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)) :
    ∃ v', runBlock isa cfbMove v = some v' ∧
      dw v'.mem D (8 * i) = dw v.mem D (8 * i) ^^^ fw v (8 + i) ∧
      dw v'.mem D (8 * i + 4) = dw v.mem D (8 * i + 4) ^^^ fw v (40 + i) ∧
      (∀ y, y + 4 ≤ 8 * k → y + 4 ≤ 8 * i ∨ 8 * i + 8 ≤ y → dw v'.mem D y = dw v.mem D y) ∧
      (∀ r, r ≠ .r7 → r ≠ .r9 → v'.gpr r = v.gpr r) ∧
      v'.rd = v.rd ∧ v'.wr = v.wr ∧ Frame [⟨State.addr D, 8 * k⟩] v.mem v'.mem := by
  obtain ⟨v₁, run₁, d₁, o₁, k₁, f₁, rd₁, wr₁, fr₁⟩ := xorIn_ok hv hd (a := 0) (c := 0) (slot := 8 + i)
    (x := 8 * i) (by rw [h4, BitVec.add_zero]) (by decide) (by omega_using [hi])
    (by rw [h5, BitVec.add_zero]) (by decide) (by omega_using [hik])
  have hv₁ : Room v₁ := hv.congr (k₁ _ (by decide) (by decide)) wr₁
  have hd₁ : Data v₁ D k := hd.congr (k₁ _ (by decide) (by decide)) wr₁
  obtain ⟨v₂, run₂, d₂, o₂, k₂, f₂, rd₂, wr₂, fr₂⟩ := xorIn_ok hv₁ hd₁ (a := 128) (c := 4) (slot := 40 + i)
    (x := 8 * i + 4)
    (by rw [k₁ _ (by decide) (by decide), k₁ _ (by decide) (by decide), h4, ptr4hi]) (by decide)
    (by omega_using [hi]) (by rw [k₁ _ (by decide) (by decide), h5, add_ofNat_ofNat]) (by decide)
    (by omega_using [hik])
  refine ⟨v₂, runBlock_cat_some
      (a := [.ldr .r7 .r5 0, .ldr .r9 .r4 0, .dp .eor .r7 .r7 (.reg .r9), .str .r7 .r5 0]) run₁ run₂,
    ?_, ?_, fun y hy hsep => ?_, fun r h7 h9 => (k₂ r h7 h9).trans (k₁ r h7 h9), rd₂.trans rd₁, wr₂.trans wr₁,
    fr₁.trans fr₂⟩
  · rw [o₂ _ (by omega_using [hik]) (by omega_using []), d₁]
  · rw [d₂, o₁ _ (by omega_using [hik]) (by omega_using []), f₁ _ (by omega_using [hi])]
  · rw [o₂ y hy (by omega_using [hsep]), o₁ y hy (by omega_using [hsep])]

/-- After `i` blocks of CFB decryption's copy out from `s`. -/
structure CfbOut (s : State) (D : BitVec 32) (k i : Nat) (v : State) : Prop where
  r4 : v.gpr .r4 = s.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i))
  r5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)
  r6 : v.gpr .r6 = BitVec.ofNat 32 (k - i)
  keep : ∀ r, cbcKept r → v.gpr r = s.gpr r
  put : ∀ b < i, dw v.mem D (8 * b) = dw s.mem D (8 * b) ^^^ fw s (8 + b) ∧
    dw v.mem D (8 * b + 4) = dw s.mem D (8 * b + 4) ^^^ fw s (40 + b)
  rest : ∀ y, 8 * i ≤ y → y + 4 ≤ 8 * k → dw v.mem D y = dw s.mem D y
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  frame : Frame [⟨State.addr D, 8 * k⟩] s.mem v.mem

theorem cfbOut_step {s : State} (h : Room s) {D : BitVec 32} {k : Nat} (hd : Data s D k) (hk : k ≤ 32)
    {i : Nat} (hi : i < k) {v : State} (J : CfbOut s D k i v) :
    ∃ v', runBlock isa cfbOutBody v = some v' ∧ CfbOut s D k (i + 1) v' ∧ v'.z = decide (i + 1 = k) := by
  have g3 : v.gpr .r3 = s.gpr .r3 := J.keep _ (by decide)
  have hv : Room v := h.congr g3 J.wr
  have hdv : Data v D k := hd.congr g3 J.wr
  have fwv : ∀ j < 256, fw v j = fw s j := fun j hj => hd.fw_frame h g3 J.frame hj
  obtain ⟨v₁, run₁, lo₁, hi₁, o₁, k₁, rd₁, wr₁, f₁⟩ := cfbMove_ok hv hdv (i := i)
    (by omega_using [hi, hk]) hi (by rw [J.r4, g3]) J.r5
  obtain ⟨v', run', n4, n5, n6, nz, nk, nm, nrd, nwr, _⟩ := copyNext_ok (s := v₁)
  refine ⟨v', by rw [cfbOutBody_eq]; exact runBlock_cat_some run₁ run',
    ⟨?_, ?_, ?_, fun r hr => ?_, fun b hb => ?_, fun y hy hyk => ?_, nrd.trans (rd₁.trans J.rd),
      nwr.trans (wr₁.trans J.wr), ?_⟩, ?_⟩
  · rw [n4, k₁ _ (by decide) (by decide), J.r4, ptr4]
  · rw [n5, k₁ _ (by decide) (by decide), J.r5, ptr5]
  · rw [n6, k₁ _ (by decide) (by decide), J.r6,
      (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).1]
    congr 1
  · rw [nk r hr.1 hr.2.1 hr.2.2.1, k₁ r hr.2.2.2.1 hr.2.2.2.2.1, J.keep r hr]
  · rw [nm]
    by_cases e : b = i
    · subst e
      rw [lo₁, hi₁, fwv _ (by omega_using [hi, hk]), fwv _ (by omega_using [hi, hk]),
        J.rest _ (Nat.le_refl _) (by omega_using [hi]), J.rest _ (by omega_using []) (by omega_using [hi])]
      exact ⟨rfl, rfl⟩
    · have hb' : b < i := by omega_using [hb, e]
      rw [o₁ _ (by omega_using [hi, hb']) (by omega_using [hb']),
        o₁ _ (by omega_using [hi, hb']) (by omega_using [hb'])]
      exact J.put b hb'
  · rw [nm, o₁ y hyk (by omega_using [hy])]
    exact J.rest y (by omega_using [hy]) hyk
  · rw [nm]; exact J.frame.trans f₁
  · rw [nz, k₁ _ (by decide) (by decide), J.r6,
      (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).2]
    exact decide_eq_decide.mpr (by omega_using [hi])

/-- CFB decryption's copy out: the state words XORed into the batch's blocks. -/
theorem cfbOut_ok {s : State} (h : Room s) {D : BitVec 32} {k : Nat} (hd : Data s D k)
    (hD : s.gpr .r1 = D) (hc : s.gpr .r12 = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) (hk : k ≤ 32) :
    WP isa cfbOut s (CfbOut s D k k) := by
  unfold cfbOut
  apply WP.seq
  obtain ⟨s₁, run₁, i4, i5, i6, ik, im, ird, iwr, _⟩ := copyStart_ok (s := s)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have I0 : CfbOut s D k 0 s₁ :=
    ⟨i4, by rw [i5, hD], by rw [i6, hc]; rfl,
      fun r hr => ik r hr.1 hr.2.1 hr.2.2.1, fun b hb => by omega, fun y _ _ => by rw [im], ird, iwr,
      by rw [im]; exact Frame.refl _ _⟩
  refine WP.loop (M := isa) (fun m v => ∃ i, i < k ∧ m = k - i ∧ CfbOut s D k i v) ?_ k s₁ ⟨0, hk1, rfl, I0⟩
  intro m v ⟨i, hi, hm, J⟩
  obtain ⟨v', run, J', z⟩ := cfbOut_step h hd hk hi J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show isa.eval .ne v' = some !v'.z from rfl, z]
  by_cases e : i + 1 = k
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], k - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, e], rfl, J'⟩

/-! ## A batch of CFB decryption -/

/-- Byte `r` of CFB decryption's block, from the block `B` and the block `P`
before it. -/
def cfbF (K : Schedule) (B P : Block) (r : Nat) : Byte := bbyte B r ^^^ bbyte (encryptBlock K P) r

theorem cfbBatch_ok {s : State} {Sb D I : BitVec 32} {n : Nat} (h : WidePre s Sb D I n) :
    WP isa cfbBatch s (WidePost s Sb D I n (min n 32) cfbF) := by
  have fit := h.data.fit
  have fitI := h.iv.fit
  have hn : n < 2 ^ 32 := by omega_using [fit]
  generalize hk : min n 32 = k
  have hk1 : 1 ≤ k := by have := h.pos; omega_using [hk, this]
  have hk32 : k ≤ 32 := by omega_using [hk]
  have hkn : k ≤ n := by omega_using [hk]
  have hkOf : kOf s = k := by rw [kOf, h.r2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, hk]
  unfold cfbBatch
  apply WP.seq
  refine WP.mono (batchCount_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_
  rw [hkOf] at c₁
  have r3₁ : s₁.gpr .r3 = s.gpr .r3 := g₁ _ (by decide)
  have h₁ : Room s₁ := h.room.congr r3₁ wr₁
  -- the copy in
  apply WP.seq
  refine WP.mono (cfbIn_ok h₁ (h.data.congr r3₁ wr₁) (h.iv.congr r3₁ wr₁) h.apart
    ((g₁ _ (by decide)).trans h.r1) ((g₁ _ (by decide)).trans h.r8) c₁ hk1 hkn hk32)
    fun s₂ ⟨got, iv0, iv4, dat, k₂', rd₂', wr₂', f₂⟩ => ?_
  have k₂ : ∀ r, cbcKept r → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr h12 => (k₂' r hr).trans (g₁ r h12)
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := k₂ _ (by decide) (by decide)
  have wr₂ : s₂.wr = s.wr := wr₂'.trans wr₁
  have rd₂ : s₂.rd = s.rd := rd₂'.trans rd₁
  have h₂ : Room s₂ := h.room.congr r3₂ wr₂
  have F₂ : Frame [headR s 90, ⟨State.addr I, 8 * 1⟩] s.mem s₂.mem := by
    have := f₂
    rw [m₁, stR_congr r3₁] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have K₂ : scheduleAt s₂.mem (State.addr Sb) = scheduleAt s.mem (State.addr Sb) :=
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ F₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.sched.apart.sub_right (Region.sub_prefix (by decide))
      · exact h.ki
  -- the kernel
  apply WP.seq
  refine WP.mono (kernel_ok .encrypt h₂ (h.sched.congr r3₂ rd₂) ((k₂ _ (by decide) (by decide)).trans h.r0))
    fun s₃ ⟨ker, g₃, rd₃, wr₃, f₃⟩ => ?_
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := (g₃ _ (by decide)).trans r3₂
  have wr₃' : s₃.wr = s.wr := wr₃.trans wr₂
  have h₃ : Room s₃ := h.room.congr r3₃ wr₃'
  have F₃ : Frame [headR s 90, ⟨State.addr I, 8 * 1⟩] s.mem s₃.mem :=
    F₂.trans (frame_in (by rw [← headR_congr r3₂]; exact f₃) List.mem_cons_self)
  have d₃ : Data s₃ D k := (h.data.take hkn).congr r3₃ wr₃'
  have c12 : s₃.gpr .r12 = BitVec.ofNat 32 k := by rw [g₃ _ (by decide), k₂' _ (by decide), c₁]
  -- the copy out
  apply WP.seq
  refine WP.mono (cfbOut_ok h₃ d₃ ((g₃ _ (by decide)).trans ((k₂ _ (by decide) (by decide)).trans h.r1)) c12
    hk1 hk32) fun s₄ J => ?_
  obtain ⟨s₅, run₅, n1, n2, nz, n0, n3, m₅, rd₅, wr₅, nk⟩ := advance_ok (s := s₄)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have e12 : s₄.gpr .r12 = BitVec.ofNat 32 k := (J.keep _ (by decide)).trans c12
  have e2 : s₄.gpr .r2 = BitVec.ofNat 32 n :=
    (J.keep _ (by decide)).trans ((g₃ _ (by decide)).trans ((k₂ _ (by decide) (by decide)).trans h.r2))
  obtain ⟨sub, subz⟩ := ofNat_sub hkn hn
  have dS : ∀ x, x + 4 ≤ 8 * n → dw s₃.mem D x = dw s.mem D x := fun x hx =>
    ((h.data.congr r3₂ wr₂).read_frame (c := 90) (by decide) f₃ hx).trans ((dat x hx).trans (by rw [m₁]))
  have hapk : (⟨State.addr I, 8 * 1⟩ : Region).Disjoint ⟨State.addr D, 8 * k⟩ :=
    h.apart.sub_right (Region.sub_prefix (by omega_using [hkn]))
  have dI : ∀ x, x + 4 ≤ 8 * 1 → dw s₄.mem I x = dw s₂.mem I x := fun x hx =>
    (dw_frame_apart fitI hapk J.frame hx).trans
      ((h.iv.congr r3₂ wr₂).read_frame (c := 90) (by decide) f₃ hx)
  refine ⟨by rw [n0, J.keep _ (by decide), g₃ _ (by decide), k₂ _ (by decide) (by decide), h.r0], ?_,
    by rw [n2, e2, e12, sub], by rw [n3, J.keep _ (by decide), r3₃], ?_, by rw [nz, e2, e12, subz],
    by rw [rd₅, J.rd, rd₃, rd₂], by rw [wr₅, J.wr, wr₃'], fun b hb r hr => ?_, ?_, ?_⟩
  · rw [n1, J.keep _ (by decide), g₃ _ (by decide), k₂ _ (by decide) (by decide), h.r1, e12,
      shl3 k (by omega_using [hk32])]
  · rw [nk _ (by decide) (by decide), J.keep _ (by decide), g₃ _ (by decide), k₂ _ (by decide) (by decide), h.r8]
  · have hb32 : b < 32 := by omega_using [hb, hk32]
    have hbn : b < n := by omega_using [hb, hkn]
    obtain ⟨p1, p2⟩ := J.put b hb
    obtain ⟨g1, g2⟩ := got b hb
    have w1 : fw s₃ (8 + b) = words s₃ b := rfl
    have w2 : fw s₃ (40 + b) = words s₃ (32 + b) := by
      rw [words, show spills + (32 + b) = 40 + b by unfold spills; omega_using []]
    have i1 : words s₂ b = (prevW s.mem D I b).1 := g1.trans (by rw [m₁])
    have i2 : words s₂ (32 + b) = (prevW s.mem D I b).2 := by
      rw [words, show spills + (32 + b) = 40 + b by unfold spills; omega_using [], g2, m₁]
    unfold cfbF
    rw [m₅, ← bbyte_blockAt s₄.mem (wAt (State.addr D) b) hr, ← wb_dw s₄.mem fit hbn, p1, p2,
      bbyte_wb_xor _ _ _ _ hr, dS _ (by omega_using [hbn]), dS _ (by omega_using [hbn]), wb_dw s.mem fit hbn, w1,
      w2, ker b hb32, i1, i2, wb_prevW s.mem fit fitI hbn, K₂, blockOut_encrypt]
  · rw [m₅, ← wb_dw0 s₄.mem fitI, dI _ (by decide), dI _ (by decide), iv0, iv4, m₁,
      wb_dw s.mem fit (by omega_using [hk1, hkn])]
  · rw [m₅]
    refine (F₃.sub fun r hr => ?_).trans (frame_in J.frame (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

/-! ## The batches -/

open VG.Proof.TripleDes.Bitslice (blockAt_frame wAt_wAt)

/-- After `done` blocks of the `N` from `s₀`. -/
structure WideInv (F : Schedule → Block → Block → Nat → Byte) (s₀ : State) (Sb D I : BitVec 32)
    (N done : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = Sb
  r1 : s.gpr .r1 = D + BitVec.ofNat 32 (8 * done)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (N - done)
  r3 : s.gpr .r3 = s₀.gpr .r3
  r8 : s.gpr .r8 = I
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  out : ∀ q < done, ∀ r < 8, s.mem (wAt (State.addr D) q + BitVec.ofNat 64 r) =
    F (scheduleAt s₀.mem (State.addr Sb)) (blockAt s₀.mem (wAt (State.addr D) q))
      (prevBlock s₀.mem (State.addr D) (State.addr I) q) r
  rest : ∀ q, done ≤ q → q < N →
    blockAt s.mem (wAt (State.addr D) q) = blockAt s₀.mem (wAt (State.addr D) q)
  ivm : blockAt s.mem (State.addr I) = prevBlock s₀.mem (State.addr D) (State.addr I) done
  frame : Frame [headR s₀ 90, ⟨State.addr D, 8 * N⟩, ⟨State.addr I, 8 * 1⟩] s₀.mem s.mem

/-- What the batches need of the state they start from. -/
structure WideBase (s₀ : State) (Sb D I : BitVec 32) (N : Nat) : Prop where
  room : Room s₀
  sched : Sched s₀ Sb
  data : Data s₀ D N
  iv : Data s₀ I 1
  apart : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr D, 8 * N⟩
  kd : (⟨State.addr Sb, 384⟩ : Region).Disjoint ⟨State.addr D, 8 * N⟩
  ki : (⟨State.addr Sb, 384⟩ : Region).Disjoint ⟨State.addr I, 8⟩

theorem wide_step {F : Schedule → Block → Block → Nat → Byte} {batch : Prog isa}
    (hb : ∀ {s : State} {Sb D I : BitVec 32} {n : Nat}, WidePre s Sb D I n →
      WP isa batch s (WidePost s Sb D I n (min n 32) F))
    {s₀ : State} {Sb D I : BitVec 32} {N : Nat} (B : WideBase s₀ Sb D I N) {done : Nat} (hdone : done < N)
    {s : State} (J : WideInv F s₀ Sb D I N done s) :
    WP isa batch s fun s' => WideInv F s₀ Sb D I N (done + min (N - done) 32) s' ∧
      s'.z = decide (N - done = min (N - done) 32) := by
  have fit := B.data.fit
  have aD : State.addr (D + BitVec.ofNat 32 (8 * done)) = wAt (State.addr D) done :=
    addr_add (by omega_using [fit, hdone])
  have hsub : Data s (D + BitVec.ofNat 32 (8 * done)) (N - done) :=
    (B.data.sub (a := done) (m := N - done) (by omega_using [hdone])).congr J.r3 J.wr
  have hap : (⟨State.addr I, 8⟩ : Region).Disjoint
      ⟨State.addr (D + BitVec.ofNat 32 (8 * done)), 8 * (N - done)⟩ := by
    rw [aD]; exact B.apart.sub_right (Offset.sub_base _ (by omega_using [hdone]))
  -- a block of the data is apart from what a batch writes, but for its own blocks
  have apart : ∀ {k : Nat} (q : Nat), q < N → q < done ∨ done + k ≤ q → k ≤ N - done →
      ∀ r ∈ [headR s 90, ⟨State.addr (D + BitVec.ofNat 32 (8 * done)), 8 * k⟩, ⟨State.addr I, 8 * 1⟩],
        (⟨wAt (State.addr D) q, 8⟩ : Region).Disjoint r := by
    intro k q hq hsep hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [headR_congr J.r3]; exact B.data.block_apart hq (by decide)
    · rw [aD]
      exact Offset.disjoint _ (by omega_using [hsep]) (by omega_using [fit, hq])
        (by omega_using [fit, hdone, hk])
    · exact (B.apart.sub_right (Offset.sub_base _ (by omega_using [hq]))).symm
  have eK : scheduleAt s.mem (State.addr Sb) = scheduleAt s₀.mem (State.addr Sb) :=
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ J.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact B.sched.apart.sub_right (Region.sub_prefix (by decide))
      · exact B.kd
      · exact B.ki
  -- the block before block `done + b`
  have prev : ∀ b, done + b < N → prevBlock s.mem (State.addr (D + BitVec.ofNat 32 (8 * done))) (State.addr I) b =
      prevBlock s₀.mem (State.addr D) (State.addr I) (done + b) := by
    intro b hb
    by_cases h0 : b = 0
    · subst h0; rw [prevBlock, ite_eq_left rfl]; exact J.ivm
    · rw [prevBlock, prevBlock, ite_eq_right h0, ite_eq_right (by omega_using [h0]), aD, wAt_wAt,
        show done + (b - 1) = done + b - 1 by omega_using [h0]]
      exact J.rest _ (by omega_using [h0]) (by omega_using [hb])
  refine WP.mono (hb ⟨B.room.congr J.r3 J.wr, B.sched.congr J.r3 J.rd, hsub, B.iv.congr J.r3 J.wr, hap, B.ki, J.r0,
    J.r1, J.r2, J.r8, by omega_using [hdone]⟩) fun s' P => ⟨⟨P.r0, ?_, ?_, P.r3.trans J.r3, P.r8,
      P.rd.trans J.rd, P.wr.trans J.wr, fun q hq r hr => ?_, fun q hq hqN => ?_, ?_, ?_⟩, P.z⟩
  · rw [P.r1, add_ofNat_ofNat]; congr 2; omega_using []
  · rw [P.r2]; congr 1; omega_using []
  · by_cases hlt : q < done
    · rw [← J.out q hlt r hr, ← bbyte_blockAt s'.mem _ hr, ← bbyte_blockAt s.mem _ hr,
        blockAt_frame P.frame (apart q (by omega_using [hlt, hdone]) (.inl hlt) (Nat.min_le_left _ _))]
    · have hb' : q - done < min (N - done) 32 := by omega_using [hq, hlt]
      have e := P.out (q - done) hb' r hr
      rw [aD, wAt_wAt, show done + (q - done) = q by omega_using [hlt]] at e
      rw [e, eK, J.rest q (by omega_using [hlt]) (by omega_using [hq, hdone]), ← aD,
        prev (q - done) (by omega_using [hq, hlt, hdone]), show done + (q - done) = q by omega_using [hlt]]
  · rw [← J.rest q (by omega_using [hq]) hqN]
    exact blockAt_frame P.frame (apart q hqN (.inr hq) (Nat.min_le_left _ _))
  · have hk1 : 1 ≤ min (N - done) 32 := by omega_using [hdone]
    rw [P.ivo, aD, wAt_wAt, prevBlock, ite_eq_right (by omega_using [hk1]),
      show done + (min (N - done) 32 - 1) = done + min (N - done) 32 - 1 by omega_using [hk1]]
    exact J.rest _ (by omega_using [hk1]) (by omega_using [hdone, hk1])
  · refine J.frame.trans (P.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [headR_congr J.r3]; exact fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [aD]; exact Offset.sub_base _ (by omega_using [hdone])
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem wide_loop {F : Schedule → Block → Block → Nat → Byte} {batch : Prog isa}
    (hb : ∀ {s : State} {Sb D I : BitVec 32} {n : Nat}, WidePre s Sb D I n →
      WP isa batch s (WidePost s Sb D I n (min n 32) F))
    {s₀ : State} {Sb D I : BitVec 32} {N : Nat} (B : WideBase s₀ Sb D I N) (hN : 1 ≤ N)
    (r0 : s₀.gpr .r0 = Sb) (r1 : s₀.gpr .r1 = D) (r2 : s₀.gpr .r2 = BitVec.ofNat 32 N) (r8 : s₀.gpr .r8 = I) :
    WP isa (.loop batch .ne) s₀ (WideInv F s₀ Sb D I N N) := by
  have I0 : WideInv F s₀ Sb D I N 0 s₀ :=
    ⟨r0, by rw [r1, Nat.mul_zero, BitVec.add_zero], r2, rfl, r8, rfl, rfl, fun q hq => by omega,
      fun _ _ _ => rfl, rfl, Frame.refl _ _⟩
  refine WP.loop (M := isa) (fun m v => ∃ done, done < N ∧ m = N - done ∧ WideInv F s₀ Sb D I N done v)
    ?_ N s₀ ⟨0, hN, rfl, I0⟩
  intro m v ⟨done, hdone, hm, J⟩
  refine WP.mono (wide_step hb B hdone J) fun v' ⟨J', z⟩ => ?_
  rw [show isa.eval .ne v' = some !v'.z from rfl, z]
  by_cases e : N - done = min (N - done) 32
  · left
    refine ⟨by rw [decide_eq_true e]; rfl, ?_⟩
    rw [show done + min (N - done) 32 = N by omega_using [hdone, e]] at J'
    exact J'
  · right
    exact ⟨by rw [decide_eq_false e]; rfl, N - (done + min (N - done) 32), by omega_using [hdone, hm],
      done + min (N - done) 32, by omega_using [hdone, e], rfl, J'⟩

/-! ## The function -/

/-- The functions' precondition, with the working space as a stack argument. -/
structure WideFn (s : State) : Prop where
  spF : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (s.gpr .r0), 384⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩,
    ⟨State.addr (stackArg s 0), 1024⟩]
  ki : (⟨State.addr (s.gpr .r0), 384⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 8⟩
  kd : (⟨State.addr (s.gpr .r0), 384⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
  ks : (⟨State.addr (s.gpr .r0), 384⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 1024⟩
  id : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
  is : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 1024⟩
  ds : (⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 1024⟩
  fK : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  fI : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  fD : (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32
  fS : (stackArg s 0).toNat + 1024 ≤ 2 ^ 32

theorem wsaved_slots : Spill.Slots 360 396 Impl.TripleDes.Arm.Wide.saved := by decide

theorem wsaved_restorable : Spill.Restorable .r3 Impl.TripleDes.Arm.Wide.saved := by decide

theorem wsaved_regs : ∀ r ∈ preserved, r ∈ Impl.TripleDes.Arm.Wide.saved.map Prod.fst := by decide

theorem wsaved_ne : ∀ p ∈ Impl.TripleDes.Arm.Wide.saved, p.1 ≠ .r12 := by decide

/-- The arguments where the batches have them. -/
theorem args_ok {s : State} :
    ∃ s', runBlock isa args s = some s' ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r2 ∧
      s'.gpr .r2 = s.gpr .r3 ∧ s'.gpr .r3 = s.gpr .r12 ∧ s'.gpr .r8 = s.gpr .r1 ∧
      s'.z = (s.gpr .r3 == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := exec_mov (s := s) (d := .r8) (o := .reg .r1) (op2_reg _ _)
  let s₁ := s.setReg .r8 (s.gpr .r1)
  have e₂ := exec_mov (s := s₁) (d := .r1) (o := .reg .r2) (op2_reg _ _)
  let s₂ := s₁.setReg .r1 (s₁.gpr .r2)
  have e₃ := exec_mov (s := s₂) (d := .r2) (o := .reg .r3) (op2_reg _ _)
  let s₃ := s₂.setReg .r2 (s₂.gpr .r3)
  have e₄ := exec_mov (s := s₃) (d := .r3) (o := .reg .r12) (op2_reg _ _)
  let s₄ := s₃.setReg .r3 (s₃.gpr .r12)
  have e₅ := exec_cmp (s := s₄) (n := .r2) (o := .imm 0) (op2_imm (by decide))
  have e0 : s₄.gpr .r2 - (0 : BitVec 32) = s₄.gpr .r2 := BitVec.sub_zero _
  refine ⟨subFlags s₄ (s₄.gpr .r2) 0, by
    rw [args, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil], ?_, ?_, ?_, ?_, ?_, ?_, rfl,
    rfl, rfl⟩
  · show s₄.gpr .r0 = _
    simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false]
  · show s₄.gpr .r1 = _
    simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · show s₄.gpr .r2 = _
    simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · show s₄.gpr .r3 = _
    simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · show s₄.gpr .r8 = _
    simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · show (s₄.gpr .r2 - 0 == 0) = _
    rw [e0]
    simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]

theorem exec_ldrSp {s : State} {t : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4) :
    exec (.ldrSp t off) s = some (s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) := by
  simp only [reduceExec, ho, ite_true, State.load32, h, Option.map_some]

theorem wide_wp {F : Schedule → Block → Block → Nat → Byte} {batch : Prog isa}
    (hb : ∀ {s : State} {Sb D I : BitVec 32} {n : Nat}, WidePre s Sb D I n →
      WP isa batch s (WidePost s Sb D I n (min n 32) F)) {s : State} (hp : WideFn s) :
    WP isa (wide batch) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      (∀ q < (s.gpr .r3).toNat, ∀ r < 8,
        s'.mem (wAt (State.addr (s.gpr .r2)) q + BitVec.ofNat 64 r) =
          F (scheduleAt s.mem (State.addr (s.gpr .r0))) (blockAt s.mem (wAt (State.addr (s.gpr .r2)) q))
            (prevBlock s.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r1)) q) r) ∧
      blockAt s'.mem (State.addr (s.gpr .r1)) =
        prevBlock s.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r1)) (s.gpr .r3).toNat := by
  generalize hN : (s.gpr .r3).toNat = N
  have r3N : s.gpr .r3 = BitVec.ofNat 32 N := by rw [← hN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨spF, rd, wr, ki, kd, ks, id, is, ds, fK, fI, fD, fS⟩ := hp
  rw [hN] at wr kd id ds fD
  generalize hB : stackArg s 0 = B at wr ks is ds fS
  have hNlt : N < 2 ^ 32 := by rw [← hN]; exact (s.gpr .r3).isLt
  have inScr : (⟨State.addr B, 1024⟩ : Region) ∈ s.wr := by rw [wr]; simp
  unfold wide enter
  -- the working space's address
  apply WP.seq; apply WP.seq
  have e₀ := exec_ldrSp (s := s) (t := .r12) (off := 0) (by decide)
    ⟨_, List.mem_append_left _ (by rw [rd]; simp), Region.contains_self (stackArgAddr s 0) 4⟩
  let s₁ := s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 0)) 32)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, e₀, runStep_some, runBlock_nil], ?_⟩
  have b₁ : s₁.gpr .r12 = B := (RegUpd.gpr_setReg_self _ _ _).trans hB
  have k₁ : ∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  -- the registers saved
  apply WP.seq
  have hin : ∀ o, 360 ≤ o → o + 4 ≤ 396 →
      InRegions s₁.wr (State.addr (s₁.gpr .r12) + BitVec.ofNat 64 o) 4 := fun o _ ho => by
    rw [b₁]
    exact ⟨_, inScr, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
  refine WP.mono (Spill.save_block_ok (b := .r12) wsaved_slots (s := s₁) (by rw [b₁]; omega_using [fS]) hin)
    fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
  rw [b₁] at m₂
  have F₂ : Frame [⟨State.addr B, 1024⟩] s.mem s₂.mem := by
    rw [m₂]; exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
  have sv₂ : Spill.Saved s₂.mem (State.addr B) s.gpr Impl.TripleDes.Arm.Wide.saved := fun p hp => by
    have := Spill.saveMem_saved (lo := 360) (hi := 396) (State.addr B) s₁.gpr s₁.mem _ wsaved_slots p hp
    rw [m₂, this, k₁ _ (wsaved_ne p hp)]
  -- the arguments
  obtain ⟨t, runt, t0, t1, t2, t3, t8, tz, tm, trd, twr⟩ := args_ok (s := s₂)
  refine WP.of_runBlock ⟨t, runt, ?_⟩
  have g₂' : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂]; exact k₁ r hr
  have c0 : t.gpr .r0 = s.gpr .r0 := t0.trans (g₂' _ (by decide))
  have c1 : t.gpr .r1 = s.gpr .r2 := t1.trans (g₂' _ (by decide))
  have c2 : t.gpr .r2 = BitVec.ofNat 32 N := (t2.trans (g₂' _ (by decide))).trans r3N
  have c3 : t.gpr .r3 = B := t3.trans (by rw [g₂]; exact b₁)
  have c8 : t.gpr .r8 = s.gpr .r1 := t8.trans (g₂' _ (by decide))
  have twr' : t.wr = s.wr := twr.trans wr₂
  have trd' : t.rd = s.rd := trd.trans rd₂
  have Ft : Frame [⟨State.addr B, 1024⟩] s.mem t.mem := by rw [tm]; exact F₂
  have base : WideBase t (s.gpr .r0) (s.gpr .r2) (s.gpr .r1) N :=
    ⟨⟨by rw [frameR, c3, twr']; exact inScr, by rw [c3]; exact fS⟩,
      ⟨by rw [trd', rd]; simp, fK, by rw [frameR, c3]; exact ks⟩,
      ⟨fun x hx => by rw [twr']; exact in_off (by rw [wr]; simp) fD hx (by decide), fD,
        by rw [frameR, c3]; exact ds⟩,
      ⟨fun x hx => by rw [twr']; exact in_off (by rw [wr]; simp) fI (by omega_using [hx]) (by decide), fI,
        by rw [frameR, c3]; exact is⟩, id, kd, ki⟩
  have z : t.z = decide (N = 0) := by
    rw [tz, g₂' _ (by decide), r3N]
    by_cases h0 : N = 0
    · subst h0; rfl
    · have : ¬ BitVec.ofNat 32 N = 0#32 := fun e0 => by
        have := congrArg BitVec.toNat e0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNlt] at this
        exact h0 this
      rw [decide_eq_false h0]
      exact beq_eq_false_iff_ne.mpr this
  -- the batches, if any
  apply WP.seq
  have mid : WP isa (.ite .eq (.block []) (.loop batch .ne)) t
      (WideInv F t (s.gpr .r0) (s.gpr .r2) (s.gpr .r1) N N) := by
    refine WP.ite _ (by rw [show isa.eval .eq t = some t.z from rfl, z]) (fun h0 => ?_) (fun h1 => ?_)
    · have h0 : N = 0 := by simpa using h0
      subst h0
      exact WP.block_nil ⟨c0, by rw [c1, Nat.mul_zero, BitVec.add_zero], c2, rfl, c8, rfl, rfl,
        fun q hq => by omega, fun _ _ _ => rfl, rfl, Frame.refl _ _⟩
    · have h1 : 1 ≤ N := by
        have : ¬ N = 0 := by simpa using h1
        omega_using [this]
      exact wide_loop hb base h1 c0 c1 c2 c8
  refine WP.mono mid fun u J => ?_
  -- the registers back
  have r3u : u.gpr .r3 = B := J.r3.trans c3
  have svu : Spill.Saved u.mem (State.addr (u.gpr .r3)) s.gpr Impl.TripleDes.Arm.Wide.saved := by
    rw [r3u]
    refine (show Spill.Saved t.mem (State.addr B) s.gpr _ by rw [tm]; exact sv₂).frame wsaved_slots J.frame
      fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [headR, c3]; exact Offset.disjoint_base _ (by decide) (by decide)
    · exact (ds.sub_right (Offset.sub_base _ (by decide))).symm
    · exact (is.sub_right (Offset.sub_base _ (by decide))).symm
  have hinu : ∀ o, 360 ≤ o → o + 4 ≤ 396 →
      InRegions (u.rd ++ u.wr) (State.addr (u.gpr .r3) + BitVec.ofNat 64 o) 4 := fun o _ ho => by
    rw [r3u, J.wr, twr']
    exact ⟨_, List.mem_append_right _ inScr, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
  refine WP.mono (Spill.restore_block_ok wsaved_slots wsaved_restorable (by rw [r3u]; omega_using [fS]) hinu svu)
    fun s' ⟨g', _, m', _⟩ => ⟨Spill.restored_of g' wsaved_regs, fun q hq r hr => ?_, ?_⟩
  -- the schedule, the data and the chaining value were as on entry
  all_goals
    have eK : scheduleAt t.mem (State.addr (s.gpr .r0)) = scheduleAt s.mem (State.addr (s.gpr .r0)) :=
      VG.Proof.TripleDes.scheduleAt_eq_of_frame _ Ft fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ks
    have eB : ∀ q < N, blockAt t.mem (wAt (State.addr (s.gpr .r2)) q) =
        blockAt s.mem (wAt (State.addr (s.gpr .r2)) q) := fun q hq =>
      blockAt_frame Ft fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ds.sub_left (Offset.sub_base _ (by omega_using [hq]))
    have eI : blockAt t.mem (State.addr (s.gpr .r1)) = blockAt s.mem (State.addr (s.gpr .r1)) :=
      blockAt_frame Ft fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact is
    have eP : ∀ q, q ≤ N → prevBlock t.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r1)) q =
        prevBlock s.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r1)) q := fun q hq => by
      unfold prevBlock
      by_cases h0 : q = 0
      · rw [ite_eq_left h0, ite_eq_left h0, eI]
      · rw [ite_eq_right h0, ite_eq_right h0, eB _ (by omega_using [hq, h0])]
  · rw [m', J.out q hq r hr, eK, eB q hq, eP q (by omega_using [hq])]
  · rw [m', J.ivm, eP N (Nat.le_refl _)]

end VG.Proof.TripleDes.Arm.Bitsliced
