module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Pass
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Transpose
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
import VerifiedGarbage.Proof.TripleDes.Bitslice.Round
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The bitsliced Triple DES functions on x86 (32-bit)

Blocks as little-endian words, as on ARMv7
(`Proof/TripleDes/Arm/Bitsliced/Ecb.lean`): a block's little-endian
doubleword holds bit `i` of the block, big-endian as `decodeBlock` reads it,
at bit `i ^^^ 56` (`readW_bit`, `blockAt_of_readW`); the lane `b` of the
transposed state words is IP of the block whose words went into the state
words `b` and `32 + b` (`lane_in`), and back (`block_out`).

`batch_wp`: `batch d`, entered with the working space and the schedule as
its stack arguments, replaces each of the 32 blocks in the working space
(block `b` at its word `bufSlot + 2 b`) by its TDEA encryption or decryption
(`blockOut`), restores the caller's registers and keeps the words of the
working space between its own and the blocks.
-/

-- separate module: `Ecb/Verified` uses only `batch_wp` of it, and a change to the ECB loop or to the
-- functions' calls does not check this proof again

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.Spec.TripleDes

theorem xor56_eq : ∀ p < 64, p ^^^ 56 = 8 * (7 - p / 8) + p % 8 := by decide

/-- Bit `j` of the little-endian doubleword at `p`: bit `j % 8` of byte `j / 8`. -/
theorem readW_getLsbD (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (m (p + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [← Mem.extractLsb'_read m p (n := 8) (j := j / 8) (by omega_using [hj]), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.setWidth_eq, show j % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and]
  congr 1; omega_using []

/-- Bit `8 (k + 1) + r` of `x ++ y`, for a byte `y`: bit `8 k + r` of `x`. -/
private theorem getLsbD_append_byte_hi {n : Nat} (x : BitVec n) (y : BitVec 8) (k r : Nat) :
    (x ++ y).getLsbD (8 * (k + 1) + r) = x.getLsbD (8 * k + r) := by
  rw [BitVec.getLsbD_append, ite_eq_right (by omega)]
  congr 1; omega

/-- Bit `8 (7 - q) + r` of a block's big-endian word: bit `r` of byte `q`. -/
theorem catBlock_bit (b : Block) {q r : Nat} (hq : q < 8) (hr : r < 8) :
    (VG.Proof.TripleDes.catBlock b).getLsbD (8 * (7 - q) + r) = b[q].getLsbD r := by
  have hcases : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  have lo : ∀ {n : Nat} (x : BitVec n) (y : BitVec 8), (x ++ y).getLsbD (8 * 0 + r) = y.getLsbD r :=
    fun x y => by rw [Nat.mul_zero, Nat.zero_add, BitVec.getLsbD_append, ite_eq_left hr]
  unfold VG.Proof.TripleDes.catBlock
  -- byte `q` is under `7 - q` appends: no `split` of the eight nested `if`s
  rcases hcases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · iterate 7 refine (getLsbD_append_byte_hi _ _ _ r).trans ?_
    rw [Nat.mul_zero, Nat.zero_add]
  · iterate 6 refine (getLsbD_append_byte_hi _ _ _ r).trans ?_
    exact lo _ _
  · iterate 5 refine (getLsbD_append_byte_hi _ _ _ r).trans ?_
    exact lo _ _
  · iterate 4 refine (getLsbD_append_byte_hi _ _ _ r).trans ?_
    exact lo _ _
  · iterate 3 refine (getLsbD_append_byte_hi _ _ _ r).trans ?_
    exact lo _ _
  · iterate 2 refine (getLsbD_append_byte_hi _ _ _ r).trans ?_
    exact lo _ _
  · refine (getLsbD_append_byte_hi _ _ _ r).trans ?_
    exact lo _ _
  · exact lo _ _

/-- The little-endian doubleword of a block, bit by bit. -/
theorem readW_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (decodeBlock (blockAt m p)).getLsbD (j ^^^ 56) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, xor56_eq j hj,
    catBlock_bit _ (by omega_using [hj]) (Nat.mod_lt _ (by decide)), readW_getLsbD m p hj]
  simp [blockAt]

/-- A doubleword whose bits are those of `x` at `j ^^^ 56` is the little-endian
doubleword of the block `encodeBlock x`. -/
theorem blockAt_of_readW (m : Mem) (p : Addr) (x : BitVec 64)
    (h : ∀ j < 64, (m.readW p 64).getLsbD j = x.getLsbD (j ^^^ 56)) :
    blockAt m p = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  have hj : 8 * i + r < 64 := by omega_using [hi, hr]
  have e := h (8 * i + r) hj
  rw [readW_getLsbD m p hj, xor56_eq _ hj, show (8 * i + r) / 8 = i by omega_using [hr],
    show (8 * i + r) % 8 = r by omega_using [hr]] at e
  rw [e]
  simp only [BitVec.getLsbD_setWidth, hr, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]

/-- A doubleword's bits, from its two words. -/
theorem readW64_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = if j < 32 then (m.readW p 32).getLsbD j
      else (m.readW (p + BitVec.ofNat 64 4) 32).getLsbD (j - 32) := by
  rw [Mem.readW_lo32 rfl, Mem.readW_hi32 rfl]
  split
  · rename_i h; simp only [BitVec.getLsbD_setWidth, h, decide_true, Bool.true_and]
  · rename_i h
    simp only [BitVec.getLsbD_extractLsb', show j - 32 < 32 by omega_using [hj], decide_true,
      Bool.true_and, show 32 + (j - 32) = j by omega_using [h]]

open VG.Proof.TripleDes.Bitslice (ipLane ipLane_bit xor56_xor56 ipWord_lt fp_ipWord)
open VG.Impl.TripleDes.Bitslice (ipWord)
open VG.Proof.TripleDes (permute_bit)

/-- Lane `b` of words whose bits `b` are those of a block's little-endian
doubleword is IP of the block. -/
theorem ipLane_of_bits {w : Nat} (W : Nat → BitVec w) (x : BitVec 64) (b : Nat)
    (hW : ∀ j < 64, (W j).getLsbD b = x.getLsbD (j ^^^ 56)) : ipLane W b = permute ip x := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hw := ipWord_lt t ht
  rw [ipLane_bit _ _ ht, permute_bit ip x (by decide) t ht, hW _ hw]
  simp only [ipWord, xor56_xor56]

/-- The bits `b` of the words are those of the little-endian doubleword of
FP of lane `b`. -/
theorem bits_of_ipLane {w : Nat} (W : Nat → BitVec w) (b : Nat) :
    ∀ j < 64, (W j).getLsbD b = (permute fp (ipLane W b)).getLsbD (j ^^^ 56) := by
  intro j hj
  have hj' : j ^^^ 56 < 64 := Nat.xor_lt_two_pow (n := 6) hj (by decide)
  obtain ⟨lo, -⟩ := VG.Proof.TripleDes.Bitslice.fp_bounds _ hj'
  have ht : 64 - fp.getD (63 - (j ^^^ 56)) 1 < 64 := by omega_using [lo]
  rw [permute_bit fp _ (by decide) _ hj', ipLane_bit _ _ ht, fp_ipWord _ hj', xor56_xor56]

open VG.X86 VG.X86.Straight VG.X86.Wp VG.Impl.TripleDes.X86.Bitslice
open VG.Proof.TripleDes.Bitslice (tdeaW blockOut ipLane_congr tdeaW_lane blockOut_cores)

/-- After the transposition, lane `b` is IP of the block whose words went
into the state words `b` and `32 + b`. -/
theorem lane_in (m : Mem) (p : Addr) (W : Nat → BitVec 32) {b : Nat} (hb : b < 32)
    (lo : W b = m.readW p 32) (hi : W (32 + b) = m.readW (p + BitVec.ofNat 64 4) 32) :
    ipLane (transposeW W) b = permute ip (decodeBlock (blockAt m p)) := by
  refine ipLane_of_bits _ _ b fun j hj => ?_
  rw [← readW_bit m p hj, readW64_bit m p hj]
  simp only [transposeW, VG.Bitslice.getLsbD_ofBits, hb, decide_true, Bool.true_and]
  split
  · rename_i h
    rw [Nat.div_eq_of_lt h, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt h, lo]
  · rename_i h
    rw [show j / 32 = 1 by omega_using [h, hj], Nat.mul_one, show j % 32 = j - 32 by omega_using [h, hj], hi]

/-- The block whose words are the state words `b` and `32 + b` after the
transposition back is the encoding of FP of lane `b`. -/
theorem block_out (m : Mem) (p : Addr) (W : Nat → BitVec 32) {b : Nat} (hb : b < 32)
    (lo : m.readW p 32 = transposeW W b)
    (hi : m.readW (p + BitVec.ofNat 64 4) 32 = transposeW W (32 + b)) :
    blockAt m p = encodeBlock (permute fp (ipLane W b)) := by
  refine blockAt_of_readW m p _ fun j hj => ?_
  rw [← bits_of_ipLane W b j hj, readW64_bit m p hj]
  split
  · rename_i h
    rw [lo]
    simp only [transposeW, VG.Bitslice.getLsbD_ofBits, h, decide_true, Bool.true_and]
    rw [Nat.div_eq_of_lt hb, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hb]
  · rename_i h
    rw [hi]
    simp only [transposeW, VG.Bitslice.getLsbD_ofBits, show j - 32 < 32 by omega_using [hj], decide_true,
      Bool.true_and]
    rw [show (32 + b) / 32 = 1 by omega_using [hb], show (32 + b) % 32 = b by omega_using [hb], Nat.mul_one,
      show 32 + (j - 32) = j by omega_using [h]]

/-- A block through the state words: in, transposed, through the passes,
transposed back, and out. -/
theorem batch_block (K : Schedule) (d : Direction) (m m' : Mem) (p : Addr)
    (W₃ W₄ W₅ W₆ : Nat → BitVec 32) {b : Nat} (hb : b < 32)
    (lo : W₃ b = m.readW p 32) (hi : W₃ (32 + b) = m.readW (p + BitVec.ofNat 64 4) 32)
    (h₄ : ∀ x < 64, W₄ x = transposeW W₃ x) (h₅ : ∀ x < 64, W₅ x = tdeaW K d W₄ x)
    (h₆ : ∀ x < 64, W₆ x = transposeW W₅ x)
    (lo' : m'.readW p 32 = W₆ b) (hi' : m'.readW (p + BitVec.ofNat 64 4) 32 = W₆ (32 + b)) :
    blockAt m' p = blockOut K d (blockAt m p) := by
  rw [blockOut_cores, block_out m' p W₅ hb (lo'.trans (h₆ b (by omega_using [hb])))
    (hi'.trans (h₆ _ (by omega_using [hb]))), ipLane_congr h₅ b, tdeaW_lane K d W₄ hb,
    ipLane_congr h₄ b, lane_in m p W₃ hb lo hi]

/-! ## Words of the working space -/

/-- `mov d, [ebp + 4k]` -/
theorem wp_ldFw {s : State} (h : Room s) {k : Nat} (hk : k < wsWords) {d : Reg} {is : List Instr}
    {Q : State → Prop} (kont : ∀ s', Upd s s' d (fw s k) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (ws k)) :: is)) s Q :=
  wp_ldm (B := s.gpr .ebp) rfl (slot_rd h hk) kont

/-- `mov [ebp + 4k], r` -/
theorem wp_stFw {s : State} (h : Room s) {k : Nat} (hk : k < wsWords) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (kont : ∀ s', (∀ j < wsWords, fw s' j = if j = k then s.gpr r else fw s j) → s'.gpr = s.gpr →
      Kept (k + 1) s s' → WP isa (.block is) s' Q) :
    WP isa (.block (.store (ws k) r :: is)) s Q := by
  refine wp_stm (B := s.gpr .ebp) rfl (slot_in h hk) fun s' u => ?_
  have m : s'.mem = s.mem.writeW (wordAddr (s.gpr .ebp) k) (s.gpr r) := u.mem
  have b : s'.gpr .ebp = s.gpr .ebp := by rw [u.gpr]
  exact kont s' (fun j hj => fw_write h m b hk hj) u.gpr
    ⟨b, by rw [u.gpr], u.rd, u.wr, by rw [m]; exact stFw_frame h (Nat.lt_succ_self k) hk _⟩

theorem bufWord_bounds : ∀ j < 64, bufSlot ≤ bufWord j ∧ bufWord j < wsWords := by decide

theorem bufWord_inj : ∀ j < 64, 32 * ((bufWord j - bufSlot) % 2) + (bufWord j - bufSlot) / 2 = j := by
  decide

theorem bufWord_lo {b : Nat} (hb : b < 32) : bufWord b = bufSlot + 2 * b := by
  unfold bufWord; omega_using [hb]

theorem bufWord_hi {b : Nat} (hb : b < 32) : bufWord (32 + b) = bufSlot + 2 * b + 1 := by
  unfold bufWord; omega_using [hb]

/-! ## The blocks to the state words, and back -/

def loadN (n : Nat) : List Instr :=
  (List.range n).flatMap fun j => [.mov .eax (.mem (ws (bufWord j))), .store (ws (stSlot j)) .eax]

theorem loadN_succ (n : Nat) :
    loadN (n + 1) = loadN n ++
      ([.mov .eax (.mem (ws (bufWord n))), .store (ws (stSlot n)) .eax] : List Instr) := by
  simp only [loadN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem loadN_ok {n : Nat} (hn : n ≤ 64) {s : State} (h : Room s) :
    WP isa (.block (loadN n)) s fun s' =>
      (∀ j < n, words s' j = fw s (bufWord j)) ∧
      (∀ k, spills + 64 ≤ k → k < wsWords → fw s' k = fw s k) ∧ Kept (spills + 64) s s' := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, Kept.refl _ _⟩
  | succ n ih =>
    rw [loadN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s₁ ⟨w₁, o₁, k₁⟩ => ?_
    have h₁ : Room s₁ := k₁.room h
    obtain ⟨blo, bhi⟩ := bufWord_bounds n (by omega_using [hn])
    have hst : stSlot n < wsWords := by unfold stSlot spills wsWords; omega_using [hn]
    refine wp_ldFw h₁ bhi fun s₂ u₂ => ?_
    have h₂ : Room s₂ := h₁.congr (u₂.other _ (by decide)) u₂.wr
    refine wp_stFw h₂ hst fun s₃ f₃ g₃ k₃ => WP.block_nil ?_
    have f : ∀ j < wsWords, fw s₃ j = if j = stSlot n then fw s (bufWord n) else fw s₁ j := by
      intro j hj
      rw [f₃ j hj, u₂.gpr, o₁ _ (by unfold spills; unfold bufSlot at blo; omega_using [blo]) bhi]
      refine congrArg (fun t => if j = stSlot n then _ else t) ?_
      rw [fw, fw, u₂.other _ (by decide), u₂.mem]
    refine ⟨fun j hj => ?_, fun k hk hk' => ?_, k₁.trans ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [words, f _ (by unfold spills wsWords; omega_using [hj, hn])]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rw [ite_eq_right (by unfold stSlot; omega_using [hlt])]; exact w₁ j hlt
      · exact ite_eq_left rfl
    · rw [f k hk', ite_eq_right (by unfold stSlot; omega_using [hk, hn])]; exact o₁ k hk hk'
    · rw [k₃.ebp]; exact u₂.other _ (by decide)
    · rw [k₃.esp]; exact u₂.other _ (by decide)
    · rw [k₃.rd, u₂.rd]
    · rw [k₃.wr, u₂.wr]
    · have := headR_mono (n' := spills + 64) (by unfold stSlot; omega_using [hn]) k₃.frame
      rw [headR_congr (u₂.other _ (by decide)), u₂.mem] at this
      exact this

def storeN (n : Nat) : List Instr :=
  (List.range n).flatMap fun j => [.mov .eax (.mem (ws (stSlot j))), .store (ws (bufWord j)) .eax]

theorem storeN_succ (n : Nat) :
    storeN (n + 1) = storeN n ++
      ([.mov .eax (.mem (ws (stSlot n))), .store (ws (bufWord n)) .eax] : List Instr) := by
  simp only [storeN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem storeN_ok {n : Nat} (hn : n ≤ 64) {s : State} (h : Room s) :
    WP isa (.block (storeN n)) s fun s' =>
      (∀ j < n, fw s' (bufWord j) = words s j) ∧
      (∀ k, k < bufSlot → fw s' k = fw s k) ∧ Kept wsWords s s' := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl, Kept.refl _ _⟩
  | succ n ih =>
    rw [storeN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s₁ ⟨w₁, o₁, k₁⟩ => ?_
    have h₁ : Room s₁ := k₁.room h
    obtain ⟨blo, bhi⟩ := bufWord_bounds n (by omega_using [hn])
    have hst : stSlot n < wsWords := by unfold stSlot spills wsWords; omega_using [hn]
    refine wp_ldFw h₁ hst fun s₂ u₂ => ?_
    have h₂ : Room s₂ := h₁.congr (u₂.other _ (by decide)) u₂.wr
    refine wp_stFw h₂ bhi fun s₃ f₃ g₃ k₃ => WP.block_nil ?_
    have f : ∀ j < wsWords, fw s₃ j = if j = bufWord n then words s n else fw s₁ j := by
      intro j hj
      rw [f₃ j hj, u₂.gpr, show stSlot n = spills + n from rfl,
        o₁ _ (by unfold spills bufSlot; omega_using [hn])]
      refine congrArg (fun t => if j = bufWord n then _ else t) ?_
      rw [fw, fw, u₂.other _ (by decide), u₂.mem]
    refine ⟨fun j hj => ?_, fun k hk => ?_, k₁.trans ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [f _ (bufWord_bounds j (by omega_using [hj, hn])).2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rw [ite_eq_right fun e => by
          have a := bufWord_inj j (by omega_using [hlt, hn])
          have b := bufWord_inj n (by omega_using [hn])
          rw [e] at a; omega_using [a, b, hlt]]
        exact w₁ j hlt
      · exact ite_eq_left rfl
    · rw [f k (by unfold wsWords; unfold bufSlot at hk; omega_using [hk]),
        ite_eq_right (by omega_using [hk, blo])]
      exact o₁ k hk
    · rw [k₃.ebp]; exact u₂.other _ (by decide)
    · rw [k₃.esp]; exact u₂.other _ (by decide)
    · rw [k₃.rd, u₂.rd]
    · rw [k₃.wr, u₂.wr]
    · have := headR_mono (n' := wsWords) (by omega_using [bhi]) k₃.frame
      rw [headR_congr (u₂.other _ (by decide)), u₂.mem] at this
      exact this

/-! ## Entry and exit -/

theorem enter_ok {s : State} {A Sb : BitVec 32}
    (a0 : s.mem.readW (addr (s.gpr .esp) 4) 32 = A) (a1 : s.mem.readW (addr (s.gpr .esp) 8) 32 = Sb)
    (r0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (r1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hw : (⟨A.setWidth 64, 4 * wsWords⟩ : Region) ∈ s.wr) (hf : A.toNat + 4 * wsWords ≤ 2 ^ 32) :
    WP isa (.block enter) s fun s' =>
      Room s' ∧ s'.gpr .ebp = A ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      fw s' schedSlot = Sb ∧ fw s' 83 = s.gpr .ebx ∧ fw s' 84 = s.gpr .esi ∧ fw s' 85 = s.gpr .edi ∧
      fw s' 86 = s.gpr .ebp ∧
      (∀ j < wsWords, j < schedSlot ∨ 86 < j → fw s' j = s.mem.readW (wordAddr A j) 32) ∧
      Frame [⟨A.setWidth 64, 4 * 87⟩] s.mem s'.mem := by
  unfold enter
  refine wp_ldm (B := s.gpr .esp) rfl r0 fun s₁ u₁ => ?_
  refine wp_ldm (B := s.gpr .esp) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact r1) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .ebp = A := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; exact a0
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have h₄ : Room s₄ := ⟨by rw [frameR, b₄, wr₄]; exact hw, by rw [b₄]; exact hf⟩
  have ecx₄ : s₄.gpr .ecx = Sb := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]; exact a1
  have ebx₄ : s₄.gpr .ebx = s.gpr .ebx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have esi₄ : s₄.gpr .esi = s.gpr .esi := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have edi₄ : s₄.gpr .edi = s.gpr .edi := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have edx₄ : s₄.gpr .edx = s.gpr .ebp := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  have esp₄ : s₄.gpr .esp = s.gpr .esp := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stFw h₄ (by decide) fun s₅ f₅ g₅ k₅ => ?_
  have h₅ := k₅.room h₄
  refine wp_stFw h₅ (by decide) fun s₆ f₆ g₆ k₆ => ?_
  have h₆ := k₆.room h₅
  refine wp_stFw h₆ (by decide) fun s₇ f₇ g₇ k₇ => ?_
  have h₇ := k₇.room h₆
  refine wp_stFw h₇ (by decide) fun s₈ f₈ g₈ k₈ => ?_
  have h₈ := k₈.room h₇
  refine wp_stFw h₈ (by decide) fun s₉ f₉ g₉ k₉ => WP.block_nil ?_
  have kk : Kept 87 s₄ s₉ := (k₅.mono (by decide)).trans ((k₆.mono (by decide)).trans
    ((k₇.mono (by decide)).trans ((k₈.mono (by decide)).trans k₉)))
  have f : ∀ j < wsWords, fw s₉ j = if j = 86 then s.gpr .ebp else if j = 85 then s.gpr .edi
      else if j = 84 then s.gpr .esi else if j = 83 then s.gpr .ebx else if j = schedSlot then Sb
      else fw s₄ j := by
    intro j hj
    rw [f₉ j hj, f₈ j hj, f₇ j hj, f₆ j hj, f₅ j hj, g₈, g₇, g₆, g₅, edx₄, edi₄, esi₄, ebx₄, ecx₄]
  refine ⟨kk.room h₄, kk.ebp.trans b₄, kk.esp.trans esp₄, kk.rd.trans rd₄, kk.wr.trans wr₄,
    f schedSlot (by decide), f 83 (by decide), f 84 (by decide), f 85 (by decide), f 86 (by decide),
    fun j hj hr => ?_, ?_⟩
  · unfold schedSlot at hr
    rw [f j hj, ite_eq_right (by omega_using [hr]), ite_eq_right (by omega_using [hr]),
      ite_eq_right (by omega_using [hr]), ite_eq_right (by omega_using [hr]),
      ite_eq_right (by unfold schedSlot; omega_using [hr]), fw, b₄, m₄]
  · have := kk.frame
    rw [headR, b₄, m₄] at this; exact this

theorem leave_ok {s : State} (h : Room s) :
    WP isa (.block leave) s fun s' =>
      s'.gpr .ebx = fw s 83 ∧ s'.gpr .esi = fw s 84 ∧ s'.gpr .edi = fw s 85 ∧ s'.gpr .ebp = fw s 86 ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  show WP isa (.block [.mov .ebx (.mem (ws 83)), .mov .esi (.mem (ws 84)), .mov .edi (.mem (ws 85)),
    .mov .ebp (.mem (ws 86))]) s _
  refine wp_ldFw h (by decide) fun s₁ u₁ => ?_
  have h₁ : Room s₁ := h.congr (u₁.other _ (by decide)) u₁.wr
  have e₁ : ∀ k, fw s₁ k = fw s k := fun k => by rw [fw, fw, u₁.other _ (by decide), u₁.mem]
  refine wp_ldFw h₁ (by decide) fun s₂ u₂ => ?_
  have h₂ : Room s₂ := h₁.congr (u₂.other _ (by decide)) u₂.wr
  have e₂ : ∀ k, fw s₂ k = fw s k := fun k => by rw [fw, u₂.other _ (by decide), u₂.mem]; exact e₁ k
  refine wp_ldFw h₂ (by decide) fun s₃ u₃ => ?_
  have h₃ : Room s₃ := h₂.congr (u₃.other _ (by decide)) u₃.wr
  have e₃ : ∀ k, fw s₃ k = fw s k := fun k => by rw [fw, u₃.other _ (by decide), u₃.mem]; exact e₂ k
  refine wp_ldFw h₃ (by decide) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, e₁]
  · rw [u₄.other _ (by decide), u₃.gpr, e₂]
  · rw [u₄.gpr, e₃]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The function -/

/-- What `batch` needs: its two arguments, the working space at `A` and the
schedule at `Sb`. -/
structure BatchPre (s : State) (A Sb : BitVec 32) : Prop where
  a0 : s.mem.readW (addr (s.gpr .esp) 4) 32 = A
  a1 : s.mem.readW (addr (s.gpr .esp) 8) 32 = Sb
  r0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4
  r1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4
  space : (⟨A.setWidth 64, 4 * wsWords⟩ : Region) ∈ s.wr
  fit : A.toNat + 4 * wsWords ≤ 2 ^ 32
  key : (⟨Sb.setWidth 64, 384⟩ : Region) ∈ s.rd
  keyFit : Sb.toNat + 384 ≤ 2 ^ 32
  apart : (⟨Sb.setWidth 64, 384⟩ : Region).Disjoint ⟨A.setWidth 64, 4 * wsWords⟩

/-- What `batch d` does. -/
structure BatchPost (d : Direction) (s : State) (A Sb : BitVec 32) (s' : State) : Prop where
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨A.setWidth 64, 4 * wsWords⟩] s.mem s'.mem
  mid : ∀ k, 87 ≤ k → k < bufSlot → s'.mem.readW (wordAddr A k) 32 = s.mem.readW (wordAddr A k) 32
  blocks : ∀ b < 32, blockAt s'.mem (wordAddr A (bufSlot + 2 * b)) =
    blockOut (scheduleAt s.mem (Sb.setWidth 64)) d (blockAt s.mem (wordAddr A (bufSlot + 2 * b)))

theorem wordAddr_succ {A : BitVec 32} {k : Nat} (h : A.toNat + 4 * (k + 1) < 2 ^ 32) :
    wordAddr A (k + 1) = wordAddr A k + BitVec.ofNat 64 4 := by
  rw [wordAddr, wordAddr, addr_eq (by omega_using [h]), addr_eq (by omega_using [h]), VG.Offset.add_add,
    Nat.mul_succ]

theorem batch_wp (d : Direction) {s : State} {A Sb : BitVec 32} (hp : BatchPre s A Sb) :
    WP isa (batch d) s (BatchPost d s A Sb) := by
  unfold batch
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok hp.a0 hp.a1 hp.r0 hp.r1 hp.space hp.fit)
    fun s₁ ⟨h₁, b₁, sp₁, rd₁, wr₁, sc₁, x83, x84, x85, x86, o₁, fr₁⟩ => ?_
  refine WP.mono (loadN_ok (Nat.le_refl 64) h₁) fun s₂ ⟨w₂, o₂, k₂⟩ => ?_
  have h₂ : Room s₂ := k₂.room h₁
  apply WP.seq
  obtain ⟨s₃, run₃, w₃, b₃, sp₃, rd₃, wr₃, f₃⟩ := transpose_ok h₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₃ : Kept (spills + 64) s₂ s₃ := ⟨b₃, sp₃, rd₃, wr₃, f₃⟩
  have h₃ : Room s₃ := k₃.room h₂
  have k₁₃ : Kept (spills + 64) s₁ s₃ := k₂.trans k₃
  have hs₁ : Sched s₁ Sb :=
    ⟨by rw [rd₁]; exact hp.key, hp.keyFit, by rw [frameR, b₁]; exact hp.apart⟩
  apply WP.seq
  refine WP.mono (passes_ok d h₃ (k₁₃.sched hs₁) ((k₁₃.fw h₁ (by decide) (by decide)).trans sc₁))
    fun s₄ ⟨w₄, k₄⟩ => ?_
  have h₄ : Room s₄ := k₄.room h₃
  apply WP.seq
  obtain ⟨s₅, run₅, w₅, b₅, sp₅, rd₅, wr₅, f₅⟩ := transpose_ok h₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have k₅ : Kept (spills + 64) s₄ s₅ := ⟨b₅, sp₅, rd₅, wr₅, f₅⟩
  have h₅ : Room s₅ := k₅.room h₄
  rw [WP.block_append_iff]
  refine WP.mono (storeN_ok (Nat.le_refl 64) h₅) fun s₆ ⟨w₆, o₆, k₆⟩ => ?_
  have h₆ : Room s₆ := k₆.room h₅
  refine WP.mono (leave_ok h₆) fun s₇ ⟨ebx₇, esi₇, edi₇, ebp₇, esp₇, m₇, rd₇, wr₇⟩ => ?_
  -- the whole run, from the entry's working space on
  have k₁₆ : Kept wsWords s₁ s₆ :=
    (k₁₃.mono (by decide)).trans ((k₄.mono (by decide)).trans ((k₅.mono (by decide)).trans k₆))
  -- the words from `schedSlot` up to the blocks are kept from `s₁` on
  have mid : ∀ k, schedSlot ≤ k → k < bufSlot → fw s₆ k = fw s₁ k := by
    intro k hlo hhi
    have hk : k < wsWords := by unfold wsWords; unfold bufSlot at hhi; omega_using [hhi]
    unfold schedSlot at hlo
    rw [o₆ k hhi, k₅.fw h₄ (by unfold spills; omega_using [hlo]) hk, k₄.fw h₃ hlo hk,
      k₁₃.fw h₁ (by unfold spills; omega_using [hlo]) hk]
  have fr : Frame [⟨A.setWidth 64, 4 * wsWords⟩] s.mem s₇.mem := by
    rw [m₇]
    refine (fr₁.sub fun r hr => ?_).trans (by have := k₁₆.frame; rwa [headR, b₁] at this)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have fwA : ∀ k, s₇.mem.readW (wordAddr A k) 32 = fw s₆ k := fun k => by rw [m₇, fw, k₁₆.ebp, b₁]
  have sched : scheduleAt s₃.mem (Sb.setWidth 64) = scheduleAt s.mem (Sb.setWidth 64) := by
    rw [scheduleAt_frame hs₁ (by decide) k₁₃.frame]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ fr₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.apart.sub_right (Region.sub_prefix (by decide))
  refine ⟨fun r hr => ?_, by rw [rd₇, k₁₆.rd, rd₁], by rw [wr₇, k₁₆.wr, wr₁], fr, fun k hlo hhi => ?_,
    fun b hb => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ebx₇, mid 83 (by decide) (by decide), x83]
    · rw [esi₇, mid 84 (by decide) (by decide), x84]
    · rw [edi₇, mid 85 (by decide) (by decide), x85]
    · rw [ebp₇, mid 86 (by decide) (by decide), x86]
    · rw [esp₇, k₁₆.esp, sp₁]
  · rw [fwA, mid k (by unfold schedSlot; omega_using [hlo]) hhi,
      o₁ k (by unfold wsWords; unfold bufSlot at hhi; omega_using [hhi]) (.inr (by omega_using [hlo]))]
  · have fit := hp.fit
    have hb1 : bufSlot + 2 * b + 1 < wsWords := by unfold bufSlot wsWords; omega_using [hb]
    have hi4 : wordAddr A (bufSlot + 2 * b) + BitVec.ofNat 64 4 = wordAddr A (bufSlot + 2 * b + 1) :=
      (wordAddr_succ (by unfold wsWords at fit hb1; omega_using [fit, hb1])).symm
    have src : ∀ j < 64, words s₂ j = s.mem.readW (wordAddr A (bufWord j)) 32 := fun j hj => by
      obtain ⟨blo, bhi⟩ := bufWord_bounds j hj
      rw [w₂ j hj, o₁ _ bhi (.inr (by unfold bufSlot at blo; omega_using [blo]))]
    refine batch_block _ d s.mem s₇.mem _ (words s₂) (words s₃) (words s₄) (words s₅) hb ?_ ?_ w₃
      (fun x hx => by rw [w₄ x hx, sched]) w₅ ?_ ?_
    · rw [src b (by omega_using [hb]), bufWord_lo hb]
    · rw [src _ (by omega_using [hb]), bufWord_hi hb, hi4]
    · rw [fwA, ← bufWord_lo hb, w₆ b (by omega_using [hb])]
    · rw [hi4, fwA, ← bufWord_hi hb, w₆ _ (by omega_using [hb])]

end VG.Proof.TripleDes.X86.Bitsliced
