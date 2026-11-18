module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Pass
public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Transpose
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.TCB.Arm.Target

/-!
# Bitsliced Triple DES ECB on ARMv7

Blocks as little-endian words (`readW_bit`, `blockAt_of_readW`: a block's
little-endian doubleword holds bit `i` of the block, big-endian as
`decodeBlock` reads it, at bit `i ^^^ 56`), which the code loads and stores
a word at a time.

A batch of `k = min(n, 32)` blocks (`kOf`) is copied into the state words,
transposed (lane `b` is then IP of block `b`), put through the three
passes, transposed back and copied out; then the data pointer `r1` moves
past it and the count `r2` drops by `k`: each block becomes its TDEA
encryption or decryption (`batch_ok`).

`ecb_wp`: with the working space at `r3`, the caller's `r4`–`r11` and `lr`
saved in it, the batches (`loop_ok`), and the registers restored.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

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

open VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm.Bitslice
open VG.Proof.TripleDes.Bitslice (tdeaW blockOut wAt)
open VG.Proof.X25519.Arm (dpVal op2_imm op2_reg op2_lsr op2_lsl)

/-! ## The data -/

/-- The word of the data at `D + x`. -/
def dw (m : Mem) (D : BitVec 32) (x : Nat) : BitVec 32 :=
  m.readW (State.addr (D + BitVec.ofNat 32 x)) 32

/-- The data: the `n` blocks at `D`, writable, apart from the working space
and not wrapping around. -/
structure Data (s : State) (D : BitVec 32) (n : Nat) : Prop where
  wr : ∀ x, x + 4 ≤ 8 * n → InRegions s.wr (State.addr (D + BitVec.ofNat 32 x)) 4
  fit : D.toNat + 8 * n ≤ 2 ^ 32
  apart : (⟨State.addr D, 8 * n⟩ : Region).Disjoint (frameR s)

theorem Data.congr {s s' : State} {D : BitVec 32} {n : Nat} (h : Data s D n)
    (hb : s'.gpr .r3 = s.gpr .r3) (hw : s'.wr = s.wr) : Data s' D n where
  wr := by rw [hw]; exact h.wr
  fit := h.fit
  apart := by rw [frameR, hb]; exact h.apart

theorem Data.rd {s : State} {D : BitVec 32} {n : Nat} (h : Data s D n) {x : Nat} (hx : x + 4 ≤ 8 * n) :
    InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 x)) 4 :=
  let ⟨r, hr, hc⟩ := h.wr x hx; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word of the data is in the data's region. -/
theorem Data.contains {s : State} {D : BitVec 32} {n : Nat} (h : Data s D n) {x : Nat}
    (hx : x + 4 ≤ 8 * n) :
    (⟨State.addr D, 8 * n⟩ : Region).Contains (State.addr (D + BitVec.ofNat 32 x)) 4 :=
  contains_off h.fit hx (by decide)

/-- The blocks from `a` on. -/
theorem Data.sub {s : State} {D : BitVec 32} {n : Nat} (h : Data s D n) {a m : Nat} (ham : a + m ≤ n) :
    Data s (D + BitVec.ofNat 32 (8 * a)) m where
  wr x hx := by rw [add_ofNat_ofNat]; exact h.wr _ (by omega_using [ham, hx])
  fit := by
    have := h.fit
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have := (D + BitVec.ofNat 32 (8 * a)).isLt; omega_using [h0]
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * a) (by omega_using [this, ham, h0]),
        Nat.mod_eq_of_lt (by omega_using [this, ham, h0])]
      omega_using [this, ham]
  apart := by
    have := h.fit
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; intro x hx; simp only [Region.Contains] at hx; omega_using [hx]
    · rw [addr_add (by omega_using [this, ham, h0])]
      exact h.apart.sub_left (Offset.sub_base _ (by omega_using [ham]))

/-- A word of the data is not in the working space. -/
theorem Data.read_frame {s : State} {D : BitVec 32} {n : Nat} (h : Data s D n) {c : Nat}
    (hc : c ≤ 256) {m m' : Mem} (hf : Frame [headR s c] m m') {x : Nat} (hx : x + 4 ≤ 8 * n) :
    dw m' D x = dw m D x := by
  refine hf.readW (h.contains hx) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact h.apart.sub_right (Region.sub_prefix (by omega_using [hc]))

/-- A word of the working space is not in the data. -/
theorem Data.fw_frame {s s' : State} {D : BitVec 32} {n : Nat} (h : Room s) (hd : Data s D n)
    (hb : s'.gpr .r3 = s.gpr .r3) (hf : Frame [⟨State.addr D, 8 * n⟩] s.mem s'.mem) {k : Nat}
    (hk : k < 256) : fw s' k = fw s k := by
  rw [fw, hb]
  have fit := h.fit
  refine hf.readW (r := frameR s) (contains_off fit (by omega_using [hk]) (by decide)) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact hd.apart.symm

/-- `s` with the word of the data at `D + x` set to `v`. -/
def stD (s : State) (D : BitVec 32) (x : Nat) (v : BitVec 32) : State :=
  { s with mem := s.mem.writeW (State.addr (D + BitVec.ofNat 32 x)) v }

theorem gpr_stD (s : State) (D : BitVec 32) (x : Nat) (v : BitVec 32) (r : Reg) :
    (stD s D x v).gpr r = s.gpr r := rfl

/-- A store to the data. -/
theorem exec_strData {s : State} {D : BitVec 32} {n : Nat} (hd : Data s D n) {t r : Reg} {off x : Nat}
    (hr : s.gpr r + BitVec.ofNat 32 off = D + BitVec.ofNat 32 x) (ho : off < 4096) (hx : x + 4 ≤ 8 * n) :
    exec (.str t r off) s = some (stD s D x (s.gpr t)) := by
  have := exec_str (s := s) (t := t) (n := r) ho (by rw [hr]; exact hd.wr x hx)
  rw [hr] at this; exact this

/-- A load from the data. -/
theorem exec_ldrData {s : State} {D : BitVec 32} {n : Nat} (hd : Data s D n) {t r : Reg} {off x : Nat}
    (hr : s.gpr r + BitVec.ofNat 32 off = D + BitVec.ofNat 32 x) (ho : off < 4096) (hx : x + 4 ≤ 8 * n) :
    exec (.ldr t r off) s = some (s.setReg t (dw s.mem D x)) := by
  have := exec_ldr (s := s) (t := t) (n := r) ho (by rw [hr]; exact hd.rd hx)
  rw [hr] at this; exact this

/-- A store to a word of the working space, through any register. -/
theorem exec_strAt {s : State} (h : Room s) {t r : Reg} {off k : Nat}
    (hr : s.gpr r + BitVec.ofNat 32 off = s.gpr .r3 + BitVec.ofNat 32 (4 * k)) (ho : off < 4096)
    (hk : k < 256) : exec (.str t r off) s = some (stFw s k (s.gpr t)) := by
  have := exec_str (s := s) (t := t) (n := r) ho (by rw [hr]; exact slot_in h (by omega_using [hk]))
  rw [hr] at this; exact this

/-- A load of a word of the working space, through any register. -/
theorem exec_ldrAt {s : State} (h : Room s) {t r : Reg} {off k : Nat}
    (hr : s.gpr r + BitVec.ofNat 32 off = s.gpr .r3 + BitVec.ofNat 32 (4 * k)) (ho : off < 4096)
    (hk : k < 256) : exec (.ldr t r off) s = some (s.setReg t (fw s k)) := by
  have := exec_ldr (s := s) (t := t) (n := r) ho (by rw [hr]; exact slot_rd h (by omega_using [hk]))
  rw [hr] at this; exact this

/-- The word stored to the data. -/
theorem dw_stD_self (s : State) (D : BitVec 32) (x : Nat) (v : BitVec 32) :
    dw (stD s D x v).mem D x = v :=
  Mem.readW_writeW_self32 _ _ _

/-- Another word of the data. -/
theorem dw_stD {s : State} {D : BitVec 32} {n : Nat} (hd : Data s D n) (v : BitVec 32)
    {x y : Nat} (hx : x + 4 ≤ 8 * n) (hy : y + 4 ≤ 8 * n) (hxy : x + 4 ≤ y ∨ y + 4 ≤ x) :
    dw (stD s D x v).mem D y = dw s.mem D y := by
  have fit := hd.fit
  show (s.mem.writeW (State.addr (D + BitVec.ofNat 32 x)) v).readW (State.addr (D + BitVec.ofNat 32 y)) 32 =
    s.mem.readW (State.addr (D + BitVec.ofNat 32 y)) 32
  rw [addr_add (by omega_using [fit, hx]), addr_add (by omega_using [fit, hy])]
  exact Mem.readW_writeW_sep (w := 32) (w' := 32)
    (Offset.sep _ (by omega_using [hxy]) (by omega_using [fit, hy]) (by omega_using [fit, hx])) (by decide)

theorem stD_frame {s : State} {D : BitVec 32} {n : Nat} (hd : Data s D n) {x : Nat} (hx : x + 4 ≤ 8 * n)
    (v : BitVec 32) : Frame [⟨State.addr D, 8 * n⟩] s.mem (stD s D x v).mem :=
  (Frame.refl _ s.mem).writeW (List.mem_singleton_self _) v (hd.contains hx)

/-- A word of the working space after a store to the data. -/
theorem fw_stD {s : State} {D : BitVec 32} {n : Nat} (h : Room s) (hd : Data s D n) {x : Nat}
    (hx : x + 4 ≤ 8 * n) (v : BitVec 32) {k : Nat} (hk : k < 256) : fw (stD s D x v) k = fw s k :=
  hd.fw_frame (s' := stD s D x v) h rfl (stD_frame hd hx v) hk

/-- A word of the data after a store to the working space. -/
theorem dw_stFw {s : State} {D : BitVec 32} {n : Nat} (h : Room s) (hd : Data s D n) {k : Nat}
    (hk : k < 256) (v : BitVec 32) {x : Nat} (hx : x + 4 ≤ 8 * n) :
    dw (stFw s k v).mem D x = dw s.mem D x :=
  hd.read_frame (c := 256) (Nat.le_refl _) (stFw_frame h hk (Nat.le_refl _) v) hx

/-- The batch's blocks: `min(n, 32)`. -/
def kOf (s : State) : Nat := min (s.gpr .r2).toNat 32

/-! ## The batch's count -/

theorem batchCount_ok (s : State) :
    WP isa batchCount s fun s' => s'.gpr .r12 = BitVec.ofNat 32 (kOf s) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  unfold batchCount
  have e₁ := exec_mov (s := s) (d := .r12) (o := .shifted .r2 .lsr 5) (op2_lsr (by decide))
  let s₁ := s.setReg .r12 (s.gpr .r2 >>> 5)
  have e₂ := exec_cmp (s := s₁) (n := .r12) (o := .imm 0) (op2_imm (by decide))
  let s₂ := subFlags s₁ (s₁.gpr .r12) 0
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, by rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some,
    runBlock_nil], ?_⟩
  have z : s₂.z = decide ((s.gpr .r2).toNat < 32) := by
    have e0 : s₁.gpr .r12 - (0 : BitVec 32) = s.gpr .r2 >>> 5 := (BitVec.sub_zero _).trans (RegUpd.gpr_setReg_self _ _ _)
    show (s₁.gpr .r12 - 0 == 0) = _
    rw [e0]
    by_cases h : (s.gpr .r2).toNat < 32
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega_using [h]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
      change _ = 0 at this
      omega_using [h, this]
  refine WP.ite _ (by rw [show isa.eval .eq s₂ = some s₂.z from rfl, z]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt : (s.gpr .r2).toNat < 32 := by simpa using hlt
    have e₃ := exec_mov (s := s₂) (d := .r12) (o := .reg .r2) (op2_reg _ _)
    refine WP.of_runBlock ⟨s₂.setReg .r12 (s₂.gpr .r2), by rw [runBlock_cons, e₃, runStep_some,
      runBlock_nil], ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [RegUpd.gpr_setReg_self, kOf, Nat.min_eq_left (by omega_using [hlt])]
      show s.gpr .r2 = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [RegUpd.gpr_setReg_of_ne _ _ hr]
      show (s.setReg .r12 _).gpr r = _
      rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  · have hge : ¬ (s.gpr .r2).toNat < 32 := by simpa using hge
    have e₃ := exec_mov (s := s₂) (d := .r12) (o := .imm 32) (op2_imm (by decide))
    refine WP.of_runBlock ⟨s₂.setReg .r12 32, by rw [runBlock_cons, e₃, runStep_some, runBlock_nil],
      ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [RegUpd.gpr_setReg_self, kOf, Nat.min_eq_right (by omega_using [hge])]; rfl
    · rw [RegUpd.gpr_setReg_of_ne _ _ hr]
      show (s.setReg .r12 _).gpr r = _
      rw [RegUpd.gpr_setReg_of_ne _ _ hr]

/-! ## Copies -/

theorem count_dec : ∀ m < 33, 1 ≤ m → BitVec.ofNat 32 m - 1 = BitVec.ofNat 32 (m - 1) ∧
    (BitVec.ofNat 32 m - 1 == 0) = decide (m = 1) := by decide

/-- The pointers of a copy. -/
theorem copyStart_ok {s : State} :
    ∃ s', runBlock isa copyStart s = some s' ∧
      s'.gpr .r4 = s.gpr .r3 + BitVec.ofNat 32 (4 * (8 + 0)) ∧
      s'.gpr .r5 = s.gpr .r1 + BitVec.ofNat 32 (8 * 0) ∧ s'.gpr .r6 = s.gpr .r12 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e₁ := exec_dp (s := s) (op := .add) (d := .r4) (n := .r3) (o := .imm (BitVec.ofNat 32 (stOff 0)))
    (op2_imm (by decide))
  let s₁ := s.setReg .r4 (dpVal .add (s.gpr .r3) (BitVec.ofNat 32 (stOff 0)))
  have e₂ := exec_mov (s := s₁) (d := .r5) (o := .reg .r1) (op2_reg _ _)
  let s₂ := s₁.setReg .r5 (s₁.gpr .r1)
  have e₃ := exec_mov (s := s₂) (d := .r6) (o := .reg .r12) (op2_reg _ _)
  refine ⟨s₂.setReg .r6 (s₂.gpr .r12), ?_, ?_, ?_, ?_, fun r h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  · rw [copyStart, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some, runBlock_cons, e₂,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]
  · simp only [s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · simp only [s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, Nat.mul_zero,
      BitVec.add_zero]
  · simp only [s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [s₂, s₁, RegUpd.gpr_setReg, h4, h5, h6, ite_false]

/-- The next block, counted. -/
theorem copyNext_ok {s : State} :
    ∃ s', runBlock isa copyNext s = some s' ∧ s'.gpr .r4 = s.gpr .r4 + 4 ∧ s'.gpr .r5 = s.gpr .r5 + 8 ∧
      s'.gpr .r6 = s.gpr .r6 - 1 ∧ s'.z = (s.gpr .r6 - 1 == 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e₁ := exec_dp (s := s) (op := .add) (d := .r5) (n := .r5) (o := .imm 8) (op2_imm (by decide))
  let s₁ := s.setReg .r5 (dpVal .add (s.gpr .r5) 8)
  have e₂ := exec_dp (s := s₁) (op := .add) (d := .r4) (n := .r4) (o := .imm 4) (op2_imm (by decide))
  let s₂ := s₁.setReg .r4 (dpVal .add (s₁.gpr .r4) 4)
  have e₃ := exec_subs (s := s₂) (d := .r6) (n := .r6) (o := .imm 1) (op2_imm (by decide))
  refine ⟨(subFlags s₂ (s₂.gpr .r6) 1).setReg .r6 (s₂.gpr .r6 - 1), ?_, ?_, ?_, ?_, ?_,
    fun r h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  · rw [copyNext, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · show ((subFlags s₂ _ _).setReg _ _).gpr .r4 = _
    simp only [s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, subFlags, dpVal]
  · show ((subFlags s₂ _ _).setReg _ _).gpr .r5 = _
    simp only [s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, subFlags, dpVal]
  · show ((subFlags s₂ _ _).setReg _ _).gpr .r6 = _
    simp only [s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · show (s₂.gpr .r6 - 1 == 0) = _
    simp only [s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false]
  · show ((subFlags s₂ _ _).setReg _ _).gpr r = _
    simp only [s₂, s₁, RegUpd.gpr_setReg, h4, h5, h6, ite_false, subFlags]

theorem ptr4 (B : BitVec 32) (i : Nat) :
    B + BitVec.ofNat 32 (4 * (8 + i)) + 4 = B + BitVec.ofNat 32 (4 * (8 + (i + 1))) := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_ofNat]; congr 2

theorem ptr5 (D : BitVec 32) (i : Nat) :
    D + BitVec.ofNat 32 (8 * i) + 8 = D + BitVec.ofNat 32 (8 * (i + 1)) := by
  rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_ofNat]; congr 2

theorem ptr4hi (B : BitVec 32) (i : Nat) :
    B + BitVec.ofNat 32 (4 * (8 + i)) + BitVec.ofNat 32 128 = B + BitVec.ofNat 32 (4 * (40 + i)) := by
  rw [add_ofNat_ofNat]; congr 2; omega_using []

/-- The registers a copy leaves alone. -/
abbrev copyKept (r : Reg) : Prop := r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7

/-- The body of the copy in. -/
def copyInBody : List Instr :=
  [.ldr .r7 .r5 0, .str .r7 .r4 0, .ldr .r7 .r5 4, .str .r7 .r4 128] ++ copyNext

/-- After `i` blocks of the copy in from `s`. -/
structure CopyIn (s : State) (D : BitVec 32) (n k i : Nat) (v : State) : Prop where
  r4 : v.gpr .r4 = s.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i))
  r5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)
  r6 : v.gpr .r6 = BitVec.ofNat 32 (k - i)
  keep : ∀ r, copyKept r → v.gpr r = s.gpr r
  got : ∀ b < i, fw v (8 + b) = dw s.mem D (8 * b) ∧ fw v (40 + b) = dw s.mem D (8 * b + 4)
  data : ∀ x, x + 4 ≤ 8 * n → dw v.mem D x = dw s.mem D x
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  frame : Frame [stR s] s.mem v.mem

/-- A block's two words into the state words `8 + i` and `40 + i`. -/
theorem moveIn_ok {v : State} (hv : Room v) {D : BitVec 32} {n : Nat} (hd : Data v D n) {i : Nat}
    (hi : i < 32) (hin : i < n) (h4 : v.gpr .r4 = v.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i)))
    (h5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)) :
    ∃ v', runBlock isa [.ldr .r7 .r5 0, .str .r7 .r4 0, .ldr .r7 .r5 4, .str .r7 .r4 128] v = some v' ∧
      (∀ r, r ≠ .r7 → v'.gpr r = v.gpr r) ∧
      fw v' (8 + i) = dw v.mem D (8 * i) ∧ fw v' (40 + i) = dw v.mem D (8 * i + 4) ∧
      (∀ j < 256, j ≠ 8 + i → j ≠ 40 + i → fw v' j = fw v j) ∧
      (∀ x, x + 4 ≤ 8 * n → dw v'.mem D x = dw v.mem D x) ∧
      v'.rd = v.rd ∧ v'.wr = v.wr ∧ v'.sp = v.sp ∧ Frame [stR v] v.mem v'.mem := by
  have e₁ := exec_ldrData hd (t := .r7) (r := .r5) (off := 0) (x := 8 * i)
    (by rw [h5, BitVec.add_zero]) (by decide) (by omega_using [hin])
  let v₁ := v.setReg .r7 (dw v.mem D (8 * i))
  have k₁ : ∀ r, r ≠ .r7 → v₁.gpr r = v.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have hv₁ : Room v₁ := hv.congr (k₁ _ (by decide)) rfl
  have hd₁ : Data v₁ D n := hd.congr (k₁ _ (by decide)) rfl
  have e₂ := exec_strAt hv₁ (t := .r7) (r := .r4) (off := 0) (k := 8 + i)
    (by rw [k₁ _ (by decide), k₁ _ (by decide), h4, BitVec.add_zero]) (by decide) (by omega_using [hi])
  let v₂ := stFw v₁ (8 + i) (v₁.gpr .r7)
  have k₂ : ∀ r, v₂.gpr r = v₁.gpr r := fun r => gpr_stFw _ _ _ r
  have hv₂ : Room v₂ := hv₁.stFw _ _
  have hd₂ : Data v₂ D n := hd₁.congr (k₂ _) rfl
  have e₃ := exec_ldrData hd₂ (t := .r7) (r := .r5) (off := 4) (x := 8 * i + 4)
    (by rw [k₂, k₁ _ (by decide), h5, add_ofNat_ofNat]) (by decide) (by omega_using [hin])
  let v₃ := v₂.setReg .r7 (dw v₂.mem D (8 * i + 4))
  have k₃ : ∀ r, r ≠ .r7 → v₃.gpr r = v₂.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have hv₃ : Room v₃ := hv₂.congr (k₃ _ (by decide)) rfl
  have e₄ := exec_strAt hv₃ (t := .r7) (r := .r4) (off := 128) (k := 40 + i)
    (by rw [k₃ _ (by decide), k₃ _ (by decide), k₂, k₂, k₁ _ (by decide), k₁ _ (by decide), h4, ptr4hi])
    (by decide) (by omega_using [hi])
  have lo : v₁.gpr .r7 = dw v.mem D (8 * i) := RegUpd.gpr_setReg_self _ _ _
  have d₂ : ∀ x, x + 4 ≤ 8 * n → dw v₂.mem D x = dw v.mem D x := fun x hx =>
    dw_stFw hv₁ hd₁ (by omega_using [hi]) _ hx
  have hi' : v₃.gpr .r7 = dw v.mem D (8 * i + 4) :=
    (RegUpd.gpr_setReg_self _ _ _).trans (d₂ _ (by omega_using [hin]))
  have f₂ : Frame [stR v] v.mem v₂.mem :=
    stFw_frame (s := v₁) hv₁ (n := spills + 64) (by unfold spills; omega_using [hi]) (by decide) _
  have f₄ : Frame [stR v] v₂.mem (stFw v₃ (40 + i) (v₃.gpr .r7)).mem :=
    stFw_frame (s := v₃) hv₃ (n := spills + 64) (by unfold spills; omega_using [hi]) (by decide) _
  refine ⟨stFw v₃ (40 + i) (v₃.gpr .r7), by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil],
    fun r hr => by rw [gpr_stFw, k₃ r hr, k₂, k₁ r hr], ?_, ?_, fun j hj h8 h40 => ?_, fun x hx => ?_,
    rfl, rfl, rfl, f₂.trans f₄⟩
  · rw [fw_stFw hv₃ (by omega_using [hi]) (by omega_using [hi]), ite_eq_right (by omega_using []),
      fw_setReg _ (by decide), fw_stFw hv₁ (by omega_using [hi]) (by omega_using [hi]), ite_eq_left rfl, lo]
  · rw [fw_stFw hv₃ (by omega_using [hi]) (by omega_using [hi]), ite_eq_left rfl, hi']
  · rw [fw_stFw hv₃ (by omega_using [hi]) hj, ite_eq_right h40, fw_setReg _ (by decide),
      fw_stFw hv₁ (by omega_using [hi]) hj, ite_eq_right h8, fw_setReg _ (by decide)]
  · exact (dw_stFw hv₃ (hd₂.congr (k₃ _ (by decide)) rfl) (by omega_using [hi]) _ hx).trans (d₂ x hx)

theorem copyIn_step {s : State} (h : Room s) {D : BitVec 32} {n k : Nat} (hd : Data s D n)
    (hkn : k ≤ n) (hk : k ≤ 32) {i : Nat} (hi : i < k) {v : State} (I : CopyIn s D n k i v) :
    ∃ v', runBlock isa copyInBody v = some v' ∧ CopyIn s D n k (i + 1) v' ∧
      v'.z = decide (i + 1 = k) := by
  have g3 : v.gpr .r3 = s.gpr .r3 := I.keep _ (by decide)
  have hv : Room v := h.congr g3 I.wr
  have hdv : Data v D n := hd.congr g3 I.wr
  obtain ⟨v₁, run₁, k₁, lo₁, hi₁, fw₁, d₁, rd₁, wr₁, sp₁, f₁⟩ := moveIn_ok hv hdv (i := i) (by omega_using [hi, hk])
    (by omega_using [hi, hkn]) (by rw [I.r4, g3]) I.r5
  obtain ⟨v', run', n4, n5, n6, nz, nk, nm, nrd, nwr, nsp⟩ := copyNext_ok (s := v₁)
  have fwv : ∀ j < 256, fw v' j = fw v₁ j := fun j _ => by
    rw [fw, fw, nm, nk _ (by decide) (by decide) (by decide)]
  refine ⟨v', by rw [copyInBody]; exact runBlock_cat_some run₁ run',
    ⟨?_, ?_, ?_, fun r hr => ?_, fun b hb => ?_, fun x hx => ?_, nrd.trans (rd₁.trans I.rd),
      nwr.trans (wr₁.trans I.wr), nsp.trans (sp₁.trans I.sp), ?_⟩, ?_⟩
  · rw [n4, k₁ _ (by decide), I.r4, ptr4]
  · rw [n5, k₁ _ (by decide), I.r5, ptr5]
  · rw [n6, k₁ _ (by decide), I.r6, (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).1]
    congr 1
  · rw [nk r hr.1 hr.2.1 hr.2.2.1, k₁ r hr.2.2.2, I.keep r hr]
  · rw [fwv _ (by omega_using [hb, hi, hk]), fwv _ (by omega_using [hb, hi, hk])]
    by_cases e : b = i
    · subst e
      rw [lo₁, hi₁]
      exact ⟨I.data _ (by omega_using [hi, hkn]), I.data _ (by omega_using [hi, hkn])⟩
    · have hb' : b < i := by omega_using [hb, e]
      rw [fw₁ _ (by omega_using [hb', hi, hk]) (by omega_using [e]) (by omega_using [hb']),
        fw₁ _ (by omega_using [hb', hi, hk]) (by omega_using [hi, hk]) (by omega_using [e])]
      exact I.got b hb'
  · rw [nm, d₁ x hx]; exact I.data x hx
  · rw [nm]; exact I.frame.trans (by rw [← stR_congr g3]; exact f₁)
  · rw [nz, k₁ _ (by decide), I.r6, (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).2]
    exact decide_eq_decide.mpr (by omega_using [hi])

theorem copyIn_ok {s : State} (h : Room s) {D : BitVec 32} {n k : Nat} (hd : Data s D n)
    (hD : s.gpr .r1 = D) (hc : s.gpr .r12 = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hk : k ≤ 32) : WP isa copyIn s (CopyIn s D n k k) := by
  unfold copyIn
  apply WP.seq
  obtain ⟨s₁, run₁, i4, i5, i6, ik, im, ird, iwr, isp⟩ := copyStart_ok (s := s)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have I0 : CopyIn s D n k 0 s₁ :=
    ⟨i4, by rw [i5, hD], by rw [i6, hc]; rfl, fun r hr => ik r hr.1 hr.2.1 hr.2.2.1,
      fun b hb => by omega, fun x _ => by rw [im], ird, iwr, isp, by rw [im]; exact Frame.refl _ _⟩
  refine WP.loop (M := isa) (fun m v => ∃ i, i < k ∧ m = k - i ∧ CopyIn s D n k i v) ?_ k s₁
    ⟨0, hk1, rfl, I0⟩
  intro m v ⟨i, hi, hm, J⟩
  obtain ⟨v', run, J', z⟩ := copyIn_step h hd hkn hk hi J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show isa.eval .ne v' = some !v'.z from rfl, z]
  by_cases e : i + 1 = k
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], k - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, e], rfl, J'⟩

/-- The body of the copy out. -/
def copyOutBody : List Instr :=
  [.ldr .r7 .r4 0, .str .r7 .r5 0, .ldr .r7 .r4 128, .str .r7 .r5 4] ++ copyNext

/-- After `i` blocks of the copy out from `s`. -/
structure CopyOut (s : State) (D : BitVec 32) (k i : Nat) (v : State) : Prop where
  r4 : v.gpr .r4 = s.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i))
  r5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)
  r6 : v.gpr .r6 = BitVec.ofNat 32 (k - i)
  keep : ∀ r, copyKept r → v.gpr r = s.gpr r
  put : ∀ b < i, dw v.mem D (8 * b) = fw s (8 + b) ∧ dw v.mem D (8 * b + 4) = fw s (40 + b)
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  frame : Frame [⟨State.addr D, 8 * k⟩] s.mem v.mem

/-- The state words `8 + i` and `40 + i` into a block's two words. -/
theorem moveOut_ok {v : State} (hv : Room v) {D : BitVec 32} {k : Nat} (hd : Data v D k) {i : Nat}
    (hi : i < 32) (hik : i < k) (h4 : v.gpr .r4 = v.gpr .r3 + BitVec.ofNat 32 (4 * (8 + i)))
    (h5 : v.gpr .r5 = D + BitVec.ofNat 32 (8 * i)) :
    ∃ v', runBlock isa [.ldr .r7 .r4 0, .str .r7 .r5 0, .ldr .r7 .r4 128, .str .r7 .r5 4] v = some v' ∧
      (∀ r, r ≠ .r7 → v'.gpr r = v.gpr r) ∧
      dw v'.mem D (8 * i) = fw v (8 + i) ∧ dw v'.mem D (8 * i + 4) = fw v (40 + i) ∧
      (∀ x, x + 4 ≤ 8 * k → x + 4 ≤ 8 * i ∨ 8 * i + 8 ≤ x → dw v'.mem D x = dw v.mem D x) ∧
      v'.rd = v.rd ∧ v'.wr = v.wr ∧ v'.sp = v.sp ∧ Frame [⟨State.addr D, 8 * k⟩] v.mem v'.mem := by
  have e₁ := exec_ldrAt hv (t := .r7) (r := .r4) (off := 0) (k := 8 + i)
    (by rw [h4, BitVec.add_zero]) (by decide) (by omega_using [hi])
  let v₁ := v.setReg .r7 (fw v (8 + i))
  have k₁ : ∀ r, r ≠ .r7 → v₁.gpr r = v.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have hv₁ : Room v₁ := hv.congr (k₁ _ (by decide)) rfl
  have hd₁ : Data v₁ D k := hd.congr (k₁ _ (by decide)) rfl
  have e₂ := exec_strData hd₁ (t := .r7) (r := .r5) (off := 0) (x := 8 * i)
    (by rw [k₁ _ (by decide), h5, BitVec.add_zero]) (by decide) (by omega_using [hik])
  let v₂ := stD v₁ D (8 * i) (v₁.gpr .r7)
  have k₂ : ∀ r, v₂.gpr r = v₁.gpr r := fun r => gpr_stD _ _ _ _ r
  have hv₂ : Room v₂ := hv₁.congr (k₂ _) rfl
  have hd₂ : Data v₂ D k := hd₁.congr (k₂ _) rfl
  have e₃ := exec_ldrAt hv₂ (t := .r7) (r := .r4) (off := 128) (k := 40 + i)
    (by rw [k₂, k₂, k₁ _ (by decide), k₁ _ (by decide), h4, ptr4hi]) (by decide) (by omega_using [hi])
  let v₃ := v₂.setReg .r7 (fw v₂ (40 + i))
  have k₃ : ∀ r, r ≠ .r7 → v₃.gpr r = v₂.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have hd₃ : Data v₃ D k := hd₂.congr (k₃ _ (by decide)) rfl
  have e₄ := exec_strData hd₃ (t := .r7) (r := .r5) (off := 4) (x := 8 * i + 4)
    (by rw [k₃ _ (by decide), k₂, k₁ _ (by decide), h5, add_ofNat_ofNat]) (by decide)
    (by omega_using [hik])
  have lo : v₁.gpr .r7 = fw v (8 + i) := RegUpd.gpr_setReg_self _ _ _
  have hi' : v₃.gpr .r7 = fw v (40 + i) :=
    (RegUpd.gpr_setReg_self _ _ _).trans
      ((fw_stD hv₁ hd₁ (by omega_using [hik]) _ (by omega_using [hi])).trans (fw_setReg _ (by decide) _ _))
  have f₂ : Frame [⟨State.addr D, 8 * k⟩] v.mem v₂.mem := stD_frame hd₁ (by omega_using [hik]) _
  have f₄ : Frame [⟨State.addr D, 8 * k⟩] v₂.mem (stD v₃ D (8 * i + 4) (v₃.gpr .r7)).mem :=
    stD_frame hd₃ (by omega_using [hik]) _
  have d₂ : dw v₂.mem D (8 * i) = fw v (8 + i) := (dw_stD_self _ _ _ _).trans lo
  refine ⟨stD v₃ D (8 * i + 4) (v₃.gpr .r7), by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil],
    fun r hr => by rw [gpr_stD, k₃ r hr, k₂, k₁ r hr], ?_, ?_, fun x hx hsep => ?_, rfl, rfl, rfl,
    f₂.trans f₄⟩
  · exact (dw_stD hd₃ _ (by omega_using [hik]) (by omega_using [hik]) (by omega_using [])).trans d₂
  · exact (dw_stD_self _ _ _ _).trans hi'
  · exact (dw_stD hd₃ _ (by omega_using [hik]) hx (by omega_using [hsep])).trans
      (dw_stD hd₁ _ (by omega_using [hik]) hx (by omega_using [hsep]))

theorem copyOut_step {s : State} (h : Room s) {D : BitVec 32} {k : Nat} (hd : Data s D k)
    (hk : k ≤ 32) {i : Nat} (hi : i < k) {v : State} (I : CopyOut s D k i v) :
    ∃ v', runBlock isa copyOutBody v = some v' ∧ CopyOut s D k (i + 1) v' ∧
      v'.z = decide (i + 1 = k) := by
  have g3 : v.gpr .r3 = s.gpr .r3 := I.keep _ (by decide)
  have hv : Room v := h.congr g3 I.wr
  have hdv : Data v D k := hd.congr g3 I.wr
  have fwv : ∀ j < 256, fw v j = fw s j := fun j hj => hd.fw_frame h g3 I.frame hj
  obtain ⟨v₁, run₁, k₁, lo₁, hi₁, d₁, rd₁, wr₁, sp₁, f₁⟩ := moveOut_ok hv hdv (i := i)
    (by omega_using [hi, hk]) hi (by rw [I.r4, g3]) I.r5
  obtain ⟨v', run', n4, n5, n6, nz, nk, nm, nrd, nwr, nsp⟩ := copyNext_ok (s := v₁)
  refine ⟨v', by rw [copyOutBody]; exact runBlock_cat_some run₁ run',
    ⟨?_, ?_, ?_, fun r hr => ?_, fun b hb => ?_, nrd.trans (rd₁.trans I.rd),
      nwr.trans (wr₁.trans I.wr), nsp.trans (sp₁.trans I.sp), ?_⟩, ?_⟩
  · rw [n4, k₁ _ (by decide), I.r4, ptr4]
  · rw [n5, k₁ _ (by decide), I.r5, ptr5]
  · rw [n6, k₁ _ (by decide), I.r6, (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).1]
    congr 1
  · rw [nk r hr.1 hr.2.1 hr.2.2.1, k₁ r hr.2.2.2, I.keep r hr]
  · rw [nm]
    by_cases e : b = i
    · subst e
      rw [lo₁, hi₁, fwv _ (by omega_using [hi, hk]), fwv _ (by omega_using [hi, hk])]
      exact ⟨rfl, rfl⟩
    · have hb' : b < i := by omega_using [hb, e]
      rw [d₁ _ (by omega_using [hi, hb']) (by omega_using [hb']),
        d₁ _ (by omega_using [hi, hb']) (by omega_using [hb'])]
      exact I.put b hb'
  · rw [nm]; exact I.frame.trans f₁
  · rw [nz, k₁ _ (by decide), I.r6, (count_dec (k - i) (by omega_using [hk]) (by omega_using [hi])).2]
    exact decide_eq_decide.mpr (by omega_using [hi])

theorem copyOut_ok {s : State} (h : Room s) {D : BitVec 32} {k : Nat} (hd : Data s D k)
    (hD : s.gpr .r1 = D) (hc : s.gpr .r12 = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) (hk : k ≤ 32) :
    WP isa copyOut s (CopyOut s D k k) := by
  unfold copyOut
  apply WP.seq
  obtain ⟨s₁, run₁, i4, i5, i6, ik, im, ird, iwr, isp⟩ := copyStart_ok (s := s)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have I0 : CopyOut s D k 0 s₁ :=
    ⟨i4, by rw [i5, hD], by rw [i6, hc]; rfl, fun r hr => ik r hr.1 hr.2.1 hr.2.2.1,
      fun b hb => by omega, ird, iwr, isp, by rw [im]; exact Frame.refl _ _⟩
  refine WP.loop (M := isa) (fun m v => ∃ i, i < k ∧ m = k - i ∧ CopyOut s D k i v) ?_ k s₁
    ⟨0, hk1, rfl, I0⟩
  intro m v ⟨i, hi, hm, J⟩
  obtain ⟨v', run, J', z⟩ := copyOut_step h hd hk hi J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show isa.eval .ne v' = some !v'.z from rfl, z]
  by_cases e : i + 1 = k
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], k - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, e], rfl, J'⟩

/-! ## Into and out of the lanes -/

open VG.Proof.TripleDes.Bitslice (ipLane_congr tdeaW_lane blockOut_cores blockAt_frame wAt_wAt ecb_blocks)

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

theorem dw_lo (m : Mem) {D : BitVec 32} {b n : Nat} (hf : D.toNat + 8 * n ≤ 2 ^ 32) (hb : b < n) :
    dw m D (8 * b) = m.readW (wAt (State.addr D) b) 32 := by
  rw [dw, addr_add (by omega_using [hf, hb])]

theorem dw_hi (m : Mem) {D : BitVec 32} {b n : Nat} (hf : D.toNat + 8 * n ≤ 2 ^ 32) (hb : b < n) :
    dw m D (8 * b + 4) = m.readW (wAt (State.addr D) b + BitVec.ofNat 64 4) 32 := by
  rw [dw, addr_add (by omega_using [hf, hb]), Offset.add_add]

/-! ## The batch -/

/-- The first blocks. -/
theorem Data.take {s : State} {D : BitVec 32} {n : Nat} (h : Data s D n) {k : Nat} (hk : k ≤ n) :
    Data s D k where
  wr x hx := h.wr x (by omega_using [hk, hx])
  fit := by have := h.fit; omega_using [hk, this]
  apart := h.apart.sub_left (Region.sub_prefix (by omega_using [hk]))

/-- A block of the data is not in the working space. -/
theorem Data.block_apart {s : State} {D : BitVec 32} {n : Nat} (h : Data s D n) {b : Nat} (hb : b < n)
    {c : Nat} (hc : c ≤ 256) : (⟨wAt (State.addr D) b, 8⟩ : Region).Disjoint (headR s c) :=
  (h.apart.sub_left (Offset.sub_base _ (by omega_using [hb]))).sub_right
    (Region.sub_prefix (by omega_using [hc]))

/-- The arguments and the batch's count to the working space. -/
theorem stash_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa stash s = some s' ∧ fw s' 76 = s.gpr .r0 ∧ fw s' 77 = s.gpr .r1 ∧
      fw s' 78 = s.gpr .r2 ∧ fw s' 79 = s.gpr .r12 ∧ (∀ j < 76, fw s' j = fw s j) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [headR s 80] s.mem s'.mem := by
  have e₁ := exec_strFw h (t := .r0) (off := schedOff) 76 rfl (by decide)
  let s₁ := stFw s 76 (s.gpr .r0)
  have h₁ : Room s₁ := h.stFw _ _
  have e₂ := exec_strFw h₁ (t := .r1) (off := dataOff) 77 rfl (by decide)
  let s₂ := stFw s₁ 77 (s₁.gpr .r1)
  have h₂ : Room s₂ := h₁.stFw _ _
  have e₃ := exec_strFw h₂ (t := .r2) (off := nOff) 78 rfl (by decide)
  let s₃ := stFw s₂ 78 (s₂.gpr .r2)
  have h₃ : Room s₃ := h₂.stFw _ _
  have e₄ := exec_strFw h₃ (t := .r12) (off := kOff) 79 rfl (by decide)
  have f : ∀ j < 256, fw (stFw s₃ 79 (s₃.gpr .r12)) j = if j = 79 then s.gpr .r12
      else if j = 78 then s.gpr .r2 else if j = 77 then s.gpr .r1 else if j = 76 then s.gpr .r0
      else fw s j := by
    intro j hj
    rw [fw_stFw h₃ (by decide) hj]
    by_cases e79 : j = 79
    · rw [ite_eq_left e79, ite_eq_left e79]; rfl
    rw [ite_eq_right e79, ite_eq_right e79, fw_stFw h₂ (by decide) hj]
    by_cases e78 : j = 78
    · rw [ite_eq_left e78, ite_eq_left e78]; rfl
    rw [ite_eq_right e78, ite_eq_right e78, fw_stFw h₁ (by decide) hj]
    by_cases e77 : j = 77
    · rw [ite_eq_left e77, ite_eq_left e77]; rfl
    rw [ite_eq_right e77, ite_eq_right e77, fw_stFw h (by decide) hj]
  refine ⟨stFw s₃ 79 (s₃.gpr .r12), ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun _ => rfl, rfl, rfl, ?_⟩
  · rw [stash, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some, runBlock_cons, e₂,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil]
  · rw [f _ (by decide)]; rfl
  · rw [f _ (by decide)]; rfl
  · rw [f _ (by decide)]; rfl
  · rw [f _ (by decide)]; rfl
  · rw [f _ (by omega_using [hj]), ite_eq_right (by omega_using [hj]), ite_eq_right (by omega_using [hj]),
      ite_eq_right (by omega_using [hj]), ite_eq_right (by omega_using [hj])]
  · have f₁ : Frame [headR s 80] s.mem s₁.mem := stFw_frame h (by decide) (by decide) _
    have f₂ : Frame [headR s 80] s₁.mem s₂.mem := stFw_frame h₁ (by decide) (by decide) _
    have f₃ : Frame [headR s 80] s₂.mem s₃.mem := stFw_frame h₂ (by decide) (by decide) _
    have f₄ : Frame [headR s 80] s₃.mem (stFw s₃ 79 (s₃.gpr .r12)).mem :=
      stFw_frame h₃ (by decide) (by decide) _
    exact ((f₁.trans f₂).trans f₃).trans f₄

/-- The arguments and the batch's count back. -/
theorem unstash_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa unstash s = some s' ∧ s'.gpr .r0 = fw s 76 ∧ s'.gpr .r1 = fw s 77 ∧
      s'.gpr .r2 = fw s 78 ∧ s'.gpr .r12 = fw s 79 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := exec_ldrFw h (t := .r0) (off := schedOff) 76 rfl (by decide)
  let s₁ := s.setReg .r0 (fw s 76)
  have h₁ : Room s₁ := h.congr (RegUpd.gpr_setReg_of_ne _ _ (by decide)) (RegUpd.wr_setReg _ _ _)
  have e₂ := exec_ldrFw h₁ (t := .r1) (off := dataOff) 77 rfl (by decide)
  let s₂ := s₁.setReg .r1 (fw s₁ 77)
  have h₂ : Room s₂ := h₁.congr (RegUpd.gpr_setReg_of_ne _ _ (by decide)) (RegUpd.wr_setReg _ _ _)
  have e₃ := exec_ldrFw h₂ (t := .r2) (off := nOff) 78 rfl (by decide)
  let s₃ := s₂.setReg .r2 (fw s₂ 78)
  have h₃ : Room s₃ := h₂.congr (RegUpd.gpr_setReg_of_ne _ _ (by decide)) (RegUpd.wr_setReg _ _ _)
  have e₄ := exec_ldrFw h₃ (t := .r12) (off := kOff) 79 rfl (by decide)
  refine ⟨s₃.setReg .r12 (fw s₃ 79), ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [unstash, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some, runBlock_cons, e₂,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [s₃, s₂, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
    exact fw_setReg _ (by decide) _ _
  · simp only [s₃, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
    exact (fw_setReg _ (by decide) _ _).trans (fw_setReg _ (by decide) _ _)
  · rw [RegUpd.gpr_setReg_self]
    exact (fw_setReg _ (by decide) _ _).trans ((fw_setReg _ (by decide) _ _).trans (fw_setReg _ (by decide) _ _))
  · simp only [s₃, s₂, s₁, RegUpd.gpr_setReg, reduceCtorEq, ite_false]

/-- Past the batch's blocks. -/
theorem advance_ok {s : State} :
    ∃ s', runBlock isa advance s = some s' ∧ s'.gpr .r1 = s.gpr .r1 + s.gpr .r12 <<< 3 ∧
      s'.gpr .r2 = s.gpr .r2 - s.gpr .r12 ∧ s'.z = (s.gpr .r2 - s.gpr .r12 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) := by
  have e₁ := exec_dp (s := s) (op := .add) (d := .r1) (n := .r1) (o := .shifted .r12 .lsl 3)
    (op2_lsl (by decide))
  let s₁ := s.setReg .r1 (dpVal .add (s.gpr .r1) (s.gpr .r12 <<< 3))
  have e₂ := exec_subs (s := s₁) (d := .r2) (n := .r2) (o := .reg .r12) (op2_reg _ _)
  have k₁ : ∀ r, r ≠ .r1 → s₁.gpr r = s.gpr r := fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  have kt : ∀ r, r ≠ .r2 →
      ((subFlags s₁ (s₁.gpr .r2) (s₁.gpr .r12)).setReg .r2 (s₁.gpr .r2 - s₁.gpr .r12)).gpr r = s₁.gpr r :=
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr
  refine ⟨(subFlags s₁ (s₁.gpr .r2) (s₁.gpr .r12)).setReg .r2 (s₁.gpr .r2 - s₁.gpr .r12), ?_, ?_, ?_,
    ?_, ?_, ?_, rfl, rfl, rfl, fun r h1 h2 => (kt r h2).trans (k₁ r h1)⟩
  · rw [advance, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil]
  · exact (kt _ (by decide)).trans (RegUpd.gpr_setReg_self _ _ _)
  · rw [RegUpd.gpr_setReg_self, k₁ _ (by decide), k₁ _ (by decide)]
  · show (s₁.gpr .r2 - s₁.gpr .r12 == 0) = _
    rw [k₁ _ (by decide), k₁ _ (by decide)]
  · exact (kt _ (by decide)).trans (k₁ _ (by decide))
  · exact (kt _ (by decide)).trans (k₁ _ (by decide))

/-- What a batch needs: the working space, the schedule, a block left, and
the data. -/
structure BatchPre (s : State) (Sb D : BitVec 32) (n : Nat) : Prop where
  room : Room s
  sched : Sched s Sb
  data : Data s D n
  r0 : s.gpr .r0 = Sb
  r1 : s.gpr .r1 = D
  r2 : s.gpr .r2 = BitVec.ofNat 32 n
  pos : 1 ≤ n

structure BatchPost (d : Direction) (s : State) (Sb D : BitVec 32) (n k : Nat) (s' : State) : Prop where
  r0 : s'.gpr .r0 = Sb
  r1 : s'.gpr .r1 = D + BitVec.ofNat 32 (8 * k)
  r2 : s'.gpr .r2 = BitVec.ofNat 32 (n - k)
  r3 : s'.gpr .r3 = s.gpr .r3
  z : s'.z = decide (n = k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  out : ∀ b < k, blockAt s'.mem (wAt (State.addr D) b) =
    blockOut (scheduleAt s.mem (State.addr Sb)) d (blockAt s.mem (wAt (State.addr D) b))
  frame : Frame [headR s 80, ⟨State.addr D, 8 * k⟩] s.mem s'.mem

theorem frame_in {rs : List Region} {m m' : Mem} {r : Region} (h : Frame [r] m m') (hr : r ∈ rs) :
    Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem shl3 : ∀ k < 33, BitVec.ofNat 32 k <<< 3 = BitVec.ofNat 32 (8 * k) := by decide

theorem ofNat_sub {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) ∧
      (BitVec.ofNat 32 n - BitVec.ofNat 32 k == 0) = decide (n = k) := by
  have e : BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := n) hn, Nat.mod_eq_of_lt (a := k) (by omega_using [hk, hn]),
      Nat.mod_eq_of_lt (a := n - k) (by omega_using [hn])]
    omega_using [hk, hn]
  refine ⟨e, ?_⟩
  rw [e]
  by_cases h : n = k
  · subst h; simp
  · have : ¬ BitVec.ofNat 32 (n - k) = 0#32 := fun e0 => by
      have := congrArg BitVec.toNat e0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])] at this
      change _ = 0 at this
      omega_using [hk, h, this]
    rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr this

theorem batch_ok (d : Direction) {s : State} {Sb D : BitVec 32} {n : Nat} (h : BatchPre s Sb D n) :
    WP isa (batch d) s (BatchPost d s Sb D n (min n 32)) := by
  have fit := h.data.fit
  have hn : n < 2 ^ 32 := by omega_using [fit]
  generalize hk : min n 32 = k
  have hk1 : 1 ≤ k := by have := h.pos; omega_using [hk, this]
  have hk32 : k ≤ 32 := by omega_using [hk]
  have hkn : k ≤ n := by omega_using [hk]
  have hkOf : kOf s = k := by rw [kOf, h.r2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, hk]
  unfold batch
  -- the batch's count
  apply WP.seq
  refine WP.mono (batchCount_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_
  rw [hkOf] at c₁
  have r3₁ : s₁.gpr .r3 = s.gpr .r3 := g₁ _ (by decide)
  have h₁ : Room s₁ := h.room.congr r3₁ wr₁
  have d₁ : Data s₁ D n := h.data.congr r3₁ wr₁
  -- the copy in
  apply WP.seq
  refine WP.mono (copyIn_ok h₁ d₁ ((g₁ _ (by decide)).trans h.r1) c₁ hk1 hkn hk32) fun s₂ I₂ => ?_
  have k₂ : ∀ r, copyKept r → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr h12 =>
    (I₂.keep r hr).trans (g₁ r h12)
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := (I₂.keep _ (by decide)).trans r3₁
  have wr₂ : s₂.wr = s.wr := I₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := I₂.rd.trans rd₁
  have h₂ : Room s₂ := h.room.congr r3₂ wr₂
  have F₂ : Frame [headR s 80] s.mem s₂.mem := by
    have := I₂.frame
    rw [m₁, stR_congr r3₁] at this
    exact headR_mono (by decide) this
  -- the arguments stashed
  apply WP.seq
  obtain ⟨s₃, run₃, a0, a1, a2, a12, o₃, g₃, rd₃, wr₃, f₃⟩ := stash_ok h₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := (g₃ _).trans r3₂
  have wr₃' : s₃.wr = s.wr := wr₃.trans wr₂
  have rd₃' : s₃.rd = s.rd := rd₃.trans rd₂
  have h₃ : Room s₃ := h.room.congr r3₃ wr₃'
  have F₃ : Frame [headR s 80] s.mem s₃.mem := F₂.trans (by rw [← headR_congr r3₂]; exact f₃)
  -- the transposition
  apply WP.seq
  obtain ⟨s₄, run₄, w₄, r3₄, rd₄, wr₄, _, f₄⟩ := transpose_ok h₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have r3₄' : s₄.gpr .r3 = s.gpr .r3 := r3₄.trans r3₃
  have wr₄' : s₄.wr = s.wr := wr₄.trans wr₃'
  have rd₄' : s₄.rd = s.rd := rd₄.trans rd₃'
  have h₄ : Room s₄ := h.room.congr r3₄' wr₄'
  have G₄ : Frame [headR s₃ 76] s₃.mem s₄.mem := headR_mono (by decide) f₄
  have F₄ : Frame [headR s 80] s.mem s₄.mem :=
    F₃.trans (by rw [← headR_congr r3₃]; exact headR_mono (by decide) f₄)
  have S₄ : fw s₄ 76 = Sb := by
    rw [fw_of_frame h₃ r3₄ G₄ (by decide) (by decide), a0, k₂ _ (by decide) (by decide), h.r0]
  -- the passes
  apply WP.seq
  refine WP.mono (passes_ok d h₄ (h.sched.congr r3₄' rd₄') S₄) fun s₅ ⟨w₅, r3₅, rd₅, wr₅, _, f₅⟩ => ?_
  have r3₅' : s₅.gpr .r3 = s.gpr .r3 := r3₅.trans r3₄'
  have wr₅' : s₅.wr = s.wr := wr₅.trans wr₄'
  have rd₅' : s₅.rd = s.rd := rd₅.trans rd₄'
  have h₅ : Room s₅ := h.room.congr r3₅' wr₅'
  have G₅ : Frame [headR s₃ 76] s₃.mem s₅.mem := G₄.trans (by rw [← headR_congr r3₄]; exact f₅)
  rw [scheduleAt_frame h.sched (by decide) F₄] at w₅
  -- the transposition back
  apply WP.seq
  obtain ⟨s₆, run₆, w₆, r3₆, rd₆, wr₆, _, f₆⟩ := transpose_ok h₅
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have r3₆' : s₆.gpr .r3 = s.gpr .r3 := r3₆.trans r3₅'
  have wr₆' : s₆.wr = s.wr := wr₆.trans wr₅'
  have rd₆' : s₆.rd = s.rd := rd₆.trans rd₅'
  have h₆ : Room s₆ := h.room.congr r3₆' wr₆'
  have G₆ : Frame [headR s₃ 76] s₃.mem s₆.mem :=
    G₅.trans (by rw [← headR_congr (r3₅.trans r3₄)]; exact headR_mono (by decide) f₆)
  have F₆ : Frame [headR s 80] s.mem s₆.mem :=
    F₃.trans (by rw [← headR_congr r3₃]; exact headR_mono (by decide) G₆)
  have st : ∀ j, 76 ≤ j → j < 256 → fw s₆ j = fw s₃ j := fun j h76 hj =>
    fw_of_frame h₃ (r3₆.trans (r3₅.trans r3₄)) G₆ h76 hj
  -- the arguments back
  apply WP.seq
  obtain ⟨s₇, run₇, b0, b1, b2, b12, r3₇, m₇, rd₇, wr₇⟩ := unstash_ok h₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have r3₇' : s₇.gpr .r3 = s.gpr .r3 := r3₇.trans r3₆'
  have wr₇' : s₇.wr = s.wr := wr₇.trans wr₆'
  have h₇ : Room s₇ := h.room.congr r3₇' wr₇'
  have d₇ : Data s₇ D k := (h.data.take hkn).congr r3₇' wr₇'
  have c0 : s₇.gpr .r0 = Sb := by rw [b0, st _ (by decide) (by decide), a0, k₂ _ (by decide) (by decide), h.r0]
  have c1 : s₇.gpr .r1 = D := by rw [b1, st _ (by decide) (by decide), a1, k₂ _ (by decide) (by decide), h.r1]
  have c2 : s₇.gpr .r2 = BitVec.ofNat 32 n := by
    rw [b2, st _ (by decide) (by decide), a2, k₂ _ (by decide) (by decide), h.r2]
  have c12 : s₇.gpr .r12 = BitVec.ofNat 32 k := by
    rw [b12, st _ (by decide) (by decide), a12, I₂.keep _ (by decide), c₁]
  -- the copy out
  apply WP.seq
  refine WP.mono (copyOut_ok h₇ d₇ c1 c12 hk1 hk32) fun s₈ I₈ => ?_
  -- past the batch
  obtain ⟨s₉, run₉, n1, n2, nz, n0, n3, m₉, rd₉, wr₉, _⟩ := advance_ok (s := s₈)
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  have e12 : s₈.gpr .r12 = BitVec.ofNat 32 k := (I₈.keep _ (by decide)).trans c12
  have e2 : s₈.gpr .r2 = BitVec.ofNat 32 n := (I₈.keep _ (by decide)).trans c2
  obtain ⟨sub, subz⟩ := ofNat_sub hkn hn
  refine ⟨by rw [n0, I₈.keep _ (by decide), c0], ?_, by rw [n2, e2, e12, sub], ?_,
    by rw [nz, e2, e12, subz], ?_, ?_, fun b hb => ?_, ?_⟩
  · rw [n1, I₈.keep _ (by decide), c1, e12, shl3 k (by omega_using [hk32])]
  · rw [n3, I₈.keep _ (by decide), r3₇']
  · rw [rd₉, I₈.rd, rd₇, rd₆']
  · rw [wr₉, I₈.wr, wr₇']
  · have hb32 : b < 32 := by omega_using [hb, hk32]
    have hbn : b < n := by omega_using [hb, hkn]
    have w₃ : ∀ x < 64, words s₃ x = words s₂ x := fun x hx =>
      o₃ _ (by unfold spills; omega_using [hx])
    have dS : ∀ x, x + 4 ≤ 8 * n → dw s₁.mem D x = dw s.mem D x := fun x _ => by rw [m₁]
    obtain ⟨g1, g2⟩ := I₂.got b hb
    obtain ⟨p1, p2⟩ := I₈.put b hb
    have fw₇ : ∀ j < 256, fw s₇ j = fw s₆ j := fun j _ => by rw [fw, fw, m₇, r3₇]
    rw [m₉]
    refine batch_block _ d s.mem s₈.mem _ (words s₃) (words s₄) (words s₅) (words s₆) hb32 ?_ ?_ w₄ w₅ w₆
      ?_ ?_
    · rw [w₃ b (by omega_using [hb32]), ← dw_lo s.mem fit hbn, ← dS _ (by omega_using [hbn])]
      exact g1
    · rw [w₃ _ (by omega_using [hb32]), ← dw_hi s.mem fit hbn, ← dS _ (by omega_using [hbn]), ← g2, words,
        show spills + (32 + b) = 40 + b by unfold spills; omega_using []]
    · rw [← dw_lo s₈.mem fit hbn, p1, fw₇ _ (by omega_using [hb32])]; rfl
    · rw [← dw_hi s₈.mem fit hbn, p2, fw₇ _ (by omega_using [hb32]), words,
        show spills + (32 + b) = 40 + b by unfold spills; omega_using []]
  · rw [m₉]
    have f₈ : Frame [⟨State.addr D, 8 * k⟩] s₆.mem s₈.mem := by rw [← m₇]; exact I₈.frame
    exact (frame_in F₆ List.mem_cons_self).trans
      (frame_in f₈ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ## The batches -/

/-- After `done` blocks of the `N` from `s₀`. -/
structure LoopInv (d : Direction) (s₀ : State) (Sb D : BitVec 32) (N done : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = Sb
  r1 : s.gpr .r1 = D + BitVec.ofNat 32 (8 * done)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (N - done)
  r3 : s.gpr .r3 = s₀.gpr .r3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  out : ∀ b < done, blockAt s.mem (wAt (State.addr D) b) =
    blockOut (scheduleAt s₀.mem (State.addr Sb)) d (blockAt s₀.mem (wAt (State.addr D) b))
  rest : ∀ b, done ≤ b → b < N →
    blockAt s.mem (wAt (State.addr D) b) = blockAt s₀.mem (wAt (State.addr D) b)
  frame : Frame [headR s₀ 80, ⟨State.addr D, 8 * N⟩] s₀.mem s.mem

theorem loop_step (d : Direction) {s₀ : State} (h₀ : Room s₀) {Sb D : BitVec 32} {N : Nat}
    (hs₀ : Sched s₀ Sb) (hd₀ : Data s₀ D N)
    (kd : (⟨State.addr Sb, 384⟩ : Region).Disjoint ⟨State.addr D, 8 * N⟩) {done : Nat} (hdone : done < N)
    {s : State} (I : LoopInv d s₀ Sb D N done s) :
    WP isa (batch d) s fun s' => LoopInv d s₀ Sb D N (done + min (N - done) 32) s' ∧
      s'.z = decide (N - done = min (N - done) 32) := by
  have fit := hd₀.fit
  have hroom : Room s := h₀.congr I.r3 I.wr
  have hsub : Data s (D + BitVec.ofNat 32 (8 * done)) (N - done) :=
    (hd₀.sub (a := done) (m := N - done) (by omega_using [hdone])).congr I.r3 I.wr
  have aD : State.addr (D + BitVec.ofNat 32 (8 * done)) = wAt (State.addr D) done :=
    addr_add (by omega_using [fit, hdone])
  refine WP.mono (batch_ok d ⟨hroom, hs₀.congr I.r3 I.rd, hsub, I.r0, I.r1, I.r2, by omega_using [hdone]⟩)
    fun s' P => ⟨⟨P.r0, ?_, ?_, P.r3.trans I.r3, P.rd.trans I.rd, P.wr.trans I.wr, fun b hb => ?_,
      fun b hb hbN => ?_, ?_⟩, P.z⟩
  · rw [P.r1, add_ofNat_ofNat]; congr 2; omega_using []
  · rw [P.r2]; congr 1; omega_using []
  · by_cases hlt : b < done
    · rw [← I.out b hlt]
      refine blockAt_frame P.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [headR_congr I.r3]; exact hd₀.block_apart (by omega_using [hlt, hdone]) (by decide)
      · rw [aD]
        exact Offset.disjoint _ (by omega_using [hlt]) (by omega_using [fit, hlt, hdone])
          (by omega_using [fit, hdone])
    · have hb' : b - done < min (N - done) 32 := by omega_using [hb, hlt]
      have e := P.out (b - done) hb'
      rw [aD, wAt_wAt, show done + (b - done) = b by omega_using [hlt]] at e
      have eK : scheduleAt s.mem (State.addr Sb) = scheduleAt s₀.mem (State.addr Sb) :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame _ I.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hs₀.apart.sub_right (Region.sub_prefix (by decide))
          · exact kd
      rw [e, I.rest b (by omega_using [hlt]) (by omega_using [hb, hdone]), eK]
  · rw [← I.rest b (by omega_using [hb]) hbN]
    refine blockAt_frame P.frame fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [headR_congr I.r3]; exact hd₀.block_apart hbN (by decide)
    · rw [aD]
      exact Offset.disjoint _ (by omega_using [hb]) (by omega_using [fit, hbN])
        (by omega_using [fit, hdone])
  · refine I.frame.trans (P.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [headR_congr I.r3]; exact fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [aD]
      exact Offset.sub_base _ (by omega_using [hdone])

theorem loop_ok (d : Direction) {s₀ : State} (h₀ : Room s₀) {Sb D : BitVec 32} {N : Nat}
    (hs₀ : Sched s₀ Sb) (hd₀ : Data s₀ D N)
    (kd : (⟨State.addr Sb, 384⟩ : Region).Disjoint ⟨State.addr D, 8 * N⟩) (hN : 1 ≤ N)
    (r0 : s₀.gpr .r0 = Sb) (r1 : s₀.gpr .r1 = D) (r2 : s₀.gpr .r2 = BitVec.ofNat 32 N) :
    WP isa (.loop (batch d) .ne) s₀ (LoopInv d s₀ Sb D N N) := by
  have I0 : LoopInv d s₀ Sb D N 0 s₀ :=
    ⟨r0, by rw [r1, Nat.mul_zero, BitVec.add_zero], r2, rfl, rfl, rfl, fun b hb => by omega,
      fun _ _ _ => rfl, Frame.refl _ _⟩
  refine WP.loop (M := isa) (fun m v => ∃ done, done < N ∧ m = N - done ∧ LoopInv d s₀ Sb D N done v)
    ?_ N s₀ ⟨0, hN, rfl, I0⟩
  intro m v ⟨done, hdone, hm, J⟩
  refine WP.mono (loop_step d h₀ hs₀ hd₀ kd hdone J) fun v' ⟨J', z⟩ => ?_
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

/-- The ECB functions' precondition, with the working space at `r3`. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 384⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 1024⟩]
  kd : (⟨State.addr (s.gpr .r0), 384⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
  kb : (⟨State.addr (s.gpr .r0), 384⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 1024⟩
  db : (⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 1024⟩
  fitD : (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32
  fitK : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  fitB : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32

theorem saved_slots : Spill.Slots 320 356 saved := by decide

theorem saved_restorable : Spill.Restorable .r3 saved := by decide

theorem saved_regs : ∀ r ∈ preserved, r ∈ saved.map Prod.fst := by decide

theorem ecb_wp (d : Direction) {s : State} (hp : EcbPre s) :
    WP isa (Impl.TripleDes.Arm.Bitslice.ecb d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      ∀ b < (s.gpr .r2).toNat, blockAt s'.mem (wAt (State.addr (s.gpr .r1)) b) =
        blockOut (scheduleAt s.mem (State.addr (s.gpr .r0))) d
          (blockAt s.mem (wAt (State.addr (s.gpr .r1)) b)) := by
  generalize hN : (s.gpr .r2).toNat = N
  have r2 : s.gpr .r2 = BitVec.ofNat 32 N := by rw [← hN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨rd, wr, kd, kb, db, fitD, fitK, fitB⟩ := hp
  rw [hN] at wr kd db fitD
  have hroom : Room s := ⟨by rw [wr]; simp [frameR], fitB⟩
  have hsched : Sched s (s.gpr .r0) := ⟨by rw [rd]; simp, fitK, kb⟩
  have hdata : Data s (s.gpr .r1) N :=
    ⟨fun x hx => in_off (by rw [wr]; simp) fitD hx (by decide), fitD, db⟩
  unfold Impl.TripleDes.Arm.Bitslice.ecb
  apply WP.seq
  have e₁ := exec_cmp (s := s) (n := .r2) (o := .imm 0) (op2_imm (by decide))
  let s₁ := subFlags s (s.gpr .r2) 0
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, e₁, runStep_some, runBlock_nil], ?_⟩
  have z : s₁.z = decide (N = 0) := by
    have e0 : s.gpr .r2 - (0 : BitVec 32) = s.gpr .r2 := BitVec.sub_zero _
    show (s.gpr .r2 - 0 == 0) = _
    rw [e0, r2]
    have hlt : N < 2 ^ 32 := by rw [← hN]; exact (s.gpr .r2).isLt
    by_cases h0 : N = 0
    · subst h0; rfl
    · have : ¬ BitVec.ofNat 32 N = 0#32 := fun e0 => by
        have := congrArg BitVec.toNat e0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        exact h0 this
      rw [decide_eq_false h0]
      exact beq_eq_false_iff_ne.mpr this
  refine WP.ite _ (by rw [show isa.eval .eq s₁ = some s₁.z from rfl, z]) (fun h0 => ?_) (fun h1 => ?_)
  · have h0 : N = 0 := by simpa using h0
    exact WP.block_nil ⟨fun _ _ => rfl, fun b hb => by omega_using [hb, h0]⟩
  · have h1 : 1 ≤ N := by
      have : ¬ N = 0 := by simpa using h1
      omega_using [this]
    have hroom₁ : Room s₁ := hroom.congr rfl rfl
    -- the registers saved
    apply WP.seq
    have hin : ∀ o, 320 ≤ o → o + 4 ≤ 356 →
        InRegions s₁.wr (State.addr (s₁.gpr .r3) + BitVec.ofNat 64 o) 4 := fun o _ ho =>
      ⟨_, hroom.frame, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
    refine WP.mono (Spill.save_block_ok (b := .r3) saved_slots (s := s₁) (by show (s.gpr .r3).toNat + 356 ≤ 2 ^ 32; omega_using [fitB]) hin)
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    have g₂' : ∀ r, s₂.gpr r = s.gpr r := fun r => by rw [g₂]; rfl
    have hroom₂ : Room s₂ := hroom.congr (g₂' _) wr₂
    have F₂ : Frame [frameR s] s.mem s₂.mem := by
      rw [m₂]; exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
    have sv₂ : Spill.Saved s₂.mem (State.addr (s.gpr .r3)) s.gpr saved := by
      rw [m₂]; exact Spill.saveMem_saved _ _ _ _ saved_slots
    -- the batches
    apply WP.seq
    refine WP.mono (loop_ok d hroom₂ (hsched.congr (g₂' _) rd₂) (hdata.congr (g₂' _) wr₂) kd h1 (g₂' _)
      (g₂' _) ((g₂' _).trans r2)) fun s₃ L => ?_
    have r3₃ : s₃.gpr .r3 = s.gpr .r3 := L.r3.trans (g₂' _)
    have sv₃ : Spill.Saved s₃.mem (State.addr (s₃.gpr .r3)) s.gpr saved := by
      rw [r3₃]
      refine sv₂.frame saved_slots L.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [headR_congr (g₂' _)]
        exact Offset.disjoint_base _ (by decide) (by decide)
      · exact (db.sub_right (Offset.sub_base _ (by decide))).symm
    -- the registers back
    have hin₃ : ∀ o, 320 ≤ o → o + 4 ≤ 356 →
        InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.gpr .r3) + BitVec.ofNat 64 o) 4 := fun o _ ho => by
      rw [r3₃, L.wr, wr₂]
      exact ⟨_, List.mem_append_right _ hroom.frame,
        Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
    refine WP.mono (Spill.restore_block_ok saved_slots saved_restorable
      (by rw [r3₃]; omega_using [fitB]) hin₃ sv₃) fun s₄ ⟨g₄, _, m₄, _⟩ =>
      ⟨Spill.restored_of g₄ saved_regs, fun b hb => ?_⟩
    rw [m₄, L.out b hb]
    have eb : blockAt s₂.mem (wAt (State.addr (s.gpr .r1)) b) =
        blockAt s.mem (wAt (State.addr (s.gpr .r1)) b) :=
      blockAt_frame F₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact db.sub_left (Offset.sub_base _ (by omega_using [hb]))
    have ek : scheduleAt s₂.mem (State.addr (s.gpr .r0)) = scheduleAt s.mem (State.addr (s.gpr .r0)) :=
      VG.Proof.TripleDes.scheduleAt_eq_of_frame _ F₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact kb
    rw [eb, ek]

end VG.Proof.TripleDes.Arm.Bitsliced
