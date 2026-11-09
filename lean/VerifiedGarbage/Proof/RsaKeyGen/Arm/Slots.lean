module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.PairMem

/-! # Words of 32 bits at a base, and `u64`s of two of them (ARMv7)

The RSA prime search keeps its state in 32-bit words, `slot m B j` at
`B + 4 j`; the caller's `u64` words are pairs of them, the low half first
(`pair_word`). Stores of words are a fold (`writeSlots`), whose words are
read back by `slot_writeSlots`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm

open VG VG.Proof.Mont

/-- The 32-bit word `j` at `B`. -/
def slot (m : Mem) (B : Addr) (j : Nat) : BitVec 32 := m.readW (off B (4 * j)) 32

/-- Stores of 32-bit words, in order. -/
def writeSlots (m : Mem) (B : Addr) (values : List (Nat × BitVec 32)) : Mem :=
  values.foldl (fun m e => m.writeW (off B (4 * e.1)) e.2) m

/-- Word `j` after stores of `values` over `initial`. -/
def slotValue (values : List (Nat × BitVec 32)) (j : Nat) (initial : BitVec 32) : BitVec 32 :=
  values.foldl (fun value e => if j = e.1 then e.2 else value) initial

theorem writeSlots_cons (m : Mem) (B : Addr) (e : Nat × BitVec 32) (values : List (Nat × BitVec 32)) :
    writeSlots m B (e :: values) = writeSlots (m.writeW (off B (4 * e.1)) e.2) B values := rfl

theorem writeSlots_append (m : Mem) (B : Addr) (xs ys : List (Nat × BitVec 32)) :
    writeSlots m B (xs ++ ys) = writeSlots (writeSlots m B xs) B ys := List.foldl_append

theorem slot_store (m : Mem) (B : Addr) (v : BitVec 32) {N i j : Nat} (hN : 4 * N ≤ 2 ^ 64)
    (hi : i < N) (hj : j < N) :
    slot (m.writeW (off B (4 * i)) v) B j = if j = i then v else slot m B j := by
  by_cases same : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right same]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem slot_writeSlots (m : Mem) (B : Addr) {N : Nat} (hN : 4 * N ≤ 2 ^ 64)
    (values : List (Nat × BitVec 32)) (bounds : ∀ e ∈ values, e.1 < N) (j : Nat) (hj : j < N) :
    slot (writeSlots m B values) B j = slotValue values j (slot m B j) := by
  induction values generalizing m with
  | nil => rfl
  | cons e tail ih =>
    rw [writeSlots_cons, ih _ (fun v hv => bounds v (List.mem_cons_of_mem _ hv)),
      slot_store _ _ _ hN (bounds e (List.mem_cons_self ..)) hj]
    rfl

theorem writeSlots_frame (m : Mem) (B : Addr) {N : Nat} (hN : 4 * N < 2 ^ 64)
    (values : List (Nat × BitVec 32)) (bounds : ∀ e ∈ values, e.1 < N) :
    Frame [⟨B, 4 * N⟩] m (writeSlots m B values) := by
  induction values generalizing m with
  | nil => exact Frame.refl _ _
  | cons e tail ih =>
    have he := bounds e (List.mem_cons_self ..)
    have first : Frame [⟨B, 4 * N⟩] m (m.writeW (off B (4 * e.1)) e.2) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    exact first.trans (ih _ (fun v hv => bounds v (List.mem_cons_of_mem _ hv)))

/-- A read apart from every store. -/
theorem readW_writeSlots_sep (m : Mem) (B a : Addr) (values : List (Nat × BitVec 32))
    (h : ∀ e ∈ values, Mem.Sep a (32 / 8) (off B (4 * e.1)) (32 / 8)) :
    (writeSlots m B values).readW a 32 = m.readW a 32 := by
  induction values generalizing m with
  | nil => rfl
  | cons e tail ih =>
    rw [writeSlots_cons, ih _ (fun v hv => h v (List.mem_cons_of_mem _ hv))]
    exact Mem.readW_writeW_sep (h e (List.mem_cons_self ..)) (by decide)

/-- A `u64` word is its two halves, the low one first. -/
theorem pair_word (m : Mem) (B : Addr) (j : Nat) :
    m.readW (off B (8 * j)) 64 = slot m B (2 * j + 1) ++ slot m B (2 * j) := by
  rw [VG.Proof.Rc2.Word32.read64_pair]
  have a1 : off B (8 * j) + BitVec.ofNat 64 4 = off B (4 * (2 * j + 1)) := by
    rw [off, off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have a0 : off B (8 * j) = off B (4 * (2 * j)) := by rw [off, off]; congr 2; omega
  rw [a1, a0]; rfl

theorem pair_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (0#32 ++ BitVec.ofNat 32 n : BitVec 64) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.toNat_ofNat, Nat.zero_shiftLeft, Nat.zero_or]
  omega

/-- The caller's four `u64`s, from their halves. -/
theorem wordsAt_slots (m : Mem) (B : Addr) {a b c d : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hc : c < 2 ^ 32) (hd : d < 2 ^ 32)
    (h0 : slot m B 0 = BitVec.ofNat 32 a) (h1 : slot m B 1 = 0)
    (h2 : slot m B 2 = BitVec.ofNat 32 b) (h3 : slot m B 3 = 0)
    (h4 : slot m B 4 = BitVec.ofNat 32 c) (h5 : slot m B 5 = 0)
    (h6 : slot m B 6 = BitVec.ofNat 32 d) (h7 : slot m B 7 = 0) :
    Spec.Rsa.wordsAt m B 4 = [BitVec.ofNat 64 a, BitVec.ofNat 64 b, BitVec.ofNat 64 c,
      BitVec.ofNat 64 d] := by
  have w (j : Nat) : m.readW (B + BitVec.ofNat 64 (8 * j)) 64 = slot m B (2 * j + 1) ++ slot m B (2 * j) :=
    pair_word m B j
  simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, w]
  simp only [Nat.reduceMul, Nat.reduceAdd, h0, h1, h2, h3, h4, h5, h6, h7]
  rw [← pair_ofNat ha, ← pair_ofNat hb, ← pair_ofNat hc, ← pair_ofNat hd]; rfl

end VG.Proof.RsaKeyGen.Arm
