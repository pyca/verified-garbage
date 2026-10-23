module

public import VerifiedGarbage.Impl.Rc4.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # RC4 on PPC64LE: the table lookup, a doubleword at a time -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Proof.Rc4

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_eight (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- Steps a block of the RC4 code, keeping loads of a doubleword as
`Mem.readW` and of a byte as the byte. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, ↓read_one, ↓read_eight, write_eight, false_implies,
        $ls,*])

/-! ## Masks -/

/-- The mask `isZero` leaves. -/
theorem zero_mask (v : BitVec 64) (hv : v.toNat < 2 ^ 63) :
    0#64 - (v - 1#64) >>> 63 = if v = 0#64 then BitVec.allOnes 64 else 0#64 := by
  by_cases h : v = 0#64
  · subst h; decide
  · have hz : (v - 1#64) >>> 63 = 0#64 := by
      have h0 : v.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    rw [hz, ite_eq_right h]; decide

theorem allOnes_and_ite (p : Prop) [Decidable p] (y : BitVec 64) :
    (if p then BitVec.allOnes 64 else 0#64) &&& y = if p then y else 0#64 := by
  split
  · exact BitVec.allOnes_and
  · exact BitVec.zero_and

theorem and_allOnes_ite (p : Prop) [Decidable p] (y : BitVec 64) :
    y &&& (if p then BitVec.allOnes 64 else 0#64) = if p then y else 0#64 := by
  split
  · exact BitVec.and_allOnes
  · exact BitVec.and_zero

/-- The value `rowMask` tests: zero iff byte `idx` is in doubleword `k`. -/
theorem row_zero (idx : Byte) {k : Nat} (hk : k < 32) :
    (BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64) >>> 3 = 0#64 ↔ idx.toNat / 8 = k := by
  rw [← toNat_lt_eight, BitVec.xor_comm]
  exact row_hit idx hk

theorem row_lt (idx : Byte) (k : Nat) :
    ((BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64) >>> 3).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64).isLt
  omega

/-- The mask `rowMask` leaves. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 32) :
    0#64 - ((BitVec.ofNat 64 (8 * k) ^^^ idx.setWidth 64) >>> 3 - 1#64) >>> 63 =
      if idx.toNat / 8 = k then BitVec.allOnes 64 else 0#64 := by
  rw [zero_mask _ (row_lt idx k)]
  by_cases h : idx.toNat / 8 = k
  · rw [ite_eq_left ((row_zero idx hk).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((row_zero idx hk).mp h')), ite_eq_right h]

theorem low3 (x : BitVec 64) : (x <<< 61) >>> 61 = x &&& BitVec.ofNat 64 7 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (7 % 2 ^ 64 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The value `laneMask` tests. -/
theorem lane_val (idx : Byte) {j : Nat} (hj : j < 8) :
    ((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61) >>> 61 =
      (idx.setWidth 64 &&& BitVec.ofNat 64 7) ^^^ BitVec.ofNat 64 j := by
  rw [low3]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_xor, BitVec.toNat_and,
    Nat.and_xor_distrib_right, Nat.xor_comm]
  congr 1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (7 % 2 ^ 64 : Nat) = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The mask `laneMask` leaves. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 8) :
    0#64 - (((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61) >>> 61 - 1#64) >>> 63 =
      if idx.toNat % 8 = j then BitVec.allOnes 64 else 0#64 := by
  have hz : ∀ x : BitVec 64, x = 0#64 ↔ x.toNat < 1 := by
    intro x; rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]; omega
  have hl : (((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61) >>> 61).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := ((BitVec.ofNat 64 j ^^^ idx.setWidth 64) <<< 61).isLt
    omega
  rw [zero_mask _ hl, lane_val idx hj]
  by_cases h : idx.toNat % 8 = j
  · rw [ite_eq_left ((hz _).mpr ((lane_hit idx hj).mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((lane_hit idx hj).mp ((hz _).mp h'))), ite_eq_right h]

/-! ## Visiting the doublewords -/

/-- The doubleword holding byte `n`, once doublewords `0, …, k - 1` are visited. -/
def gather (m : Mem) (p : Addr) (n k : Nat) : BitVec 64 :=
  if n / 8 < k then m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 else 0

theorem gather_succ (m : Mem) (p : Addr) (n k : Nat) :
    gather m p n k ||| (if n / 8 = k then m.readW (p + BitVec.ofNat 64 (8 * k)) 64 else 0) =
      gather m p n (k + 1) := by
  unfold gather
  by_cases h0 : n / 8 < k
  · simp [h0, show ¬ n / 8 = k by omega, show n / 8 < k + 1 by omega]
  · by_cases h1 : n / 8 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 8 < k + 1 by omega]

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h9 : s.gpr .r9 = idx.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .r11 = s.gpr .r11 |||
        (if idx.toNat / 8 = k then s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * k)) 64 else 0) ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r3 = s.gpr .r3 ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  unfold gatherStep rowMask isZero
  rrun [h9, h8, hr, show 8 * k < 2 ^ 15 by omega, show (8 * k) % 4 = 0 by omega]
  rw [row_mask idx hk, and_allOnes_ite]

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .r11 = gather s₀.mem (s₀.gpr .r3) idx.toNat k ∧ t.gpr .r9 = s₀.gpr .r9 ∧
    t.gpr .r8 = s₀.gpr .r8 ∧ t.gpr .r3 = s₀.gpr .r3 ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧
    t.wr = s₀.wr

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem gather_steps (s₀ : State) (idx : Byte) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (h8 : s₀.gpr .r8 = 0) (hr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r3) 256) :
    ∀ n ≤ 32, ∀ s, GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h11, h9', h8', hp, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (t.gpr .r3 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hrd, hwr, hp]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (gather_step t idx (by omega) (h9'.trans h9) (h8'.trans h8) hq) fun u hu => ?_
    obtain ⟨u11, u9, u8, up, um, urd, uwr⟩ := hu
    refine ⟨?_, u9.trans h9', u8.trans h8', up.trans hp, um.trans hm, urd.trans hrd,
      uwr.trans hwr⟩
    rw [u11, h11, hp, hm, gather_succ]

/-! ## Picking the byte of the doubleword -/

/-- The doubleword shifted to byte `L`, once bytes `0, …, j - 1` are visited. -/
def pick (q : BitVec 64) (L j : Nat) : BitVec 64 := if L < j then q >>> (8 * L) else 0

theorem pick_succ (q : BitVec 64) (L j : Nat) :
    pick q L j ||| (if L = j then q >>> (8 * j) else 0) = pick q L (j + 1) := by
  unfold pick
  by_cases h0 : L < j
  · simp [h0, show ¬ L = j by omega, show L < j + 1 by omega]
  · by_cases h1 : L = j
    · subst h1; simp
    · simp [h0, h1, show ¬ L < j + 1 by omega]

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 8)
    (h9 : s.gpr .r9 = idx.setWidth 64) (h8 : s.gpr .r8 = 0) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .r10 = s.gpr .r10 ||| (if idx.toNat % 8 = j then s.gpr .r11 else 0) ∧
      t.gpr .r11 = s.gpr .r11 >>> 8 ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r3 = s.gpr .r3 ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  unfold pickStep laneMask isZero
  rrun [h9, h8, show j < 2 ^ 15 by omega]
  rw [lane_mask idx hj, and_allOnes_ite]

def PInv (s₀ : State) (q : BitVec 64) (L j : Nat) (t : State) : Prop :=
  t.gpr .r10 = pick q L j ∧ t.gpr .r11 = q >>> (8 * j) ∧ t.gpr .r9 = s₀.gpr .r9 ∧
    t.gpr .r8 = s₀.gpr .r8 ∧ t.gpr .r3 = s₀.gpr .r3 ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧
    t.wr = s₀.wr

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 64) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (h8 : s₀.gpr .r8 = 0) :
    ∀ n ≤ 8, ∀ s, PInv s₀ q (idx.toNat % 8) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (PInv s₀ q (idx.toNat % 8) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨hax, h11, h9', h8', hp, hm, hrd, hwr⟩ := ht
    refine WP.mono (pick_step t idx (by omega) (h9'.trans h9) (h8'.trans h8)) fun u hu => ?_
    obtain ⟨uax, u11, u9, u8, up, um, urd, uwr⟩ := hu
    refine ⟨?_, ?_, u9.trans h9', u8.trans h8', up.trans hp, um.trans hm, urd.trans hrd,
      uwr.trans hwr⟩
    · rw [uax, hax, h11, pick_succ]
    · rw [u11, h11, shr_byte]

/-! ## The lookup -/

theorem low8 (x : BitVec 64) : (x <<< 56) >>> 56 = x &&& BitVec.ofNat 64 255 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem lookup_core (s : State) (idx : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (h8 : s.gpr .r8 = 0) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r3 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.li .r11 0]) s (GInv s idx 0) := by
    rrun [GInv, gather, Nat.not_lt_zero]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps s idx h9 h8 hr 32 (by decide) t ht) fun u hu => ?_
  obtain ⟨u11, u9, u8, up, um, urd, uwr⟩ := hu
  let q := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * (idx.toNat / 8))) 64
  have hq : u.gpr .r11 = q := by
    rw [u11]; unfold gather; rw [ite_eq_left (by omega)]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.li .r10 0]) u (PInv s q (idx.toNat % 8) 0) := by
    rrun [PInv, pick, hq, u9, u8, up, um, urd, uwr, Nat.mul_zero, BitVec.ushiftRight_zero,
      Nat.not_lt_zero]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pick_steps s idx q h9 h8 8 (by decide) v hv) fun w hw => ?_
  obtain ⟨wax, _, _, _, _, wm, _, _⟩ := hw
  have hL : idx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rrun [wax, wm]
  unfold pick
  rw [low8, ite_eq_left hL, qword_byte _ _ hL, row_lane]

end VG.Proof.Rc4.PPC64LE
