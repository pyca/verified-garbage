import VerifiedGarbage.Proof.Rc4.Arm.Run

/-! # RC4 on ARMv7: the table lookup, a word at a time -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

/-- The mask `cmp x, #n` and `adc d, ones, #0` leave, applied to `y`: all
ones if `x < n`. -/
theorem cmp_mask (x : BitVec 32) {n : Nat} (hn : n < 2 ^ 32) {P : Prop} [Decidable P]
    (h : x.toNat < n ↔ P) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 +
      BitVec.ofNat 32 (decide ((BitVec.ofNat 32 n).toNat ≤ x.toNat)).toNat) &&& y =
      if P then y else 0 := by
  rw [adc_mask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  by_cases hp : P
  · rw [ite_eq_right (by simp only [decide_eq_true_eq]; have := h.mpr hp; omega), ite_eq_left hp]
  · rw [ite_eq_left (by simp only [decide_eq_true_eq]; have := mt h.mp hp; omega),
      ite_eq_right hp]

/-- The mask `rowMask` leaves. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 64) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 (decide ((BitVec.ofNat 32 4).toNat ≤
      (idx.setWidth 32 ^^^ BitVec.ofNat 32 (4 * k)).toNat)).toNat) &&& y =
      if idx.toNat / 4 = k then y else 0 :=
  cmp_mask _ (by decide) (row_hit32 idx hk) y

/-- The mask `laneMask` leaves. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 4) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 (decide ((BitVec.ofNat 32 1).toNat ≤
      ((idx.setWidth 32 &&& BitVec.ofNat 32 3) ^^^ BitVec.ofNat 32 j).toNat)).toNat) &&& y = if idx.toNat % 4 = j then y else 0 :=
  cmp_mask _ (by decide) (lane_hit32 idx hj) y

/-! ## Visiting the words -/

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32)
    (hfit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .r8 = s.gpr .r8 |||
        (if idx.toNat / 4 = k then s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * k)) 32
          else 0) ∧ t.mem = s.mem := by
  have he : encodable (BitVec.ofNat 32 (4 * k)) = true := encodable_lt (by omega)
  have ho : 4 * k < 4096 := by omega
  rw [← row_addr hfit hk] at hr
  unfold gatherStep rowMask
  arun [h6, h10, he, ho, hr]
  rw [row_addr hfit hk, row_mask idx hk]

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .r8 = gather s₀.mem (State.addr (s₀.gpr .r12)) idx.toNat k ∧ t.gpr .r6 = s₀.gpr .r6 ∧
    t.gpr .r10 = s₀.gpr .r10 ∧ t.gpr .r12 = s₀.gpr .r12 ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧
    t.wr = s₀.wr

theorem gather_steps (s₀ : State) (idx : Byte) (h6 : s₀.gpr .r6 = idx.setWidth 32)
    (h10 : s₀.gpr .r10 = BitVec.allOnes 32) (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r12)) 256) :
    ∀ n ≤ 64, ∀ s, GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h8, h6', h10', h12, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r12) + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [hrd, hwr, h12]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (WP.keep [.r8, .r9, .r11]
      (gather_step t idx (by omega) (h6'.trans h6) (h10'.trans h10) (by rw [h12]; exact hfit) hq)
      rfl) fun u ⟨⟨u8, um⟩, uk⟩ => ?_
    refine ⟨?_, (uk.gpr (by decide)).trans h6', (uk.gpr (by decide)).trans h10',
      (uk.gpr (by decide)).trans h12, um.trans hm, uk.2.1.trans hrd, uk.2.2.1.trans hwr⟩
    rw [u8, h8, h12, hm, gather_succ]

/-! ## Picking the byte of the word -/

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 4)
    (h6 : s.gpr .r6 = idx.setWidth 32) (h10 : s.gpr .r10 = BitVec.allOnes 32) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .r7 = s.gpr .r7 ||| (if idx.toNat % 4 = j then s.gpr .r8 else 0) ∧
      t.gpr .r8 = s.gpr .r8 >>> 8 ∧ t.mem = s.mem := by
  have he : encodable (BitVec.ofNat 32 j) = true := encodable_lt (by omega)
  unfold pickStep laneMask
  arun [h6, h10, he]
  rw [lane_mask idx hj]

def PInv (s₀ : State) (q : BitVec 32) (L j : Nat) (t : State) : Prop :=
  t.gpr .r7 = pick q L j ∧ t.gpr .r8 = q >>> (8 * j) ∧ t.gpr .r6 = s₀.gpr .r6 ∧
    t.gpr .r10 = s₀.gpr .r10 ∧ t.mem = s₀.mem

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 32) (h6 : s₀.gpr .r6 = idx.setWidth 32)
    (h10 : s₀.gpr .r10 = BitVec.allOnes 32) :
    ∀ n ≤ 4, ∀ s, PInv s₀ q (idx.toNat % 4) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (PInv s₀ q (idx.toNat % 4) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h7, h8, h6', h10', hm⟩ := ht
    refine WP.mono (WP.keep [.r7, .r8, .r9]
      (pick_step t idx (by omega) (h6'.trans h6) (h10'.trans h10)) rfl)
      fun u ⟨⟨u7, u8, um⟩, uk⟩ => ?_
    refine ⟨?_, ?_, (uk.gpr (by decide)).trans h6', (uk.gpr (by decide)).trans h10', um.trans hm⟩
    · rw [u7, h7, h8, pick_succ]
    · rw [u8, h8, shr_byte32]

/-! ## The lookup -/

/-- What a lookup or replacement needs: the index, all ones, and the table. -/
structure TableEnv (s : State) (idx : Byte) : Prop where
  idx : s.gpr .r6 = idx.setWidth 32
  ones : s.gpr .r10 = BitVec.allOnes 32
  fit : (s.gpr .r12).toNat + 256 ≤ 2 ^ 32
  table : InRegions s.wr (State.addr (s.gpr .r12)) 256

theorem TableEnv.read {s : State} {idx : Byte} (h : TableEnv s idx) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12)) 256 := region_in h.table

theorem lookup_core (s : State) (idx : Byte) (h : TableEnv s idx) :
    WP isa (.block lookup) s fun t =>
      t.gpr .r7 = (s.mem (State.addr (s.gpr .r12) + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .r8 (imm 0)]) s (GInv s idx 0) := by
    arun [GInv, gather, Nat.not_lt_zero]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps s idx h.idx h.ones h.fit h.read 64 (by decide) t ht)
    fun u hu => ?_
  obtain ⟨u8, u6, u10, _, um, _, _⟩ := hu
  let q := s.mem.readW (State.addr (s.gpr .r12) + BitVec.ofNat 64 (4 * (idx.toNat / 4))) 32
  have hq : u.gpr .r8 = q := by
    rw [u8]; unfold gather; rw [ite_eq_left (by omega)]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .r7 (imm 0)]) u (PInv s q (idx.toNat % 4) 0) := by
    arun [PInv, pick, hq, u6, u10, um, Nat.mul_zero, BitVec.ushiftRight_zero, Nat.not_lt_zero]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pick_steps s idx q h.idx h.ones 4 (by decide) v hv) fun w hw => ?_
  obtain ⟨w7, _, _, _, wm⟩ := hw
  have hL : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  arun [w7, wm]
  unfold pick
  rw [ite_eq_left hL, dword_byte _ _ hL, row_lane32]

end VG.Proof.Rc4.Arm
