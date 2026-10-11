import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Blowfish.Scan32

/-!
# Blowfish on ARMv7: an S-box lookup

`lookup_run`: `lookup j` leaves S-box `j`'s entry for xL's byte `3 - j` in
the accumulator, changing only the lookup's registers and the flags.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- What a lookup needs: the schedule at `r0` readable, without wrapping
around, and all ones in `r8`. -/
structure LookEnv (s : State) : Prop where
  fit : (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 o) 4
  ones : s.gpr .r8 = BitVec.allOnes 32

/-- The registers a lookup writes. -/
def lookRegs : List Reg := [.r4, .r5, .r6, .r7, .r9, .r10, .r11]

theorem LookEnv.keep {s t : State} (E : LookEnv s) {rs : List Reg} (h : Keep rs s t)
    (h0 : Reg.r0 ∉ rs) (h8 : Reg.r8 ∉ rs) : LookEnv t := by
  refine ⟨by rw [h.gpr h0]; exact E.fit, fun o ho => ?_, by rw [h.gpr h8]; exact E.ones⟩
  rw [h.gpr h0, h.2.1, h.2.2.1]; exact E.rd o ho

/-! ## The index -/

theorem index_val (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (if j = 0 then x >>> 24 else if j = 3 then x &&& BitVec.ofNat 32 255 else (x <<< (8 * j)) >>> 24) =
      (quarter x j).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h255 : (BitVec.ofNat 32 255).getLsbD i = decide (i < 8) := by
    change Nat.testBit 255 i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  simp only [ite_true, ite_false, reduceCtorEq, Nat.reduceEqDiff, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, h255, Nat.reduceMul, Nat.reduceSub, hi,
    decide_true, Bool.true_and] <;>
  by_cases h8 : i < 8 <;> simp (disch := omega) [h8, BitVec.getLsbD_of_ge] <;>
  first
  | (intro h; omega)
  | (simp (disch := omega) [show 24 + i - 8 = 16 + i by omega, show 24 + i - 16 = 8 + i by omega]
     omega)

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .r4 = (quarter (s.gpr .r1) j).setWidth 32 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [index] <;> rfl

/-! ## Rotations selected by a bit of the index -/

/-- The bit `c` (1 or 2) of `q` set. -/
def bitSet (q : BitVec 32) (c : Nat) : Bool := decide ((BitVec.ofNat 32 1).toNat ≤ (q &&& BitVec.ofNat 32 c).toNat)

theorem condRot_run (s : State) (x : Reg) {c a : Nat} (hc : c < 256) (ha1 : 1 ≤ a) (ha : a ≤ 31)
    (h8 : s.gpr .r8 = BitVec.allOnes 32) (x4 : x ≠ .r4) (x6 : x ≠ .r6) (x8 : x ≠ .r8) (x9 : x ≠ .r9) :
    WP isa (.block (condRot x c a)) s fun t =>
      t.gpr x = (if bitSet (s.gpr .r4) c then (s.gpr x).rotateRight a else s.gpr x) ∧ t.mem = s.mem := by
  have hx4 : Reg.r4 ≠ x := Ne.symm x4
  have hx6 : Reg.r6 ≠ x := Ne.symm x6
  have hx9 : Reg.r9 ≠ x := Ne.symm x9
  have hx8 : Reg.r8 ≠ x := Ne.symm x8
  have e1 : encodable (BitVec.ofNat 32 c) = true := encodable_lt hc
  unfold condRot
  brun [h8, x4, x6, x8, x9, hx4, hx6, hx8, hx9, e1, ha1, ha]
  rw [select_rot]
  rfl

/-- What the rotations of `condRot` amount to, for a byte index. -/
theorem bitSet_lane (q : BitVec 32) {L : Nat} (hL : q.toNat % 4 = L) :
    bitSet q 1 = decide (L % 2 = 1) ∧ bitSet q 2 = decide (L / 2 = 1) := by
  have h3 : ∀ c, c = 1 ∨ c = 2 → q &&& BitVec.ofNat 32 c = BitVec.ofNat 32 L &&& BitVec.ofNat 32 c := by
    intro c hc
    have e : q &&& BitVec.ofNat 32 3 = BitVec.ofNat 32 L := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
      rw [show (3 % 2 ^ 32 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have e' : ∀ d : BitVec 32, d = BitVec.ofNat 32 3 &&& d → q &&& d = BitVec.ofNat 32 L &&& d := by
      intro d hd
      conv => lhs; rw [hd]
      rw [← BitVec.and_assoc, e]
    rcases hc with rfl | rfl
    · exact e' _ (by decide)
    · exact e' _ (by decide)
  have hl : L < 4 := by omega
  unfold bitSet
  rw [h3 1 (.inl rfl), h3 2 (.inr rfl)]
  rcases (by omega : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The lane mask: 255 rotated left a byte if bit 0 of the lane is set, then
two if bit 1 is. -/
theorem laneMask_rot {L : Nat} (hL : L < 4) :
    (if decide (L / 2 = 1) then
        (if decide (L % 2 = 1) then (BitVec.ofNat 32 255).rotateRight 24 else BitVec.ofNat 32 255).rotateRight 16
      else if decide (L % 2 = 1) then (BitVec.ofNat 32 255).rotateRight 24 else BitVec.ofNat 32 255) =
      laneMask L := by
  rcases (by omega : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;> decide

theorem ror_ror (x : BitVec 32) {a b : Nat} (h : a + b < 32) :
    (x.rotateRight a).rotateRight b = x.rotateRight (a + b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateRight_of_lt (show b < 32 by omega),
    BitVec.getLsbD_rotateRight_of_lt (show a < 32 by omega), BitVec.getLsbD_rotateRight_of_lt h]
  have d : ∀ n, n < 32 → decide (n < 32) = true := fun n hn => decide_eq_true hn
  split <;> split <;> (try split) <;>
    first
    | omega
    | (congr 1; omega)
    | (rw [d _ (by omega), Bool.true_and]; congr 1; omega)
    | (rw [d _ (by omega), Bool.true_and, d _ (by omega), Bool.true_and]; congr 1; omega)

set_option linter.unusedSimpArgs false in
/-- The accumulator rotated right by the lane's bytes. -/
theorem acc_rot (x : BitVec 32) {L : Nat} (hL : L < 4) :
    (if decide (L / 2 = 1) then
        (if decide (L % 2 = 1) then x.rotateRight 8 else x).rotateRight 16
      else if decide (L % 2 = 1) then x.rotateRight 8 else x) = x.rotateRight (8 * L) := by
  have r0 : x.rotateRight 0 = x := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]
  rcases (by omega : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, decide_true, decide_false, ite_true,
      ite_false, Bool.false_eq_true, r0, ror_ror x (show 8 + 16 < 32 by decide)] <;> rfl

/-! ## The rows -/

theorem row_mask (q lm : BitVec 32) :
    (BitVec.allOnes 32 + 0#32 + BitVec.ofNat 32 (decide ((4#32).toNat ≤ q.toNat)).toNat &&& lm) =
      if 4 ≤ q.toNat then 0 else lm := by
  have e := adc_ones (decide ((4#32).toNat ≤ q.toNat))
  rw [show BitVec.ofNat 32 0 = 0#32 from rfl] at e
  rw [e]
  by_cases h : 4 ≤ q.toNat
  · simp [h]
  · simp only [BitVec.toNat_ofNat, h, decide_false, Bool.false_eq_true, ite_false,
      BitVec.allOnes_and]

theorem row_run (u : State) {j : Nat} (hj : j < 4) {q rp acc lm cnt : BitVec 32}
    (h4 : u.gpr .r4 = q) (h5 : u.gpr .r5 = acc) (h7 : u.gpr .r7 = lm)
    (h8 : u.gpr .r8 = BitVec.allOnes 32) (h10 : u.gpr .r10 = rp) (h11 : u.gpr .r11 = cnt)
    (hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (State.addr (rp + BitVec.ofNat 32 (planeOff j b))) 4) :
    WP isa (.block (row j)) u fun t =>
      let M := if 4 ≤ q.toNat then 0 else lm
      let w := fun b => u.mem.readW (State.addr (rp + BitVec.ofNat 32 (planeOff j b))) 32 &&& M
      t.gpr .r5 = (((acc ||| w 0) ||| (w 1).rotateRight 24) ||| (w 2).rotateRight 16) |||
        (w 3).rotateRight 8 ∧
      t.gpr .r4 = q - BitVec.ofNat 32 4 ∧ t.gpr .r10 = rp + BitVec.ofNat 32 4 ∧
      t.gpr .r11 = cnt - BitVec.ofNat 32 1 ∧ t.z = (cnt - BitVec.ofNat 32 1 == 0#32) ∧ t.mem = u.mem := by
  have o : ∀ b < 4, planeOff j b < 4096 := fun b hb => by unfold planeOff; omega
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  have o0 := o 0 (by decide)
  have o1 := o 1 (by decide)
  have o2 := o 2 (by decide)
  have o3 := o 3 (by decide)
  unfold row plane
  brun [h4, h5, h7, h8, h10, h11, r0, r1, r2, r3, o0, o1, o2, o3]
  rw [row_mask]

theorem addr_row {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) {j b k : Nat} (hj : j < 4) (hb : b < 4)
    (hk : k < 64) :
    State.addr (S + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 (planeOff j b)) =
      State.addr S + BitVec.ofNat 64 (1024 * j + 256 * b + 4 * k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by unfold planeOff; omega)]
  congr 2; unfold planeOff; omega

/-- The lane mask, the accumulator, the row pointer and the rows left. -/
theorem start_run (s : State) (h8 : s.gpr .r8 = BitVec.allOnes 32) {L : Nat}
    (hL : (s.gpr .r4).toNat % 4 = L) :
    WP isa (.block lookupStart) s fun t =>
      t.gpr .r7 = laneMask L ∧ t.gpr .r5 = 0 ∧ t.gpr .r10 = s.gpr .r0 ∧ t.gpr .r11 = BitVec.ofNat 32 64 ∧
        t.mem = s.mem := by
  have hl : L < 4 := by omega
  obtain ⟨b1, b2⟩ := bitSet_lane _ hL
  unfold lookupStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov lane (imm 255)]) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 255 ∧ t.mem = s.mem := by brun
  refine WP.mono (WP.keep [.r7] h0 (by decide)) fun t₀ ⟨⟨t7, tm⟩, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r6, .r7, .r9] (condRot_run t₀ .r7 (c := 1) (a := 24) (by decide) (by decide)
    (by decide) (by rw [tk.gpr (by decide), h8]) (by decide) (by decide) (by decide) (by decide))
    (by decide)) fun t₁ ⟨⟨u7, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r6, .r7, .r9] (condRot_run t₁ .r7 (c := 2) (a := 16) (by decide) (by decide)
    (by decide) (by rw [uk.gpr (by decide), tk.gpr (by decide), h8]) (by decide) (by decide) (by decide)
    (by decide)) (by decide)) fun t₂ ⟨⟨v7, vm⟩, vk⟩ => ?_
  have q1 : t₀.gpr .r4 = s.gpr .r4 := tk.gpr (by decide)
  have q2 : t₁.gpr .r4 = s.gpr .r4 := (uk.gpr (by decide)).trans q1
  have z0 : t₂.gpr .r0 = s.gpr .r0 := by rw [vk.gpr (by decide), uk.gpr (by decide), tk.gpr (by decide)]
  have e7 : t₂.gpr .r7 = laneMask L := by rw [v7, u7, q2, q1, t7, b1, b2]; exact laneMask_rot hl
  have em : t₂.mem = s.mem := by rw [vm, um, tm]
  brun [z0, e7, em]
  rfl


/-- After `k` rows of S-box `j` for the index `idx`, from the lookup's start
`s₀`. -/
structure RowInv (s₀ : State) (j : Nat) (idx : Byte) (k : Nat) (u : State) : Prop where
  q : u.gpr .r4 = idx.setWidth 32 - BitVec.ofNat 32 (4 * k)
  acc : u.gpr .r5 = scanAcc s₀.mem (State.addr (s₀.gpr .r0)) j idx.toNat k
  lane : u.gpr .r7 = laneMask (idx.toNat % 4)
  rp : u.gpr .r10 = s₀.gpr .r0 + BitVec.ofNat 32 (4 * k)
  cnt : u.gpr .r11 = BitVec.ofNat 32 (64 - k)
  keep : Keep lookRegs s₀ u
  mem : u.mem = s₀.mem

theorem mask_hit (idx : Byte) {k : Nat} (hk : k < 64) (lm : BitVec 32) :
    (if 4 ≤ (idx.setWidth 32 - BitVec.ofNat 32 (4 * k)).toNat then 0 else lm) =
      if idx.toNat / 4 = k then lm else 0 := by
  have h := row_hit idx hk
  by_cases e : idx.toNat / 4 = k
  · rw [ite_eq_right (by omega), ite_eq_left e]
  · rw [ite_eq_left (by omega), ite_eq_right e]

theorem row_step {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {k : Nat}
    (hk : k < 64) {u : State} (I : RowInv s₀ j idx k u) :
    WP isa (.block (row j)) u fun u' =>
      RowInv s₀ j idx (k + 1) u' ∧ u'.z = (BitVec.ofNat 32 (64 - (k + 1)) == 0#32) := by
  have fit := E.fit
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2.1]
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr)
      (State.addr (s₀.gpr .r0 + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 (planeOff j b))) 4 :=
    fun b hb => by rw [addr_row fit hj hb hk, hrd]; exact E.rd _ (by omega)
  have h8 : u.gpr .r8 = BitVec.allOnes 32 := by rw [I.keep.gpr (by decide)]; exact E.ones
  refine WP.mono (WP.keep [.r4, .r5, .r6, .r9, .r10, .r11]
    (row_run u hj I.q I.acc I.lane h8 I.rp I.cnt hr) (by simp [writesOnly, row, plane, dstOf, mReg, qReg, tmp, acc, rowPtr, rows])) fun u' ⟨⟨a5, a4, a10, a11, az, am⟩, ak⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, I.keep.trans_sub ak (by decide), am.trans I.mem⟩, ?_⟩
  · rw [a4, BitVec.sub_sub, ← BitVec.ofNat_add]; congr 2
  · dsimp only at a5
    rw [a5, mask_hit idx hk, I.mem]
    simp only [addr_row fit hj (show 0 < 4 by decide) hk, addr_row fit hj (show 1 < 4 by decide) hk,
      addr_row fit hj (show 2 < 4 by decide) hk, addr_row fit hj (show 3 < 4 by decide) hk]
    exact scanAcc_succ _ _ _ _ _ _ rfl
  · rw [ak.gpr (by decide), I.lane]
  · rw [a10, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · rw [a11]; apply BitVec.eq_of_toNat_eq; simp; omega
  · rw [az]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega


theorem rows_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {u : State}
    (I : RowInv s₀ j idx 0 u) : WP isa (.loop (.block (row j)) .ne) u (RowInv s₀ j idx 64) := by
  refine WP.loop (M := isa) (Q := RowInv s₀ j idx 64)
    (fun (n : Nat) (v : State) => ∃ k, k < 64 ∧ n = 64 - k ∧ RowInv s₀ j idx k v) ?_ 64 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨k, hk, hn, J⟩
  refine WP.mono (row_step E hj idx hk J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : k + 1 = 64
  · left
    refine ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    refine ⟨?_, n - 1, by omega, k + 1, by omega, by omega, J'⟩
    have : BitVec.ofNat 32 (64 - (k + 1)) ≠ 0#32 := by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega
    rw [show (BitVec.ofNat 32 (64 - (k + 1)) == 0#32) = false from beq_eq_false_iff_ne.mpr this]; rfl

theorem sub256_mod (idx : Byte) : (idx.setWidth 32 - BitVec.ofNat 32 (4 * 64)).toNat % 4 = idx.toNat % 4 := by
  have := idx.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 32 by omega)]
  omega

/-- The lookup of S-box `j` for xL's byte `3 - j`. -/
theorem lookup_run {s : State} (E : LookEnv s) {j : Nat} (hj : j < 4) :
    WP isa (lookup j) s fun t =>
      t.gpr .r5 = sEntry (scheduleAt s.mem (State.addr (s.gpr .r0))) j (quarter (s.gpr .r1) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter (s.gpr .r1) j
  unfold lookup
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r4] (index_run s hj) (by
    unfold index; split <;> (try split) <;> simp [writesOnly, dstOf, qReg])) fun t ⟨⟨t4, tm⟩, tk⟩ => ?_
  have hL : (t.gpr .r4).toNat % 4 = idx.toNat % 4 := by rw [t4, BitVec.toNat_setWidth]; simp [idx]
  refine WP.mono (WP.keep [.r5, .r6, .r7, .r9, .r10, .r11]
    (start_run t (by rw [tk.gpr (by decide)]; exact E.ones) hL) (by
      simp [writesOnly, lookupStart, condRot, dstOf, lane, mReg, tmp, acc, rowPtr, rows]))
    fun u ⟨⟨u7, u5, u10, u11, um⟩, uk⟩ => ?_
  have K0 : Keep lookRegs s u := (tk.trans uk).mono (by decide)
  have I0 : RowInv s j idx 0 u := by
    refine ⟨?_, by rw [u5, scanAcc_zero], u7, ?_, by rw [u11], K0, by rw [um]; exact tm⟩
    · rw [uk.gpr (by decide), t4]; simp; rfl
    · rw [u10, tk.gpr (by decide)]; simp
  apply WP.seq
  refine WP.mono (rows_run E hj idx I0) fun v V => ?_
  have v8 : v.gpr .r8 = BitVec.allOnes 32 := by rw [V.keep.gpr (by decide)]; exact E.ones
  unfold lookupEnd
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r5, .r6, .r9] (condRot_run v .r5 (c := 1) (a := 8) (by decide) (by decide)
    (by decide) v8 (by decide) (by decide) (by decide) (by decide)) (by decide))
    fun w ⟨⟨w5, wm⟩, wk⟩ => ?_
  refine WP.mono (WP.keep [.r5, .r6, .r9] (condRot_run w .r5 (c := 2) (a := 16) (by decide) (by decide)
    (by decide) (by rw [wk.gpr (by decide), v8]) (by decide) (by decide) (by decide) (by decide))
    (by decide)) fun x ⟨⟨x5, xm⟩, xk⟩ => ?_
  have hL4 : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨b1, b2⟩ := bitSet_lane _ (sub256_mod idx)
  refine ⟨?_, (V.keep.trans wk).trans xk |>.mono (by decide), by rw [xm, wm, V.mem]⟩
  rw [x5, w5, wk.gpr (by decide), V.q, b1, b2, acc_rot _ hL4, V.acc, scanAcc_all]
  exact hitWord_ror _ _ hj idx

end VG.Proof.Blowfish.Arm
