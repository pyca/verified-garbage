module

import VerifiedGarbage.Proof.Blowfish.Blocks
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Blowfish.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Blowfish.Feistel
public import VerifiedGarbage.Proof.Blowfish.Arm.Run
public import VerifiedGarbage.Proof.Blowfish.Scan32
public import VerifiedGarbage.Proof.Blowfish.F

/-! ### `Blowfish.Arm.Cipher`, which this module and modules that import it used -/

section

/-! ### `Blowfish.Arm.Lookup`, which only this module used -/

section

/-!
# Blowfish on ARMv7: an S-box lookup

`lookup_run`: `lookup j` leaves S-box `j`'s entry for xL's byte `3 - j` in
the accumulator, changing only the lookup's registers and the flags.
-/

@[expose] public section

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
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  simp only [ite_true, ite_false, reduceCtorEq, Nat.reduceEqDiff, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, h255, Nat.reduceMul, Nat.reduceSub, hi,
    decide_true, Bool.true_and] <;>
  by_cases h8 : i < 8 <;> simp (disch := omega) [h8, BitVec.getLsbD_of_ge] <;>
  first
  | (intro h; omega_using [h8, h])
  | (simp (disch := omega) [show 24 + i - 8 = 16 + i by omega_using [], show 24 + i - 16 = 8 + i by omega_using []]
     omega_using [h8])

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .r4 = (quarter (s.gpr .r1) j).setWidth 32 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
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
      omega_using [hL]
    have e' : ∀ d : BitVec 32, d = BitVec.ofNat 32 3 &&& d → q &&& d = BitVec.ofNat 32 L &&& d := by
      intro d hd
      conv => lhs; rw [hd]
      rw [← BitVec.and_assoc, e]
    rcases hc with rfl | rfl
    · exact e' _ (by decide)
    · exact e' _ (by decide)
  have hl : L < 4 := by omega_using [hL]
  unfold bitSet
  rw [h3 1 (.inl rfl), h3 2 (.inr rfl)]
  rcases (by omega_using [hL] : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;> decide

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
  have o : ∀ b < 4, planeOff j b < 4096 := fun b hb => by unfold planeOff; omega_using [hj, hb]
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
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by unfold planeOff; omega_using [fit, hj, hb, hk])]
  congr 2; unfold planeOff; omega_using []

/-- The lane mask, the accumulator, the row pointer and the rows left. -/
theorem start_run (s : State) (h8 : s.gpr .r8 = BitVec.allOnes 32) {L : Nat}
    (hL : (s.gpr .r4).toNat % 4 = L) :
    WP isa (.block lookupStart) s fun t =>
      t.gpr .r7 = laneMask L ∧ t.gpr .r5 = 0 ∧ t.gpr .r10 = s.gpr .r0 ∧ t.gpr .r11 = BitVec.ofNat 32 64 ∧
        t.mem = s.mem := by
  have hl : L < 4 := by omega_using [hL]
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

theorem row_step {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {k : Nat}
    (hk : k < 64) {u : State} (I : RowInv s₀ j idx k u) :
    WP isa (.block (row j)) u fun u' =>
      RowInv s₀ j idx (k + 1) u' ∧ u'.z = (BitVec.ofNat 32 (64 - (k + 1)) == 0#32) := by
  have fit := E.fit
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2.1]
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr)
      (State.addr (s₀.gpr .r0 + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 (planeOff j b))) 4 :=
    fun b hb => by rw [addr_row fit hj hb hk, hrd]; exact E.rd _ (by omega_using [hj, hk, hb])
  have h8 : u.gpr .r8 = BitVec.allOnes 32 := by rw [I.keep.gpr (by decide)]; exact E.ones
  refine WP.mono (WP.keep [.r4, .r5, .r6, .r9, .r10, .r11]
    (row_run u hj I.q I.acc I.lane h8 I.rp I.cnt hr) (by rfl)) fun u' ⟨⟨a5, a4, a10, a11, az, am⟩, ak⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, I.keep.trans_sub ak (by decide), am.trans I.mem⟩, ?_⟩
  · rw [a4, BitVec.sub_sub, ← BitVec.ofNat_add]; congr 2
  · dsimp only at a5
    rw [a5, mask_hit idx hk, I.mem]
    simp only [addr_row fit hj (show 0 < 4 by decide) hk, addr_row fit hj (show 1 < 4 by decide) hk,
      addr_row fit hj (show 2 < 4 by decide) hk, addr_row fit hj (show 3 < 4 by decide) hk]
    exact scanAcc_succ _ _ _ _ _ _ rfl
  · rw [ak.gpr (by decide), I.lane]
  · rw [a10, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · rw [a11]; apply BitVec.eq_of_toNat_eq; simp; omega_using [hk]
  · rw [az]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega_using [hk]


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
    refine ⟨?_, n - 1, by omega_using [hk, hn], k + 1, by omega_using [hk, e], by omega_using [hn], J'⟩
    have : BitVec.ofNat 32 (64 - (k + 1)) ≠ 0#32 := by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega_using [hk, e, this]
    rw [show (BitVec.ofNat 32 (64 - (k + 1)) == 0#32) = false from beq_eq_false_iff_ne.mpr this]; rfl

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
    unfold index; split <;> (try split) <;> rfl)) fun t ⟨⟨t4, tm⟩, tk⟩ => ?_
  have hL : (t.gpr .r4).toNat % 4 = idx.toNat % 4 := by rw [t4, BitVec.toNat_setWidth]; simp [idx]
  refine WP.mono (WP.keep [.r5, .r6, .r7, .r9, .r10, .r11]
    (start_run t (by rw [tk.gpr (by decide)]; exact E.ones) hL) (by
      rfl))
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

end

end

/-! ### `Blowfish.Arm.F`, which only this module used -/

section

/-!
# Blowfish on ARMv7: F

`f_run`: F of xL (`r1`) into `lr`, one S-box at a time (`fAcc`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- The registers F writes. -/
def fRegs : List Reg := .lr :: lookRegs

theorem combine_run (u : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [combine j]) u fun t =>
      t.gpr .lr = (if j = 0 then u.gpr .r5 else if j = 2 then u.gpr .lr ^^^ u.gpr .r5
        else u.gpr .lr + u.gpr .r5) ∧ t.mem = u.mem := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [combine]

/-- S-box `j`'s lookup, then its accumulation, from `fAcc … (j - 1)` (or
anything, for `j = 0`) in `lr`. -/
theorem step_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) {u : State} (k : Keep fRegs s₀ u)
    (hm : u.mem = s₀.mem) (h3 : 0 < j → u.gpr .lr = fAcc (scheduleAt s₀.mem (State.addr (s₀.gpr .r0)))
      (s₀.gpr .r1) (j - 1)) {Q : State → Prop}
    (hQ : ∀ t, t.gpr .lr = fAcc (scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1) j →
      Keep fRegs s₀ t → t.mem = s₀.mem → Q t) :
    WP isa (.seq (lookup j) (.block [combine j])) u Q := by
  have Eu : LookEnv u := E.keep k (by decide) (by decide)
  apply WP.seq
  refine WP.mono (lookup_run Eu hj) fun v ⟨v5, vk, vm⟩ => ?_
  refine WP.mono (WP.keep [.lr] (combine_run v hj) (by
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide))
    fun t ⟨⟨t3, tm⟩, tk⟩ => hQ t ?_ ((k.trans vk).trans tk |>.mono (by decide)) (by rw [tm, vm, hm])
  have e0 : u.gpr .r0 = s₀.gpr .r0 := k.gpr (by decide)
  have e1 : u.gpr .r1 = s₀.gpr .r1 := k.gpr (by decide)
  rw [t3, v5, hm, e0, e1, vk.gpr (by decide)]
  exact fAcc_step _ _ hj _ h3

theorem f_run {s : State} (E : LookEnv s) :
    WP isa Impl.Blowfish.Arm.f s fun t =>
      t.gpr .lr = Spec.Blowfish.f (scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1) ∧
        Keep fRegs s t ∧ t.mem = s.mem := by
  unfold Impl.Blowfish.Arm.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl (fun h => absurd h (by decide))
    fun t0 h0 k0 m0 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0 m0 (fun _ => h0) fun t1 h1 k1 m1 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1 m1 (fun _ => h1) fun t2 h2 k2 m2 => ?_
  refine step_run E (j := 3) (by decide) k2 m2 (fun _ => h2) fun t3 h3 k3 m3 => ?_
  exact ⟨by rw [h3, fAcc_three], k3, m3⟩

end VG.Proof.Blowfish.Arm

end

end


/-!
# Blowfish on ARMv7: the block function

`cipher_run`: `cipher up` takes the halves in `r1` and `r2` to their
encryption (`up`) or decryption under the schedule at `r0`, changing only
`r1`, `r2`, `r4`–`r12`, `lr` and the flags.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- `pPtr`'s offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- The registers the block function writes. -/
def cRegs : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- What the block function needs: the schedule at `r0` readable, without
wrapping around. -/
structure CipherEnv (s : State) : Prop where
  fit : (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 o) 4

theorem CipherEnv.keep {s t : State} (E : CipherEnv s) {rs : List Reg} (h : Keep rs s t)
    (h0 : Reg.r0 ∉ rs) : CipherEnv t := by
  refine ⟨by rw [h.gpr h0]; exact E.fit, fun o ho => ?_⟩
  rw [h.gpr h0, h.2.1, h.2.2.1]; exact E.rd o ho

theorem CipherEnv.look {s : State} (E : CipherEnv s) (h8 : s.gpr .r8 = BitVec.allOnes 32) : LookEnv s :=
  ⟨E.fit, E.rd, h8⟩

/-- The address of the P-array entry of round `i`. -/
theorem addr_P {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) {i : Nat} (hi : i < 16) :
    State.addr (S + BitVec.ofNat 32 (pBase up i) + BitVec.ofNat 32 (pAt up)) =
      State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up i) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by cases up <;> simp [pBase, pAt] <;> omega_arith)]
  congr 2; cases up <;> simp [pBase, pAt, ord] <;> omega_using [hi]

/-- After `i` rounds from `s₀`. -/
structure CInv (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  p : u.gpr .r12 = s₀.gpr .r0 + BitVec.ofNat 32 (pBase up i)
  halves : (u.gpr .r1, u.gpr .r2) =
    iter (scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (ord up) i (s₀.gpr .r1, s₀.gpr .r2)
  ones : u.gpr .r8 = BitVec.allOnes 32
  keep : Keep cRegs s₀ u
  mem : u.mem = s₀.mem

theorem round_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : State.addr (u.gpr .r12 + BitVec.ofNat 32 (pAt up)) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.ldr tmp pPtr (pAt up), .dp .eor xL xL (.reg tmp)]) u fun t =>
      t.gpr .r1 = u.gpr .r1 ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 4096 := by cases up <;> decide
  rw [← hp] at hr hP
  brun [ho, hr, hP]

theorem round_tail (u : State) (up : Bool) (S : BitVec 32) {i : Nat} (hi : i < 16)
    (h0 : u.gpr .r0 = S) (h12 : u.gpr .r12 = S + BitVec.ofNat 32 (pBase up i)) :
    WP isa (.block [.dp .eor xR xR (.reg fReg), .mov tmp (.reg xL), .mov xL (.reg xR), .mov xR (.reg tmp),
        .dp (if up then .add else .sub) pPtr pPtr (imm 4), .dp .sub tmp pPtr (.reg sch),
        .cmp tmp (imm (if up then pOff + 64 else pOff))]) u fun t =>
      t.gpr .r1 = u.gpr .r2 ^^^ u.gpr .lr ∧ t.gpr .r2 = u.gpr .r1 ∧
        t.gpr .r12 = S + BitVec.ofNat 32 (pBase up (i + 1)) ∧
        t.z = decide (i + 1 = 16) ∧ t.mem = u.mem := by
  cases up
  · brun [h0, h12, pOff]
    simp only [pBase, Bool.false_eq_true, ite_false]
    refine ⟨ofs_sub S (by omega_using [hi]), ?_⟩
    rw [ofs_sub S (by omega_using [hi]), ofs_diff, ofNat_sub_beq (by omega_using []) (by decide)]
    congr 1; apply propext; omega_using []
  · brun [h0, h12, pOff]
    simp only [pBase, ite_true]
    refine ⟨ofs_add S _ _, ?_⟩
    rw [ofs_add, ofs_diff, ofNat_sub_beq (by omega_using [hi]) (by decide)]
    congr 1; apply propext; omega_using []

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2.1]

theorem round_step {s₀ : State} (E : CipherEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv s₀ up i u) :
    WP isa (round up) u fun u' => CInv s₀ up (i + 1) u' ∧ u'.z = decide (i + 1 = 16) := by
  have fit := E.fit
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega_arith
  let K := scheduleAt s₀.mem (State.addr (s₀.gpr .r0))
  have u0 : u.gpr .r0 = s₀.gpr .r0 := I.keep.gpr (by decide)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.r1, .r9] (round_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P fit up hi]) (by rw [keep_reads I.keep]; exact E.rd _ (by omega_using [ho]))
    (by rw [I.mem, pEntry_read _ _ ho])) (by cases up <;> decide)) fun v ⟨⟨v1, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs s₀ v := I.keep.trans_sub vk (by decide)
  have Ev : LookEnv v := (E.keep kv (by decide)).look (by rw [vk.gpr (by decide), I.ones])
  apply WP.seq
  refine WP.mono (f_run Ev) fun w ⟨w3, wk, wm⟩ => ?_
  have w0 : w.gpr .r0 = s₀.gpr .r0 := by rw [wk.gpr (by decide), vk.gpr (by decide), u0]
  have w12 : w.gpr .r12 = s₀.gpr .r0 + BitVec.ofNat 32 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.r1, .r2, .r9, .r12] (round_tail w up _ hi w0 w12) (by
    cases up <;> decide)) fun x ⟨⟨x1, x2, x12, xz, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (State.addr (v.gpr .r0)) = K := by rw [vm, I.mem, vk.gpr (by decide), u0]
  refine ⟨⟨by omega_using [hi], x12, ?_, ?_, (kv.trans_sub wk (by decide)).trans_sub xk (by decide),
    by rw [xm, wm, vm, I.mem]⟩, xz⟩
  · have w1 : w.gpr .r1 = u.gpr .r1 ^^^ pEntry K (ord up i) := by rw [wk.gpr (by decide), v1]
    have w2 : w.gpr .r2 = u.gpr .r2 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
    rw [x1, x2, w3, hK, w1, w2, iter_succ, ← I.halves]
    simp only [roundStep]
    rw [BitVec.xor_comm, v1]
  · rw [xk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), I.ones]

theorem ones_eq : ((0xFFFF : BitVec 16) ++
    (((0xFFFF : BitVec 16).setWidth 32).extractLsb' 0 16) : BitVec 32) = BitVec.allOnes 32 := by
  decide

theorem cipher_start (s : State) (up : Bool) :
    WP isa (.block (setOnes ++ ([.dp .add pPtr sch (imm (if up then pOff else pOff + 64))] : List Instr))) s fun t =>
      t.gpr .r8 = BitVec.allOnes 32 ∧ t.gpr .r12 = s.gpr .r0 + BitVec.ofNat 32 (pBase up 0) ∧
        t.mem = s.mem := by
  cases up <;> brun [setOnes, pOff, pBase, ones_eq]

theorem rounds_run {s : State} (E : CipherEnv s) (up : Bool) {u : State} (I : CInv s up 0 u) :
    WP isa (.loop (round up) .ne) u (CInv s up 16) := by
  refine WP.loop (M := isa) (Q := CInv s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : i + 1 = 16
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by simp [e], n - 1, by omega_using [hi, hn], i + 1, by omega_using [hi, e], by omega_using [hn], J'⟩

/-- The addresses of the last P-array entries. -/
theorem addr_last {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) :
    State.addr (S + BitVec.ofNat 32 (pBase up 16) + BitVec.ofNat 32 (pAt up)) =
        State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up 16) ∧
      State.addr (S + BitVec.ofNat 32 (pBase up 16) + BitVec.ofNat 32 (4 - pAt up)) =
        State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up 17) := by
  constructor <;>
  · rw [ofs_add, addr_add (by cases up <;> simp [pBase, pAt] <;> omega_using [fit])]
    congr 2; cases up <;> simp [pBase, pAt, ord]

theorem cipher_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : State.addr (u.gpr .r12 + BitVec.ofNat 32 (pAt up)) = a)
    (hb : State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 - pAt up)) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.ldr tmp pPtr (pAt up), .dp .eor tmp xL (.reg tmp),
        .ldr xL pPtr (4 - pAt up), .dp .eor xL xL (.reg xR), .mov xR (.reg tmp)]) u fun t =>
      t.gpr .r1 = P₁₇ ^^^ u.gpr .r2 ∧ t.gpr .r2 = u.gpr .r1 ^^^ P₁₆ ∧ t.mem = u.mem := by
  have ho : pAt up < 4096 := by cases up <;> decide
  have ho' : 4 - pAt up < 4096 := by cases up <;> decide
  rw [← ha] at hra h16
  rw [← hb] at hrb h17
  brun [ho, ho', hra, hrb, h16, h17]

/-- The block function. -/
theorem cipher_run {s : State} (E : CipherEnv s) (up : Bool) :
    WP isa (cipher up) s fun t =>
      (t.gpr .r1, t.gpr .r2) =
        feistel (scheduleAt s.mem (State.addr (s.gpr .r0))) (ord up) (s.gpr .r1) (s.gpr .r2) ∧
      Keep cRegs s t ∧ t.mem = s.mem := by
  have fit := E.fit
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.r8, .r12] (cipher_start s up) (by cases up <;> decide))
    fun u ⟨⟨u8, u12, um⟩, uk⟩ => ?_
  have I0 : CInv s up 0 u :=
    ⟨by decide, u12, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, u8, uk.mono (by decide), um⟩
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  obtain ⟨a16, a17⟩ := addr_last fit up
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (State.addr (s.gpr .r0))
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.r1, .r2, .r9] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * ord up 17)) (by rw [V.p]; exact a16) (by rw [V.p]; exact a17)
    (by rw [hrd]; exact E.rd _ r16) (by rw [hrd]; exact E.rd _ r17)
    (by rw [V.mem, pEntry_read _ _ o16]) (by rw [V.mem, pEntry_read _ _ o17])) (by cases up <;> decide))
    fun t ⟨⟨t1, t2, tm⟩, tk⟩ => ?_
  refine ⟨?_, V.keep.trans_sub tk (by decide), by rw [tm, V.mem]⟩
  rw [t1, t2, feistel_eq, ← V.halves, BitVec.xor_comm]

end VG.Proof.Blowfish.Arm

end

end

/-!
# Blowfish on ARMv7: ECB

`ecb_correct`: every block becomes its encryption or decryption, one at a
time; our caller's registers are saved in the working space and restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## Blocks in and out of the halves -/

theorem rev_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (rev x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact rev_bit x hb hi

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem rev_load (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    rev (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [rev_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega_arith),
    ← Mem.readW_byte m _ (by omega_arith), Offset.add_add]

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) :
    Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega_arith) (by simp only [Region.Contains]; omega_arith)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem inRegions_off {rs : List Region} {a : Addr} {N o n : Nat} (h : InRegions rs a N) (hon : o + n ≤ N) :
    InRegions rs (a + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  obtain e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega_arith

theorem inRegions_pre {rs : List Region} {a : Addr} {N n : Nat} (h : InRegions rs a N) (hn : n ≤ N) :
    InRegions rs a n := by
  have := inRegions_off (o := 0) (n := n) h (by omega_arith)
  rwa [BitVec.add_zero] at this

/-- The block at the data pointer (in the working space) into the halves. -/
theorem loadBlock_run (u : State) {B P : BitVec 32} {Ba Pa : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (e0 : State.addr (P + BitVec.ofNat 32 0) = Pa) (e4 : State.addr (P + BitVec.ofNat 32 4) = Pa + BitVec.ofNat 64 4)
    (rB : InRegions (u.rd ++ u.wr) (Ba + BitVec.ofNat 64 36) 4)
    (r0 : InRegions (u.rd ++ u.wr) Pa 4) (r4 : InRegions (u.rd ++ u.wr) (Pa + BitVec.ofNat 64 4) 4)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = P) :
    WP isa (.block loadBlock) u fun t =>
      t.gpr .r1 = decodeWord (blockAt u.mem Pa) 0 ∧ t.gpr .r2 = decodeWord (blockAt u.mem Pa) 4 ∧
        t.mem = u.mem := by
  obtain l0 := rev_load u.mem Pa (o := 0) (by decide)
  obtain l4 := rev_load u.mem Pa (o := 4) (by decide)
  rw [BitVec.add_zero] at l0
  unfold loadBlock
  brun [hlr, ptrOff, eB, e0, e4, rB, r0, r4, hP, l0, l4]

/-- The halves to the block at the data pointer, the next block's pointer,
and the counter less one. -/
theorem storeBlock_run (u : State) {B P C : BitVec 32} {Ba Pa : Addr} (hlr : u.gpr .r3 = B)
    (eB : State.addr (B + BitVec.ofNat 32 36) = Ba + BitVec.ofNat 64 36)
    (eC : State.addr (B + BitVec.ofNat 32 40) = Ba + BitVec.ofNat 64 40)
    (e0 : State.addr (P + BitVec.ofNat 32 0) = Pa) (e4 : State.addr (P + BitVec.ofNat 32 4) = Pa + BitVec.ofNat 64 4)
    (wB : InRegions u.wr (Ba + BitVec.ofNat 64 36) 8)
    (w0 : InRegions u.wr Pa 8) (dj : Region.Disjoint ⟨Ba + BitVec.ofNat 64 36, 8⟩ ⟨Pa, 8⟩)
    (hP : u.mem.readW (Ba + BitVec.ofNat 64 36) 32 = P) (hC : u.mem.readW (Ba + BitVec.ofNat 64 40) 32 = C) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = (((u.mem.writeW Pa (rev (u.gpr .r1))).writeW (Pa + BitVec.ofNat 64 4) (rev (u.gpr .r2))).writeW
          (Ba + BitVec.ofNat 64 36) (P + BitVec.ofNat 32 8)).writeW (Ba + BitVec.ofNat 64 40) (C - 1#32) ∧
        t.z = (C - 1#32 == 0#32) ∧ t.gpr .r3 = B ∧ t.gpr .r0 = u.gpr .r0 := by
  have s36 : Mem.Sep (Ba + BitVec.ofNat 64 40) 4 (Ba + BitVec.ofNat 64 36) 4 :=
    Offset.sep Ba (by decide) (by decide) (by decide)
  have sP : ∀ o, o ≤ 4 → Mem.Sep (Ba + BitVec.ofNat 64 40) 4 (Pa + BitVec.ofNat 64 o) 4 := fun o ho =>
    sep_of_disjoint ((dj.sub_left (Offset.sub Ba (d := 40) (n := 4) (e := 36) (k := 8) (by decide)
      (by decide))).sub_right (Offset.sub_base Pa (d := o) (n := 4) (k := 8) (by omega_arith)))
  have rB := inRegions_pre (n := 4) wB (by decide)
  have rC := inRegions_off (o := 4) (n := 4) wB (by decide)
  rw [Offset.add_add] at rC
  have r0 := inRegions_pre (n := 4) w0 (by decide)
  have r4 := inRegions_off (o := 4) (n := 4) w0 (by decide)
  unfold storeBlock countDown
  brun [hlr, ptrOff, cntOff, eB, eC, e0, e4, rB, rC, r0, r4, region_in (rs := u.rd) rB,
    region_in (rs := u.rd) rC, hP, hC]

/-- What the stores leave: the block's bytes, the pointer and the counter. -/
theorem stored_facts (m : Mem) (Ba Pa : Addr) (L R P C : BitVec 32)
    (dj : Region.Disjoint ⟨Ba + BitVec.ofNat 64 36, 8⟩ ⟨Pa, 8⟩) :
    let M := (((m.writeW Pa (rev L)).writeW (Pa + BitVec.ofNat 64 4) (rev R)).writeW
          (Ba + BitVec.ofNat 64 36) P).writeW (Ba + BitVec.ofNat 64 40) C
    M.readW (Ba + BitVec.ofNat 64 36) 32 = P ∧ M.readW (Ba + BitVec.ofNat 64 40) 32 = C ∧
      Frame [⟨Pa, 8⟩, ⟨Ba + BitVec.ofNat 64 36, 8⟩] m M ∧ blockAt M Pa = encodeBlock L R := by
  intro M
  obtain s36 : Mem.Sep (Ba + BitVec.ofNat 64 36) 4 (Ba + BitVec.ofNat 64 40) 4 :=
    Offset.sep Ba (by decide) (by decide) (by decide)
  refine ⟨by rw [Mem.readW_writeW_sep s36 (by decide), Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _, ?_, ?_⟩
  · have c0 : Region.Contains ⟨Pa, 8⟩ Pa (32 / 8) := Offset.contains_base Pa (d := 0) (n := 4) (k := 8)
      (by decide) (by decide) |> fun h => by rwa [BitVec.add_zero] at h
    obtain c4 : Region.Contains ⟨Pa, 8⟩ (Pa + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base Pa (by decide) (by decide)
    obtain c36 : Region.Contains ⟨Ba + BitVec.ofNat 64 36, 8⟩ (Ba + BitVec.ofNat 64 36) (32 / 8) := by
      have := Offset.contains_base (Ba + BitVec.ofNat 64 36) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this
    obtain c40 : Region.Contains ⟨Ba + BitVec.ofNat 64 36, 8⟩ (Ba + BitVec.ofNat 64 40) (32 / 8) := by
      have := Offset.contains_base (Ba + BitVec.ofNat 64 36) (d := 4) (n := 4) (k := 8) (by decide) (by decide)
      rwa [Offset.add_add] at this
    exact ((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _ c4).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ c36).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ c40
  · refine blockAt_eq _ _ _ fun i hi => ?_
    obtain dk : ∀ o, o < 8 → Region.Disjoint ⟨Pa + BitVec.ofNat 64 o, 1⟩ ⟨Ba + BitVec.ofNat 64 36, 8⟩ :=
      fun o ho => (dj.sub_right (Offset.sub_base Pa (d := o) (n := 1) (k := 8) (by omega_arith))).symm
    obtain d36 := (dk i hi).sub_right (Offset.sub (e := 36) (k := 8) (d := 36) (n := 4) Ba (by decide) (by decide))
    obtain d40 := (dk i hi).sub_right (Offset.sub (e := 36) (k := 8) (d := 40) (n := 4) Ba (by decide) (by decide))
    simp only [M]
    rw [writeW32_other _ d40, writeW32_other _ d36, encodeBlock_getD _ _ hi]
    by_cases h4 : i < 4
    · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint Pa (d := i) (n := 1) (e := 4) (k := 4) (by omega_arith)
        (by omega_arith) (by decide)), st_byte _ _ _ h4, rev_byte _ h4]
    · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega_arith, ← Offset.add_add, st_byte _ _ _ (by omega_arith),
        rev_byte _ (by omega_arith)]
      congr 2; omega_arith

/-! ## The loop -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- What ECB may assume: the schedule readable, the `n` blocks and the
working space writable, apart, none wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 4168⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩]
  keyData : (⟨State.addr (s.gpr .r0), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
  keyBuf : (⟨State.addr (s.gpr .r0), 4168⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 256⟩
  dataBuf : (⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 256⟩
  fitK : (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32
  fitD : (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32
  fitB : (s.gpr .r3).toNat + 256 ≤ 2 ^ 32

/-- After `k` blocks from `s`. -/
structure EInv (s : State) (up : Bool) (k : Nat) (u : State) : Prop where
  le : k ≤ (s.gpr .r2).toNat
  r3 : u.gpr .r3 = s.gpr .r3
  r0 : u.gpr .r0 = s.gpr .r0
  ptr : u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 32 = s.gpr .r1 + BitVec.ofNat 32 (8 * k)
  cnt : u.mem.readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 32 =
    BitVec.ofNat 32 ((s.gpr .r2).toNat - k)
  saved : Spill.Saved u.mem (State.addr (s.gpr .r3)) s.gpr saved
  done : ∀ b < k, blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) =
    blockOut (scheduleAt s.mem (State.addr (s.gpr .r0))) up (blockAt s.mem (wAt (State.addr (s.gpr .r1)) b))
  rest : ∀ b, k ≤ b → b < (s.gpr .r2).toNat →
    blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) = blockAt s.mem (wAt (State.addr (s.gpr .r1)) b)
  frame : Frame [⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem saved_slots : Spill.Slots 0 36 saved := by decide

theorem ecb_step {s : State} (h : EcbPre s) (up : Bool) {k : Nat} (hk : k < (s.gpr .r2).toNat) {u : State}
    (I : EInv s up k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) u fun u' =>
      EInv s up (k + 1) u' ∧ u'.z = (BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) == 0#32) := by
  obtain ⟨hrd, hwr, kd, kb, db, fK, fD, fB⟩ := h
  obtain hrw : u.rd ++ u.wr = [⟨State.addr (s.gpr .r0), 4168⟩,
      ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩, ⟨State.addr (s.gpr .r3), 256⟩] := by
    rw [I.rd, I.wr, hrd, hwr]; rfl
  obtain dR : (⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ : Region) ∈ u.wr := by
    rw [I.wr, hwr]; exact List.mem_cons_self
  obtain bR : (⟨State.addr (s.gpr .r3), 256⟩ : Region) ∈ u.wr := by
    rw [I.wr, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- addresses
  obtain eB : State.addr (s.gpr .r3 + BitVec.ofNat 32 36) = State.addr (s.gpr .r3) + BitVec.ofNat 64 36 :=
    addr_add (by omega_arith)
  obtain eC : State.addr (s.gpr .r3 + BitVec.ofNat 32 40) = State.addr (s.gpr .r3) + BitVec.ofNat 64 40 :=
    addr_add (by omega_arith)
  obtain eP : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k)) = wAt (State.addr (s.gpr .r1)) k :=
    addr_add (by omega_arith)
  obtain e0 : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 0) =
      wAt (State.addr (s.gpr .r1)) k := by rw [BitVec.add_zero, eP]
  obtain e4 : State.addr (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4) =
      wAt (State.addr (s.gpr .r1)) k + BitVec.ofNat 64 4 := by
    rw [ofs_add, addr_add (by omega_arith), Offset.add_add]
  obtain wK : InRegions u.wr (wAt (State.addr (s.gpr .r1)) k) 8 :=
    ⟨_, dR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain wB : InRegions u.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 8 :=
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain subK : Region.Sub ⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩ :=
    Offset.sub_base _ (by omega_arith)
  obtain subB : Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨State.addr (s.gpr .r3), 256⟩ :=
    Offset.sub_base _ (by omega_arith)
  obtain dj : Region.Disjoint ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ :=
    ((db.sub_left subK).sub_right subB).symm
  -- the block in
  apply WP.seq
  refine WP.mono (WP.keep [.r1, .r2, .r12] (loadBlock_run u I.r3 eB e0 e4
    (region_in (inRegions_pre wB (by decide))) (region_in (inRegions_pre wK (by decide)))
    (region_in (inRegions_off (o := 4) (n := 4) wK (by decide))) I.ptr) (by decide))
    fun u₁ ⟨⟨l1, l2, lm⟩, lk⟩ => ?_
  -- the cipher
  obtain hK : scheduleAt u.mem (State.addr (s.gpr .r0)) = scheduleAt s.mem (State.addr (s.gpr .r0)) :=
    scheduleAt_eq_of_frame _ I.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kd
      · exact kb
  obtain CE : CipherEnv u₁ := by
    refine ⟨by rw [lk.gpr (by decide), I.r0]; exact fK, fun o ho => ?_⟩
    rw [keep_reads lk, hrw, lk.gpr (by decide), I.r0]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₂ ⟨c12, ck, cm⟩ => ?_
  -- the block out
  obtain k₂ : Keep cRegs u u₂ := (lk.trans ck).mono (by decide)
  refine WP.mono (WP.keep [.r1, .r2, .r11, .r12] (storeBlock_run u₂ (C := BitVec.ofNat 32 ((s.gpr .r2).toNat - k))
    (by rw [k₂.gpr (by decide), I.r3]) eB eC e0 e4 (by rw [k₂.2.2.1]; exact wB) (by rw [k₂.2.2.1]; exact wK) dj
    (by rw [cm, lm]; exact I.ptr) (by rw [cm, lm]; exact I.cnt)) (by decide)) fun u₃ ⟨⟨sm, sz, slr, s0⟩, sk⟩ => ?_
  obtain ⟨M36, M40, MF, MB⟩ := stored_facts u₂.mem (State.addr (s.gpr .r3)) (wAt (State.addr (s.gpr .r1)) k)
    (u₂.gpr .r1) (u₂.gpr .r2) (s.gpr .r1 + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 8)
    (BitVec.ofNat 32 ((s.gpr .r2).toNat - k) - 1#32) dj
  rw [← sm] at M36 M40 MF MB
  obtain m₂ : u₂.mem = u.mem := by rw [cm, lm]
  rw [m₂] at MF
  obtain hcnt : BitVec.ofNat 32 ((s.gpr .r2).toNat - k) - 1#32 = BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  obtain dOther : ∀ b, b < (s.gpr .r2).toNat → b ≠ k → ∀ r ∈ [(⟨wAt (State.addr (s.gpr .r1)) k, 8⟩ : Region),
      ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩], (⟨wAt (State.addr (s.gpr .r1)) b, 8⟩ : Region).Disjoint r :=
    fun b hb hne r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact (db.sub_left (Offset.sub_base _ (by omega_arith))).sub_right subB
  obtain other : ∀ b, b < (s.gpr .r2).toNat → b ≠ k →
      blockAt u₃.mem (wAt (State.addr (s.gpr .r1)) b) = blockAt u.mem (wAt (State.addr (s.gpr .r1)) b) :=
    fun b hb hne => blockAt_frame MF (dOther b hb hne)
  obtain u₁r0 : u₁.gpr .r0 = s.gpr .r0 := by rw [lk.gpr (by decide), I.r0]
  refine ⟨⟨by omega_arith, slr, by rw [s0, k₂.gpr (by decide), I.r0], by rw [M36, ofs_add]; congr 2,
    by rw [M40, hcnt], ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_, ?_, ?_⟩, by rw [sz, hcnt]⟩
  · refine I.saved.frame saved_slots MF fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [BitVec.add_zero]
      exact (db.symm.sub_left (Region.sub_prefix (by decide))).sub_right subK
    · exact Offset.disjoint _ (by decide) (by omega_arith) (by omega_arith)
  · by_cases hbk : b = k
    · subst hbk
      rw [lm, u₁r0, l1, l2] at c12
      rw [MB, blockOut_eq, ← I.rest b (by omega_arith) hk, ← hK, ← c12]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · refine I.frame.trans (MF.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, subK⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subB⟩
  · rw [sk.2.1, k₂.2.1, I.rd]
  · rw [sk.2.2.1, k₂.2.2.1, I.wr]


theorem saved_restorable : Spill.Restorable .r3 saved := by decide

theorem restore_eq : restore = saved.map (fun (p : Reg × Nat) => Instr.ldr p.1 .r3 p.2) := rfl
theorem save_eq (rest : List Instr) :
    save ++ rest = saved.map (fun p => Instr.str p.1 .r3 p.2) ++ rest := rfl

/-- Restoring our caller's registers from the working space at `r3`. -/
theorem restore_run {u : State} {g : Reg → BitVec 32}
    (fit : (u.gpr .r3).toNat + 36 ≤ 2 ^ 32)
    (hin : ∀ d, d + 4 ≤ 36 → InRegions (u.rd ++ u.wr) (State.addr (u.gpr .r3) + BitVec.ofNat 64 d) 4)
    (hsv : Spill.Saved u.mem (State.addr (u.gpr .r3)) g saved) :
    WP isa (.block restore) u fun t => (∀ r ∈ preserved, t.gpr r = g r) ∧ t.mem = u.mem := by
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok saved_slots saved_restorable fit (fun d _ h => hin d h) hsv)
    fun t ⟨ht, _, hm, _⟩ => ⟨fun r hr => ?_, hm⟩
  have : r ∈ saved.map Prod.fst := by revert r; decide
  exact Spill.restored_reg ht this

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.Blowfish.ecb K (if up then .encrypt else .decrypt) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- What ECB guarantees. -/
structure EcbPost (s : State) (up : Bool) (t : State) : Prop where
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  blocks : blocksAt t.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
    Spec.Blowfish.ecb (scheduleAt s.mem (State.addr (s.gpr .r0))) (if up then .encrypt else .decrypt)
      (blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)

theorem ecb_correct {s : State} (h : EcbPre s) (up : Bool) : WP isa (Impl.Blowfish.Arm.ecb up) s (EcbPost s up) := by
  have H := h
  obtain ⟨hrd, hwr, kd, kb, db, fK, fD, fB⟩ := H
  obtain bR : (⟨State.addr (s.gpr .r3), 256⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain subB : Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩ ⟨State.addr (s.gpr .r3), 256⟩ :=
    Offset.sub_base _ (by omega_arith)
  obtain wB : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 8 :=
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold Impl.Blowfish.Arm.ecb
  apply WP.seq
  rw [save_eq]
  refine Spill.save_slots_ok saved_slots (by omega_arith) (fun d _ hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) ?_
  let s₁ : State := { s with mem := Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved }
  obtain eB : State.addr (s.gpr .r3 + BitVec.ofNat 32 36) = State.addr (s.gpr .r3) + BitVec.ofNat 64 36 :=
    addr_add (by omega_arith)
  obtain eC : State.addr (s.gpr .r3 + BitVec.ofNat 32 40) = State.addr (s.gpr .r3) + BitVec.ofNat 64 40 :=
    addr_add (by omega_arith)
  obtain w36 : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 4 := inRegions_pre wB (by decide)
  obtain w40 : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 4 := by
    have := inRegions_off (o := 4) (n := 4) wB (by decide); rwa [Offset.add_add] at this
  have g₁ : s₁.gpr = s.gpr := rfl
  refine WP.mono (WP.keep [.lr] (Q := fun u => u.mem = ((Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved).writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 36)
      (s.gpr .r1)).writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) (s.gpr .r2) ∧
      u.z = (s.gpr .r2 - 0#32 == 0#32)) (by brun [g₁, eB, eC, w36, w40, ptrOff, cntOff]) (by decide))
    fun u₀ ⟨⟨um, uz⟩, uk⟩ => ?_
  -- the loop's start
  obtain s36 : Mem.Sep (State.addr (s.gpr .r3) + BitVec.ofNat 64 36) 4 (State.addr (s.gpr .r3) + BitVec.ofNat 64 40) 4 :=
    Offset.sep _ (by decide) (by decide) (by decide)
  obtain F0 : Frame [⟨State.addr (s.gpr .r3), 256⟩] s.mem u₀.mem := by
    obtain f₁ : Frame [⟨State.addr (s.gpr .r3), 256⟩] s.mem s₁.mem :=
      (Spill.saveMem_frame s.mem _ s.gpr (L := 36) (by decide) saved (by decide)).sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    rw [um]
    exact (f₁.writeW List.mem_cons_self _ (Offset.contains_base _ (d := 36) (n := 4) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (d := 40) (n := 4) (by decide) (by decide))
  obtain I0 : EInv s up 0 u₀ := by
    refine ⟨Nat.zero_le _, by rw [uk.gpr (by decide)], by rw [uk.gpr (by decide)], ?_, ?_, ?_, fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b _ hb => blockAt_frame F0 fun r hr => ?_, F0.mono fun r hr => ?_, uk.2.1, uk.2.2.1⟩
    · rw [um, Mem.readW_writeW_sep s36 (by decide), Mem.readW_writeW_self32, Nat.mul_zero]; simp
    · rw [um, Mem.readW_writeW_self32, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have sv := Spill.saveMem_saved (State.addr (s.gpr .r3)) s.gpr s.mem saved saved_slots
      refine sv.frame saved_slots (rs := [⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 36, 8⟩]) ?_ fun r hr => ?_
      · rw [um]
        exact ((Frame.refl _ _).writeW List.mem_cons_self _
          (Offset.contains (e := 36) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide))).writeW
          List.mem_cons_self _ (Offset.contains (e := 36) (k := 8) (d := 40) (n := 4) _ (by decide) (by decide) (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact Offset.disjoint _ (by decide) (by decide) (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact (db.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the end
  obtain fin : ∀ u, EInv s up (s.gpr .r2).toNat u → WP isa (.block restore) u (EcbPost s up) := fun u I => by
    refine WP.mono (restore_run (u := u) (by rw [I.r3]; omega_arith) (fun d hd => ?_) (by rw [I.r3]; exact I.saved))
      fun t ⟨tr, tm⟩ =>
      ⟨tr, ecb_blocks _ _ _ _ _ _ fun b hb => by rw [tm]; exact I.done b hb⟩
    rw [I.rd, I.wr, hrd, hwr, I.r3]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.ite (s.gpr .r2 - 0#32 == 0#32) (by rw [eval_eq, uz]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .r2).toNat = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz); simpa using this
    exact WP.block_nil (fin u₀ (by rw [hn]; exact I0))
  · have hn : 0 < (s.gpr .r2).toNat := by
      obtain h0 : s.gpr .r2 ≠ 0#32 := by intro e; rw [e] at hz; simp at hz
      have : (s.gpr .r2).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
      omega_arith
    refine WP.mono (WP.loop (M := isa) (Q := EInv s up (s.gpr .r2).toNat)
      (fun (m : Nat) (u : State) => ∃ k, k < (s.gpr .r2).toNat ∧ m = (s.gpr .r2).toNat - k ∧ EInv s up k u)
      ?_ _ u₀ ⟨0, hn, rfl, I0⟩) fin
    intro m u ⟨k, hk, hm, I⟩
    refine WP.mono (ecb_step h up hk I) fun u' ⟨I', zu⟩ => ?_
    rw [eval_ne, zu]
    by_cases e : k + 1 = (s.gpr .r2).toNat
    · left
      exact ⟨by rw [e, Nat.sub_self]; rfl, e ▸ I'⟩
    · right
      obtain nz : BitVec.ofNat 32 ((s.gpr .r2).toNat - (k + 1)) ≠ 0#32 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
      exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, k + 1, by omega_arith, rfl, I'⟩

end VG.Proof.Blowfish.Arm
