module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Run
public import VerifiedGarbage.Proof.Blowfish.Scan32
public import VerifiedGarbage.Proof.Blowfish.F
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# Blowfish on PPC64LE: an S-box lookup

`lookup_run`: `lookup j` leaves S-box `j`'s entry for the byte `3 - j` of
xL's low word in the accumulator's low word, changing only the lookup's
registers.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-- What a lookup needs: the schedule at `r3` readable and zero in `r0`. -/
structure LookEnv (s : State) : Prop where
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 o) 4
  zero : s.gpr .r0 = 0#64

/-- The registers a lookup writes. -/
def lookRegs : List Reg := [.r9, .r10, .r11, .r12, .r14, .r15]

theorem LookEnv.keep {s t : State} (E : LookEnv s) {rs : List Reg} (h : Keep rs s t)
    (h3 : Reg.r3 ∉ rs) (h0 : Reg.r0 ∉ rs) : LookEnv t := by
  refine ⟨fun o ho => ?_, by rw [h.gpr h0]; exact E.zero⟩
  rw [h.gpr h3, h.2.1, h.2.2]; exact E.rd o ho

/-! ## The index -/

theorem index_val (x : BitVec 64) {j : Nat} (hj : j < 4) :
    (x <<< (32 + 8 * j)) >>> 56 = (quarter (lo x) j).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.true_and, show 56 + i < 64 by omega,
      show ¬ (56 + i < 32 + 8 * j) by omega, decide_false, Bool.not_false,
      show 8 * (3 - j) + i < 32 by omega]
    rw [decide_eq_true hi, Bool.true_and]
    congr 1; omega
  · simp only [h8, decide_false, Bool.false_and]
    by_cases h : 56 + i < 64
    · omega
    · simp [h]

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .r9 = (quarter (lo (s.gpr .r4)) j).setWidth 64 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  unfold index
  brun [show 32 + 8 * j < 64 by omega]

/-! ## Rotations selected by a bit of the index -/

theorem condRot_run (s : State) (x : Reg) {c a : Nat} (hc : c < 64) (ha : a < 32)
    (h0 : s.gpr .r0 = 0#64) (x0 : x ≠ .r0) (x9 : x ≠ .r9) (x11 : x ≠ .r11) (x12 : x ≠ .r12) :
    WP isa (.block (condRot x c a)) s fun t =>
      t.gpr x = (if (s.gpr .r9).getLsbD c then ((lo (s.gpr x)).rotateRight a).setWidth 64 else s.gpr x) ∧
        t.mem = s.mem := by
  have hx9 : Reg.r9 ≠ x := Ne.symm x9
  have hx11 : Reg.r11 ≠ x := Ne.symm x11
  have hx12 : Reg.r12 ≠ x := Ne.symm x12
  have hx0 : Reg.r0 ≠ x := Ne.symm x0
  unfold condRot bitMask
  brun [h0, x0, x9, x11, x12, hx0, hx9, hx11, hx12, ha, show 63 - c < 64 by omega]
  rw [bitMask_eq _ hc, select_eq]

/-- The low two bits of `q`, by `q`'s residue mod 4. -/
theorem bit01 (q : BitVec 64) :
    q.getLsbD 0 = decide (q.toNat % 4 % 2 = 1) ∧ q.getLsbD 1 = decide (q.toNat % 4 / 2 = 1) := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, Nat.testBit_succ]
  constructor <;> congr 1 <;> apply propext <;> omega

theorem lo_ite {b : Bool} (x y : BitVec 64) : lo (if b then x else y) = if b then lo x else lo y := by
  cases b <;> rfl

/-- The lane mask, the accumulator and the row pointer. -/
theorem start_run (s : State) (h0 : s.gpr .r0 = 0#64) {L : Nat} (hL : (s.gpr .r9).toNat % 4 = L) :
    WP isa (.block lookupStart) s fun t =>
      lo (t.gpr .r14) = laneMask L ∧ t.gpr .r10 = 0#64 ∧ t.gpr .r15 = s.gpr .r3 ∧ t.mem = s.mem := by
  have hl : L < 4 := by omega
  obtain ⟨b0, b1⟩ := bit01 (s.gpr .r9)
  rw [hL] at b0 b1
  unfold lookupStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have hA : WP isa (.block [.li lane 255]) s fun t =>
      t.gpr .r14 = (BitVec.ofNat 32 255).setWidth 64 ∧ t.mem = s.mem := by brun; rfl
  refine WP.mono (WP.keep [.r14] hA (by decide) rfl) fun t₀ ⟨⟨t14, tm⟩, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r12, .r14] (condRot_run t₀ .r14 (c := 0) (a := 24) (by decide) (by decide)
    (by rw [tk.gpr (by decide), h0]) (by decide) (by decide) (by decide) (by decide))
    (by decide) rfl) fun t₁ ⟨⟨u14, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r12, .r14] (condRot_run t₁ .r14 (c := 1) (a := 16) (by decide) (by decide)
    (by rw [uk.gpr (by decide), tk.gpr (by decide), h0]) (by decide) (by decide) (by decide) (by decide))
    (by decide) rfl) fun t₂ ⟨⟨v14, vm⟩, vk⟩ => ?_
  have q1 : t₀.gpr .r9 = s.gpr .r9 := tk.gpr (by decide)
  have q2 : t₁.gpr .r9 = s.gpr .r9 := (uk.gpr (by decide)).trans q1
  have z3 : t₂.gpr .r3 = s.gpr .r3 := by rw [vk.gpr (by decide), uk.gpr (by decide), tk.gpr (by decide)]
  have e14 : lo (t₂.gpr .r14) = laneMask L := by
    rw [v14, u14, q2, q1, t14, b0, b1, ← laneMask_rot hl]
    simp only [lo_ite, lo_ext]
  have em : t₂.mem = s.mem := by rw [vm, um, tm]
  brun [z3, em, BitVec.or_self]
  exact e14


/-! ## The rows -/

theorem ite_ones_and (c : Prop) [Decidable c] (y : BitVec 64) :
    (if c then BitVec.allOnes 64 else 0) &&& y = if c then y else 0 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, BitVec.allOnes_and]
  · simp [h]

theorem lo_ite' (c : Prop) [Decidable c] (x y : BitVec 64) :
    lo (if c then x else y) = if c then lo x else lo y := by
  by_cases h : c <;> simp [h]

theorem lo_zero : lo 0#64 = 0#32 := rfl

theorem row_run (u : State) {j : Nat} (hj : j < 4) {q rp S : BitVec 64} {acc lm : BitVec 32}
    (h9 : u.gpr .r9 = q) (h10 : lo (u.gpr .r10) = acc) (h14 : lo (u.gpr .r14) = lm)
    (h15 : u.gpr .r15 = rp) (h3 : u.gpr .r3 = S) (h0 : u.gpr .r0 = 0#64)
    (hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (rp + BitVec.ofNat 64 (planeOff j b)) 4) :
    WP isa (.block (row j)) u fun t =>
      let M := if (q >>> 2).toNat = 0 then lm else 0
      let w := fun b => u.mem.readW (rp + BitVec.ofNat 64 (planeOff j b)) 32 &&& M
      lo (t.gpr .r10) = (((acc ||| w 0) ||| (w 1).rotateRight 24) ||| (w 2).rotateRight 16) |||
        (w 3).rotateRight 8 ∧
      t.gpr .r9 = q - 4#64 ∧ t.gpr .r15 = rp + 4#64 ∧ t.gpr .r12 = rp + 4#64 - S - 256#64 ∧
      t.mem = u.mem := by
  have o : ∀ b < 4, planeOff j b < 2 ^ 15 := fun b hb => by unfold planeOff; omega
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  have o0 := o 0 (by decide)
  have o1 := o 1 (by decide)
  have o2 := o 2 (by decide)
  have o3 := o 3 (by decide)
  have hq : (q >>> 2).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := q.isLt; omega
  unfold row rowMask plane
  brun [h9, h15, h3, h0, r0, r1, r2, r3, o0, o1, o2, o3]
  rw [isZero_eq _ hq]
  simp only [lo_or, lo_and, lo_ext, lo_ite', ite_ones_and, h10, h14]
  rfl

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

/-- `a - c` (as doublewords, both below `2 ^ 64`) is nonzero iff `a ≠ c`. -/
theorem ofNat_sub_bne {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != 0#64) = !decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega
    simp [this, h]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0#64) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega
    simp [this, h]

/-- `(q - 4k) >> 2` is zero iff row `k` holds the index. -/
theorem row_hit (x : Byte) {k : Nat} (hk : k < 64) :
    ((x.setWidth 64 - BitVec.ofNat 64 (4 * k)) >>> 2).toNat = 0 ↔ x.toNat / 4 = k := by
  have := x.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 4 * k < 2 ^ 64 by omega),
    Nat.shiftRight_eq_div_pow]
  omega

/-- After `k` rows of S-box `j` for the index `idx`, from the lookup's start
`s₀`. -/
structure RowInv (s₀ : State) (j : Nat) (idx : Byte) (k : Nat) (u : State) : Prop where
  q : u.gpr .r9 = idx.setWidth 64 - BitVec.ofNat 64 (4 * k)
  acc : lo (u.gpr .r10) = scanAcc s₀.mem (s₀.gpr .r3) j idx.toNat k
  lane : lo (u.gpr .r14) = laneMask (idx.toNat % 4)
  rp : u.gpr .r15 = s₀.gpr .r3 + BitVec.ofNat 64 (4 * k)
  keep : Keep lookRegs s₀ u
  mem : u.mem = s₀.mem

theorem row_step {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {k : Nat}
    (hk : k < 64) {u : State} (I : RowInv s₀ j idx k u) :
    WP isa (.block (row j)) u fun u' =>
      RowInv s₀ j idx (k + 1) u' ∧ u'.gpr .r12 = BitVec.ofNat 64 (4 * (k + 1)) - BitVec.ofNat 64 256 := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have ha : ∀ b < 4, s₀.gpr .r3 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (planeOff j b) =
      s₀.gpr .r3 + BitVec.ofNat 64 (1024 * j + 256 * b + 4 * k) := fun b _ =>
    Offset.add_add_eq _ (by unfold planeOff; omega)
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr)
      (s₀.gpr .r3 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (planeOff j b)) 4 :=
    fun b hb => by rw [ha b hb, hrd]; exact E.rd _ (by omega)
  have h3 : u.gpr .r3 = s₀.gpr .r3 := I.keep.gpr (by decide)
  have h0 : u.gpr .r0 = 0#64 := by rw [I.keep.gpr (by decide)]; exact E.zero
  refine WP.mono (WP.keep [.r9, .r10, .r11, .r12, .r15]
    (row_run u hj I.q I.acc I.lane I.rp h3 h0 hr) (by
      simp [writesOnly, Code.allInstrs_eq, instrs, row, rowMask, plane, dstOf, mReg, qReg, tmp, acc,
        rowPtr]) rfl) fun u' ⟨⟨a10, a9, a15, a12, am⟩, ak⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, I.keep.trans ak |>.mono (by decide), am.trans I.mem⟩, ?_⟩
  · rw [a9, BitVec.sub_sub, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]
    congr 2
  · dsimp only at a10
    rw [a10, I.mem]
    simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]
    refine scanAcc_succ _ _ _ _ _ _ ?_
    by_cases e : idx.toNat / 4 = k
    · rw [ite_eq_left ((row_hit idx hk).mpr e), ite_eq_left e]
    · rw [ite_eq_right (fun h => e ((row_hit idx hk).mp h)), ite_eq_right e]
  · rw [ak.gpr (by decide), I.lane]
  · rw [a15, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
    congr 2
  · rw [a12, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
      Offset.add_sub_cancel_left]
    congr 2

theorem rows_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {u : State}
    (I : RowInv s₀ j idx 0 u) : WP isa (.loop (.block (row j)) (.nonzero .d .r12)) u (RowInv s₀ j idx 64) := by
  refine WP.loop (M := isa) (Q := RowInv s₀ j idx 64)
    (fun (n : Nat) (v : State) => ∃ k, k < 64 ∧ n = 64 - k ∧ RowInv s₀ j idx k v) ?_ 64 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨k, hk, hn, J⟩
  refine WP.mono (row_step E hj idx hk J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_nonzero, hz, ofNat_sub_bne (by omega) (by decide)]
  by_cases e : k + 1 = 64
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by simp; omega, n - 1, by omega, k + 1, by omega, by omega, J'⟩

/-- The lookup of S-box `j` for the byte `3 - j` of xL's low word. -/
theorem lookup_run {s : State} (E : LookEnv s) {j : Nat} (hj : j < 4) :
    WP isa (lookup j) s fun t =>
      lo (t.gpr .r10) = sEntry (scheduleAt s.mem (s.gpr .r3)) j (quarter (lo (s.gpr .r4)) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .r4)) j
  unfold lookup
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r9] (index_run s hj) (by simp [writesOnly, Code.allInstrs_eq, instrs, index,
    dstOf, qReg]) rfl) fun t ⟨⟨t9, tm⟩, tk⟩ => ?_
  have hL : (t.gpr .r9).toNat % 4 = idx.toNat % 4 := by rw [t9, BitVec.toNat_setWidth]; simp [idx]
  refine WP.mono (WP.keep [.r10, .r11, .r12, .r14, .r15]
    (start_run t (by rw [tk.gpr (by decide)]; exact E.zero) hL) (by decide) rfl)
    fun u ⟨⟨u14, u10, u15, um⟩, uk⟩ => ?_
  have K0 : Keep lookRegs s u := (tk.trans uk).mono (by decide)
  have I0 : RowInv s j idx 0 u := by
    refine ⟨?_, by rw [u10, scanAcc_zero]; rfl, u14, ?_, K0, by rw [um]; exact tm⟩
    · rw [uk.gpr (by decide), t9]; simp [idx]
    · rw [u15, tk.gpr (by decide)]; simp
  apply WP.seq
  refine WP.mono (rows_run E hj idx I0) fun v V => ?_
  have v0 : v.gpr .r0 = 0#64 := by rw [V.keep.gpr (by decide)]; exact E.zero
  unfold lookupEnd
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r10, .r11, .r12] (condRot_run v .r10 (c := 0) (a := 8) (by decide) (by decide)
    v0 (by decide) (by decide) (by decide) (by decide)) (by decide) rfl) fun w ⟨⟨w10, wm⟩, wk⟩ => ?_
  refine WP.mono (WP.keep [.r10, .r11, .r12] (condRot_run w .r10 (c := 1) (a := 16) (by decide) (by decide)
    (by rw [wk.gpr (by decide), v0]) (by decide) (by decide) (by decide) (by decide)) (by decide) rfl)
    fun x ⟨⟨x10, xm⟩, xk⟩ => ?_
  have hL4 : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨b0, b1⟩ := bit01 (v.gpr .r9)
  have hq : (v.gpr .r9).toNat % 4 = idx.toNat % 4 := by
    rw [V.q, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := idx.isLt
    rw [Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega)]
    omega
  rw [hq] at b0 b1
  refine ⟨?_, (V.keep.trans wk).trans xk |>.mono (by decide), by rw [xm, wm, V.mem]⟩
  rw [x10, wk.gpr (by decide), w10, b0, b1]
  simp only [lo_ite, lo_ext]
  rw [acc_rot _ hL4, V.acc, scanAcc_all]
  exact hitWord_ror _ _ hj idx

end VG.Proof.Blowfish.PPC64LE
