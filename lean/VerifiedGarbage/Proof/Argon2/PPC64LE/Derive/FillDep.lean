module

import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Initial
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! ### `Argon2.PPC64LE.Derive.FillState`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.Derive.FillSteps`, which this module and modules that import it used -/

section

/-!
# Argon2 on PPC64LE: the steps of the filling loops

The address computations the filling loops share: `column_ok` (the current
column), `blockAddr_ok` (a block's address from its lane and column) and
`prevPointer_ok` (the previous block's). Register-only steps are described
by `Only` (the registers they may write), which keeps the body's invariant
when the invariant names none of them (`Inv.only`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_add wp_sub wp_subi wp_lsl)
open VG.Impl.Argon2.PPC64LE.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff ld)

theorem Inv.only {s₀ s t : State} (h : Inv s₀ s) {ds : List Reg} (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : Inv s₀ t :=
  h.step o.sp (o.gpr _ fun m => (hd _ m).1 rfl) (o.gpr _ fun m => (hd _ m).2.1 rfl)
    (fun r hr => o.gpr _ fun m => (hd _ m).2.2 hr) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)

theorem Divide.KeepD.only {s t : State} (k : Divide.KeepD s t) : Only [.r4, .r6, .r7, .r8, .r9] s t :=
  ⟨fun r hr => k.other r (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
    (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h])),
    k.mem, k.rd, k.wr, k.sp⟩

theorem ofNat_mul_ofNat {a b : Nat} : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) :=
  (BitVec.ofNat_mul ..).symm

/-- `ofNat x << n`, without overflow. -/
theorem ofNat_shl' {x n : Nat} (h : x * 2 ^ n < 2 ^ 64) :
    BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x * 2 ^ n) := by
  have hx : x < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right x (Nat.two_pow_pos n)) h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx]

/-! ## Addresses -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem laneLen_ge : 8 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_using [this]

theorem laneLen_le : (prm s₀).laneLen ≤ blocksN s₀ := by
  rw [hp.blocks_eq]; exact Nat.le_mul_of_pos_left _ hp.lanes_pos

theorem blocks_lt' : blocksN s₀ < 2 ^ 32 := Nat.lt_of_le_of_lt hp.blocks_le (mcost_lt s₀)

/-- A cell of the matrix, and its bytes, fit in the matrix. -/
theorem cell_fits {lane col : Nat} (hl : lane < lanesN s₀) (hc : col < (prm s₀).laneLen) :
    lane * (prm s₀).laneLen + col < blocksN s₀ ∧
      (lane * (prm s₀).laneLen + col) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by
  have : lane * (prm s₀).laneLen + col < blocksN s₀ := by
    have e := hp.blocks_eq
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show lane + 1 ≤ lanesN s₀ by omega_using [hl])
    rw [Nat.succ_mul] at this
    omega_using [hc, e, this]
  have h2 : (lane * (prm s₀).laneLen + col + 1) * 1024 ≤ blocksN s₀ * 1024 :=
    Nat.mul_le_mul_right 1024 this
  rw [Nat.succ_mul] at h2
  exact ⟨this, h2⟩

/-- `blockAddr`: `r3 :=` the address of block `col` of lane `lane`. -/
theorem blockAddr_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {lane col : Nat}
    (hl : lane < lanesN s₀) (hc : col < (prm s₀).laneLen) (ha : s.gpr .r3 = BitVec.ofNat 64 lane)
    (hcx : s.gpr .r4 = BitVec.ofNat 64 col) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r3 = memP s₀ + BitVec.ofNat 64 ((lane * (prm s₀).laneLen + col) * 1024) →
      Only [.r3, .r5] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.blockAddr ++ is)) s Q := by
  obtain ⟨cl, cf⟩ := cell_fits hp hl hc
  have hb := blocks_lt' hp
  unfold Impl.Argon2.PPC64LE.Derive.blockAddr
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h (d := laneLenOff) (by decide) fun s₁ u₁ => wp_mul fun s₂ u₂ =>
    wp_add fun s₃ u₃ => wp_lsl (by decide) fun s₄ u₄ => ?_
  have i₄ := (((h.upd u₁).upd u₂).upd u₃).upd u₄
  have e₄ : s₄.gpr .r3 = BitVec.ofNat 64 ((lane * (prm s₀).laneLen + col) * 1024) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other .r4 (by decide), u₁.gpr, u₁.other .r3 (by decide),
      u₁.other .r4 (by decide), ha, hcx, pr.laneLen, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat,
      ofNat_shl' (by omega_using [cl, hb])]
  refine wp_lda hp i₄ (i := 13) (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ => k s₆ ?_ ?_
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), e₄]
  · exact (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆) |>.mono (by simp)

end

/-- The loop position in the frame. -/
structure Pos (s₀ s : State) (pass slice lane index : Nat) : Prop where
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 64 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 64 lane
  index : lw s₀ s indexOff = BitVec.ofNat 64 index

theorem Pos.of_mem {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hm : t.mem = s.mem) : Pos s₀ t pass slice lane index :=
  ⟨by rw [lw_mem hm]; exact h.pass, by rw [lw_mem hm]; exact h.slice, by rw [lw_mem hm]; exact h.lane,
    by rw [lw_mem hm]; exact h.index⟩

theorem Pos.of_lw {s₀ s t : State} {pass slice lane index : Nat} (h : Pos s₀ s pass slice lane index)
    (hl : ∀ d, 208 ≤ d → d + 8 ≤ 240 → lw s₀ t d = lw s₀ s d) :
    Pos s₀ t pass slice lane index :=
  ⟨by rw [hl _ (by decide) (by decide)]; exact h.pass, by rw [hl _ (by decide) (by decide)]; exact h.slice,
    by rw [hl _ (by decide) (by decide)]; exact h.lane, by rw [hl _ (by decide) (by decide)]; exact h.index⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem segLen_lt : (prm s₀).segmentLen < 2 ^ 30 := by
  have := laneLen_ge hp
  have := laneLen_le hp
  have := blocks_lt' hp
  have l := hp.laneLen_eq
  omega

omit hp in
/-- `column`: `r4 :=` the current column, `slice · segLen + index`. -/
theorem column_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r4 = BitVec.ofNat 64 (slice * (prm s₀).segmentLen + index) →
      Only [.r3, .r4, .r5] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.column ++ is)) s Q := by
  unfold Impl.Argon2.PPC64LE.Derive.column
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h (d := sliceOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine wp_ldloc i₁ (d := segLenOff) (by decide) fun s₂ u₂ => wp_mul fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂).upd u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldloc i₃ (d := indexOff) (by decide) fun s₄ u₄ => wp_add fun t u => k t ?_ ?_
  · rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem,
      ps.slice, pr.segLen, u₄.gpr, lw_mem m₃, ps.index, ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  · exact ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).trans (Only.of_upd u) |>.mono (by simp)

/-- `prevColumn`: `r4 :=` the column before `r4`, cyclically. -/
theorem prevColumn_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {col : Nat}
    (hc : col < (prm s₀).laneLen) (hx : s.gpr .r4 = BitVec.ofNat 64 col) :
    WP isa Impl.Argon2.PPC64LE.Derive.prevColumn s fun t =>
      t.gpr .r4 = BitVec.ofNat 64 ((col + (prm s₀).laneLen - 1) % (prm s₀).laneLen) ∧
        Only [.r4] s t := by
  have := laneLen_ge hp
  have := laneLen_le hp
  have := blocks_lt' hp
  unfold Impl.Argon2.PPC64LE.Derive.prevColumn
  refine WP.seq (WP.ite (decide (col = 0)) ?_ ?_ ?_)
  · rw [show isa.eval _ s = VG.PPC64LE.eval _ s from rfl, MdStream.PPC64LE.eval_zero, hx,
      MdStream.PPC64LE.ofNat_beq_zero (by omega_arith)]
  · intro hz
    refine wp_ldloc h (d := laneLenOff) (by decide) fun s₂ u₂ => WP.block_nil ?_
    refine wp_subi (by decide) fun t u => WP.block_nil ⟨?_, ?_⟩
    · have c0 : col = 0 := of_decide_eq_true hz
      rw [u.gpr, u₂.gpr, pr.laneLen, c0, MdStream.PPC64LE.sub_ofNat (by omega_using [hc]), Nat.zero_add,
        Nat.mod_eq_of_lt (by omega_using [hc])]
    · exact ((Only.of_upd u₂).trans (Only.of_upd u)).mono (by simp)
  · intro hz
    refine WP.block_nil (wp_subi (by decide) fun t u => WP.block_nil ⟨?_, ?_⟩)
    · have c0 : col ≠ 0 := of_decide_eq_false hz
      rw [u.gpr, hx, MdStream.PPC64LE.sub_ofNat (by omega_using [c0])]
      congr 1
      rw [show col + (prm s₀).laneLen - 1 = col - 1 + (prm s₀).laneLen by omega_using [c0], Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_using [hc])]
    · exact (Only.of_upd u).mono (by simp)

/-- `prevPointer`: `r3 :=` the address of the previous block. -/
theorem prevPointer_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.PPC64LE.Derive.prevPointer s fun t =>
      t.gpr .r3 = memP s₀ + BitVec.ofNat 64 ((lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen) * 1024) ∧
      Only [.r3, .r4, .r5] s t := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  have := laneLen_ge hp
  unfold Impl.Argon2.PPC64LE.Derive.prevPointer
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.PPC64LE.Derive.column]
  refine column_ok h pr ps fun s₁ c₁ k₁ => WP.block_nil ?_
  have i₁ := h.only k₁
  refine WP.seq ((prevColumn_ok hp i₁ (pr.of_mem k₁.mem) hc c₁).mono fun s₂ ⟨c₂, k₂⟩ => ?_)
  have i₂ := i₁.only k₂
  have m₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine wp_ldloc i₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  rw [← List.append_nil Impl.Argon2.PPC64LE.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (pr.of_mem (by rw [u₃.mem, m₂])) hl (Nat.mod_lt _ (by omega_using [hc]))
    (by rw [u₃.gpr, lw_mem m₂, ps.lane]) (by rw [u₃.other _ (by decide), c₂])
    fun t a k => WP.block_nil ⟨a, ?_⟩
  exact (((k₁.trans k₂).trans (Only.of_upd u₃)).trans k).mono (by simp)

end

end VG.Proof.Argon2.PPC64LE.Derive

end

end

/-!
# Argon2 on PPC64LE: the state of the filling loops

`FS s₀ pass slice lane index ctr st`: the body at a position of the filling
loops (`Pos`), the memory matrix representing `st`'s, and the address block
cached in `scratch[6144, 7168)` that of the counter in the frame, if it is
not zero (`CacheOk`). `addressMode_ok`: `addressMode` leaves `r8` nonzero
for data-dependent addressing.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li wp_sub wp_lsr wp_and)
open VG.Spec.Argon2 (Block zeroBlock FillState addressBlock independent)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.PPC64LE.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff counterOff)

/-- The address block cached at `scratch + 6144`, for the counter in the frame. -/
def CacheOk (s₀ : State) (pass lane slice ctr : Nat) (s : State) : Prop :=
  ctr < 2 ^ 32 ∧ lw s₀ s counterOff = BitVec.ofNat 64 ctr ∧
    (ctr = 0 ∨ 1 ≤ ctr ∧
      blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144) = addressBlock (prm s₀) pass lane slice ctr)

/-- The counter after a block: the index's group, for data-independent addressing. -/
def ctrNext (p : Spec.Argon2.Params) (pass slice index ctr : Nat) : Nat :=
  if independent p pass slice then index / 128 + 1 else ctr

/-- The filling loops' state at a position, the memory matrix holding `st`'s. -/
structure FS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  cache : CacheOk s₀ pass lane slice ctr s
  mem : Represents s.mem (memP s₀) (prm s₀).blocks st.memory

theorem Represents.keep {m m' : Mem} {base : Addr} {n : Nat} {b : Array Block}
    (h : Represents m base n b)
    (hk : ∀ k < n, blockAt m' (matrixCell base k) = blockAt m (matrixCell base k)) :
    Represents m' base n b :=
  ⟨h.size, fun k hk' => (hk k hk').trans (h.block k hk')⟩

/-! ## The addressing mode -/

theorem independent_eq {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) (pass slice : Nat) :
    independent (prm s₀) pass slice = (decide ((kindV s₀).toNat = 1) ||
      (decide ((kindV s₀).toNat = 2) && decide (pass = 0) && decide (slice < 2))) := by
  have hv : (prm s₀).variant =
      (if (kindV s₀).toNat = 0 then .d else if (kindV s₀).toNat = 1 then .i else .id) := rfl
  have e1 : (Spec.Argon2.Variant.d == .i) = false := rfl
  have e2 : (Spec.Argon2.Variant.d == .id) = false := rfl
  have e3 : (Spec.Argon2.Variant.i == .i) = true := rfl
  have e3' : (Spec.Argon2.Variant.i == .id) = false := rfl
  have e4 : (Spec.Argon2.Variant.id == .i) = false := rfl
  have e5 : (Spec.Argon2.Variant.id == .id) = true := rfl
  rcases (by omega_using [hk] : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with
    h | h | h
  · rw [independent, hv, ite_eq_left h, e1, e2, h]; simp
  · rw [independent, hv, ite_eq_right (by omega_using [h]), ite_eq_left h, e3, e3', h]; simp
  · rw [independent, hv, ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]), e4, e5, h]; simp
    cases pass <;> rfl

/-- `((0 - x) | x) >> 63` is whether `x` is not zero. -/
theorem nz (x : BitVec 64) : ((0 - x) ||| x) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx; decide
  · simp only [hx, ite_false]
    have hn : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq h)
    have hm : ∀ y : BitVec 64, y.msb = decide (2 ^ 63 ≤ y.toNat) := fun y => by
      rw [BitVec.msb_eq_decide]
    have hb : 2 ^ 63 ≤ ((0 - x) ||| x).toNat := by
      have : ((0 - x) ||| x).msb = true := by
        rw [BitVec.msb_or, hm, hm, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
        have := x.isLt
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega_using [hn]
      rw [hm] at this; exact of_decide_eq_true this
    have hl := ((0 - x) ||| x).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 1
    omega_using [hb]

/-- The second test of `addressMode`: Argon2id in the first two slices of the first pass. -/
theorem id_zero {k : Nat} (hk : k ≤ 2) {pass slice : Nat} (hp : pass < 2 ^ 64) (hs : slice < 4) :
    ((BitVec.ofNat 64 k ^^^ BitVec.ofNat 64 2) ||| BitVec.ofNat 64 pass ||| (BitVec.ofNat 64 slice >>> 1) = 0) ↔
      (k = 2 ∧ pass = 0 ∧ slice < 2) := by
  have e : BitVec.ofNat 64 slice >>> 1 = 0 ↔ slice < 2 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hs])] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega_using [this]
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hs])]
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega_using [h]
  have f : BitVec.ofNat 64 k ^^^ BitVec.ofNat 64 2 = 0 ↔ k = 2 := by
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h <;> subst h <;> decide
  have pp : BitVec.ofNat 64 pass = 0 ↔ pass = 0 := by
    constructor
    · intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] at this; exact this
    · intro e; rw [e]; rfl
  have orz : ∀ x y : BitVec 64, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
  rw [orz, orz, f, e, pp, and_assoc]

theorem mode_bits (a b : Prop) [Decidable a] [Decidable b] :
    (((if a then (0 : BitVec 64) else 1) &&& (if b then 0 else 1)) != 0) = !(decide a || decide b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- `nonzero d n t`: `d :=` whether `n` is not zero. -/
theorem nonzero_ok {s : State} {d n t : Reg} (hnt : n ≠ t) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, u.gpr d = (if s.gpr n = 0 then 0 else 1) → Only [t, d] s u → WP isa (.block is) u Q) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.nonzero d n t ++ is)) s Q := by
  simp only [Impl.Argon2.PPC64LE.Derive.nonzero, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_or fun s₃ u₃ =>
    wp_lsr (by decide) fun u u₄ => k u ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other n hnt, u₁.gpr, u₁.other n hnt,
      show BitVec.ofNat 64 0 = 0 from rfl, nz]
  · exact (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
      |>.mono (by simp)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addressMode`: `r8` is nonzero for data-dependent addressing. -/
theorem addressMode_ok {s : State} (h : Inv s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.PPC64LE.Derive.addressMode) s fun t =>
      VG.PPC64LE.eval (.nonzero .d .r8) t = some (!independent (prm s₀) pass slice) ∧
        Only [.r3, .r4, .r5, .r6, .r7, .r8] s t := by
  have hk := hp.kind_le
  have K : (arg32 s₀ 0).setWidth 64 = BitVec.ofNat 64 (kindV s₀).toNat := ofNat_toNat (toNat_ext32 _)
  unfold Impl.Argon2.PPC64LE.Derive.addressMode
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldw hp h (i := 0) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_xor fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_xor fun s₅ u₅ => ?_
  have o₅ := ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have i₅ := h.only o₅
  refine wp_ldloc i₅ (d := passOff) (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ => ?_
  have o₇ := (o₅.trans (Only.of_upd u₆)).trans (Only.of_upd u₇)
  have i₇ := h.only o₇
  refine wp_ldloc i₇ (d := sliceOff) (by decide) fun s₈ u₈ => wp_lsr (by decide) fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => ?_
  have o₁₀ := ((o₇.trans (Only.of_upd u₈)).trans (Only.of_upd u₉)).trans (Only.of_upd u₁₀)
  have v4 : s₁₀.gpr .r4 = BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, K]
  have v5 : s₁₀.gpr .r5 = (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 2) |||
      BitVec.ofNat 64 pass ||| (BitVec.ofNat 64 slice >>> 1) := by
    rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₈.other _ (by decide), u₇.gpr,
      u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, K, lw_mem o₇.mem, ps.slice,
      lw_mem o₅.mem, ps.pass]
  refine nonzero_ok (by decide) fun s₁₁ v₁₁ o₁₁ => nonzero_ok (by decide) fun s₁₂ v₁₂ o₁₂ =>
    wp_and fun t ut => WP.block_nil ⟨?_, ?_⟩
  · have r8 : t.gpr .r8 = (if BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 = 0 then 0 else 1) &&&
        (if (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 2) ||| BitVec.ofNat 64 pass |||
          (BitVec.ofNat 64 slice >>> 1) = 0 then 0 else 1) := by
      rw [ut.gpr, o₁₂.gpr _ (by decide), v₁₁, v4, v₁₂, o₁₁.gpr _ (by decide), v5]
    have k1 : (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 = 0) ↔ (kindV s₀).toNat = 1 := by
      rcases (by omega_using [hk] : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with
        e | e | e <;> rw [e] <;> decide
    rw [MdStream.PPC64LE.eval_nonzero, r8, mode_bits, independent_eq hk]
    simp only [k1, id_zero hk (by omega_using [hpass] : pass < 2 ^ 64) hs, Bool.decide_and, Bool.and_assoc]
  · exact (((o₁₀.trans o₁₁).trans o₁₂).trans (Only.of_upd ut)).mono (by simp)

end

end VG.Proof.Argon2.PPC64LE.Derive

end

end

/-!
# Argon2 on PPC64LE: the filling state, and data-dependent addressing

`FS.keep`: what keeps the filling state (`FS.of_only`, `FS.store`,
`FS.frame`). `dependentWord_ok`: J₁ and J₂, the halves of the previous
block's first doubleword, to the frame (`Rand`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_lwz)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.PPC64LE.Derive (j1Off j2Off)

/-- Doubleword `j` of a block. -/
theorem blockAt_get (m : Mem) (p : Addr) {j : Nat} (hj : j < 128) :
    (blockAt m p)[j] = m.readW (p + BitVec.ofNat 64 (8 * j)) 64 := by
  simp only [blockAt, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

/-- J₁ and J₂, the halves of the random word `w`, in the frame. -/
def Rand (s₀ s : State) (w : BitVec 64) : Prop :=
  lw s₀ s j1Off = w &&& 0xffffffff ∧ lw s₀ s j2Off = w >>> 32

theorem lo_ext (w : BitVec 64) : (w.setWidth 32).setWidth 64 = w &&& 0xffffffff := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt w.toNat (show 0 < 2 ^ 32 by decide)
  omega_using []

theorem hi_ext (w : BitVec 64) : (w.extractLsb' 32 32).setWidth 64 = w >>> 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h32 : w.toNat / 2 ^ 32 < 2 ^ 32 := by omega_using []
  rw [Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt (by omega_using [])]

theorem FS.keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t)
    (hl : ∀ d, 208 ≤ d → d + 8 ≤ 272 → lw s₀ t d = lw s₀ s d)
    (hc : blockAt t.mem (scrP s₀ + BitVec.ofNat 64 6144) = blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144))
    (hm : ∀ k < (prm s₀).blocks,
      blockAt t.mem (matrixCell (memP s₀) k) = blockAt s.mem (matrixCell (memP s₀) k)) :
    FS s₀ pass slice lane index ctr st t := by
  refine ⟨it, Prm.of_lw h.pr fun d h₁ h₂ => hl d (by omega_using [h₁]) (by omega_using [h₂]),
    h.pos.of_lw fun d h₁ h₂ => hl d (by omega_using [h₁]) (by omega_using [h₂]), ?_, Represents.keep h.mem hm⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [hl _ (by decide) (by decide)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [hl _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [hc]; exact c4⟩⟩

/-- A step that writes only registers the invariant does not name keeps the
filling state. -/
theorem FS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {ds : List Reg} (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.only o hd) (fun d _ _ => lw_mem o.mem d) (by rw [o.mem]) fun _ _ => by rw [o.mem]

/-- Regions a step of the filling loops may write without changing the filling state. -/
def Outside (s₀ : State) (r : Region) : Prop :=
  r.Disjoint ⟨at' s₀ 256, 64⟩ ∧ r.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 6144, 1024⟩ ∧ r.Disjoint (memR s₀)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem FS.frame {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {rs : List Region}
    (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, Outside s₀ r) : FS s₀ pass slice lane index ctr st t := by
  refine h.keep it (fun d h₁ h₂ => ?_) ?_ fun k hk => ?_
  · refine f.readW (r := ⟨E s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => (ho r hr).1.symm.sub_left ?_) (by decide)
    rw [E_add]; exact Offset.sub _ (by omega_using [h₁]) (by omega_using [h₂])
  · exact blockAt_keep f fun r hr => (ho r hr).2.1.symm
  · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact blockAt_keep f fun r hr => (ho r hr).2.2.symm.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk')

/-- A store to the frame outside the filling state's variables keeps the
filling state. -/
theorem FS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t) {d : Nat} (hd : 272 ≤ d)
    (hd' : d + 8 ≤ 336) {v : BitVec 64} (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) v) :
    FS s₀ pass slice lane index ctr st t := by
  refine h.frame hp it (rs := [⟨E s₀ + BitVec.ofNat 64 d, 8⟩]) (by rw [hm]; exact frame_loc v)
    fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  rw [E_add]
  refine ⟨Offset.disjoint _ (by omega_using [hd]) (by omega_using [hd']) (by omega_using []), ?_, ?_⟩
  · exact (stk_disj hp (by omega_using [hd']) (scrR s₀) (by simp)).sub_right (scr_sub (by decide))
  · exact stk_disj hp (by omega_using [hd']) (memR s₀) (by simp)

theorem outside_scr {o n : Nat} (h : o + n ≤ 6144 ∨ (7168 ≤ o ∧ o + n ≤ 16384)) :
    Outside s₀ ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ := by
  have sub : Region.Sub ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) := Offset.sub_base _ (by omega_using [h])
  refine ⟨((stk_disj hp (d := 256) (n := 64) (by decide) (scrR s₀) (by simp)).symm.sub_left sub),
    Offset.disjoint _ (by omega_using [h]) (by omega_using [h]) (by omega_using []), hp.mem_scr.symm.sub_left sub⟩

/-- `dependentWord`: J₁ and J₂ are the halves of the previous block's first doubleword. -/
theorem dependentWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.PPC64LE.Derive.dependentWord s fun t => FS s₀ pass slice lane index ctr st t ∧
      Rand s₀ t (blockAt s.mem (matrixCell (memP s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))[0] := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, cf⟩ := cell_fits hp hl
    (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)
    (Nat.mod_lt _ (by omega_using [L8]))
  unfold Impl.Argon2.PPC64LE.Derive.dependentWord
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = c at cl cf a₁ ⊢
  have h₁ := h.of_only k₁
  have hb := blocks_lt' hp
  have inP : ∀ o, o + 4 ≤ 1024 → (memR s₀).Contains (matrixCell (memP s₀) c + BitVec.ofNat 64 o) 4 :=
    fun o ho => by
      rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_using [cl, ho]) (by omega_using [cl, hb, ho])
  have mW : ∀ t, Inv s₀ t → memR s₀ ∈ t.wr := fun t it => by rw [it.wr]; exact mem_mem hp
  have hb := blocks_lt' hp
  have c0 : (memR s₀).Contains (matrixCell (memP s₀) c) 4 :=
    Offset.contains_base (memP s₀) (d := c * 1024) (n := 4) (k := blocksN s₀ * 1024)
      (Nat.le_trans (Nat.add_le_add_left (by decide) _) cf) (by omega_arith)
  refine wp_lwz (a := matrixCell (memP s₀) c) (by decide) (by rw [a₁]; simp [matrixCell])
    ⟨_, List.mem_append_right _ (mW _ h₁.inv), c0⟩ fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂)
  refine wp_stloc h₂.inv (d := j1Off) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := j1Off) (by decide) (by decide) m₃
  refine wp_lwz (a := matrixCell (memP s₀) c + BitVec.ofNat 64 4) (by decide)
    (by rw [g₃, u₂.other _ (by decide), a₁]; rfl)
    ⟨_, List.mem_append_right _ (mW _ h₃.inv), inP 4 (by decide)⟩ fun s₄ u₄ => ?_
  have h₄ := h₃.of_only (Only.of_upd u₄)
  refine wp_stloc h₄.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact h₄.store hp it (d := j2Off) (by decide) (by decide) mt
  · have w0 : s.mem.readW (matrixCell (memP s₀) c) 64 = (blockAt s.mem (matrixCell (memP s₀) c))[0] := by
      rw [blockAt_get _ _ (by decide)]; simp
    rw [ot j1Off (by decide) (by decide), lw_mem u₄.mem, v₃, u₂.gpr, k₁.mem, Mem.readW_lo32 w0, lo_ext]
  · have sub : Region.Sub ⟨matrixCell (memP s₀) c, 8⟩ (memR s₀) :=
      Offset.sub_base (memP s₀) (d := c * 1024) (n := 8) (k := blocksN s₀ * 1024)
        (Nat.le_trans (Nat.add_le_add_left (by decide) _) cf)
    have w0 : s₃.mem.readW (matrixCell (memP s₀) c) 64 = (blockAt s.mem (matrixCell (memP s₀) c))[0] := by
      rw [m₃, (frame_loc _).readW (r := ⟨matrixCell (memP s₀) c, 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (loc_disj hp (d := j1Off) (by decide) (by decide) (memR s₀) (by simp)).symm.sub_left sub)
        (by decide), u₂.mem, k₁.mem, blockAt_get _ _ (by decide)]
      simp
    rw [vt, u₄.gpr]
    exact (congrArg (BitVec.setWidth 64) (Mem.readW_hi32 w0)).trans (hi_ext _)

end

end VG.Proof.Argon2.PPC64LE.Derive
