import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillSteps
import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions

/-!
# Argon2 on ARMv7: the state of the filling loops

`FS s₀ pass slice lane index ctr st`: the body at a position of the filling
loops (`Pos`), the memory matrix representing `st`'s, and the address block
cached in `scratch[6144, 7168)` that of the counter in the locals, if it is
not zero (`CacheOk`). `addressMode_ok`: `addressMode` sets Z for
data-dependent addressing.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_sub wp_orr wp_and wp_cmp op2_imm op2_reg op2_lsr)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState addressBlock independent)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only rd64 A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- The address block cached at `scratch + 6144`, for the counter in the locals. -/
def CacheOk (s₀ : State) (pass lane slice ctr : Nat) (s : State) : Prop :=
  ctr < 2 ^ 32 ∧ lw s₀ s counterOff = BitVec.ofNat 32 ctr ∧
    (ctr = 0 ∨ 1 ≤ ctr ∧ blk s.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice ctr)

/-- The counter after a block: the index's group, for data-independent addressing. -/
def ctrNext (p : Spec.Argon2.Params) (pass slice index ctr : Nat) : Nat :=
  if independent p pass slice then index / 128 + 1 else ctr

/-- The filling loops' state at a position, the memory matrix holding `st`'s. -/
structure FS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  cache : CacheOk s₀ pass lane slice ctr s
  mem : Represents s.mem (memB s₀) (prm s₀).blocks st.memory

theorem Represents.keep {m m' : Mem} {base : Addr} {n : Nat} {b : Array Block}
    (h : Represents m base n b) (hk : ∀ k < n, blockAt m' (matrixCell base k) = blockAt m (matrixCell base k)) :
    Represents m' base n b :=
  ⟨h.size, fun k hk' => (hk k hk').trans (h.block k hk')⟩

/-- The block at `B + o`, from `B + o` as its base. -/
theorem blk_shift (m : Mem) (B : BitVec 32) (o : Nat) : blk m (B + BitVec.ofNat 32 o) 0 = blk m B o := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64, A, Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    Nat.add_assoc]

/-- The cells of the matrix, as `blk`. -/
theorem cell_blk {s₀ : State} (hp : DPre s₀) (m : Mem) {k : Nat} (hk : k < blocksN s₀) :
    blockAt m (matrixCell (memB s₀) k) = blk m (memP s₀) (k * 1024) := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  rw [← cell_addr hp hk, Proof.Argon2.Arm.blockAt_eq (by rw [add_nat (by omega)]; omega), blk_shift]

/-- Word `j` of a block. -/
theorem blk_get (m : Mem) (B : BitVec 32) (o j : Nat) (hj : j < 128) :
    (blk m B o)[j] = m.readW (A B (o + 8 * j + 4)) 32 ++ m.readW (A B (o + 8 * j)) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64]

/-- The first word of a block. -/
theorem blk_zero (m : Mem) (B : BitVec 32) (o : Nat) :
    (blk m B o)[0] = m.readW (A B (o + 4)) 32 ++ m.readW (A B o) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64, Nat.mul_zero, Nat.add_zero]

/-! ## The addressing mode -/

theorem independent_eq {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) (pass slice : Nat) :
    independent (prm s₀) pass slice = (decide ((kindV s₀).toNat = 1) ||
      (decide ((kindV s₀).toNat = 2) && decide (pass = 0) && decide (slice < 2))) := by
  have hv : (prm s₀).variant = (if (kindV s₀).toNat = 0 then .d else if (kindV s₀).toNat = 1 then .i else .id) :=
    rfl
  have e1 : (Spec.Argon2.Variant.d == .i) = false := rfl
  have e2 : (Spec.Argon2.Variant.d == .id) = false := rfl
  have e3 : (Spec.Argon2.Variant.i == .i) = true := rfl
  have e3' : (Spec.Argon2.Variant.i == .id) = false := rfl
  have e4 : (Spec.Argon2.Variant.id == .i) = false := rfl
  have e5 : (Spec.Argon2.Variant.id == .id) = true := rfl
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h
  · rw [independent, hv, ite_eq_left h, e1, e2, h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_left h, e3, e3', h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_right (by omega), e4, e5, h]; simp
    cases pass <;> rfl

/-- `((0 - x) | x) >> 31` is whether `x` is not zero. -/
theorem nz (x : BitVec 32) : ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx; decide
  · simp only [hx, ite_false]
    have hn : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq h)
    have hm : ∀ y : BitVec 32, y.msb = decide (2 ^ 31 ≤ y.toNat) := fun y => by rw [BitVec.msb_eq_decide]
    have hb : 2 ^ 31 ≤ ((0 - x) ||| x).toNat := by
      have : ((0 - x) ||| x).msb = true := by
        rw [BitVec.msb_or, hm, hm, BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]
        have := x.isLt
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
      rw [hm] at this; exact of_decide_eq_true this
    have hl := ((0 - x) ||| x).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 1
    omega

/-- The second test of `addressMode`: Argon2id in the first two slices of the first pass. -/
theorem id_zero {k p sl : BitVec 32} (hk : k.toNat ≤ 2) :
    ((k ^^^ (2 : BitVec 32)) ||| p ||| (sl >>> 1) = 0) ↔ (k.toNat = 2 ∧ p = 0 ∧ sl.toNat < 2) := by
  have e : sl >>> 1 = 0 ↔ sl.toNat < 2 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
      rw [show (0 : BitVec 32).toNat = 0 from rfl] at this
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [show (0 : BitVec 32).toNat = 0 from rfl]
      omega
  have f : k ^^^ (2 : BitVec 32) = 0 ↔ k.toNat = 2 := by
    rcases (by omega : k.toNat = 0 ∨ k.toNat = 1 ∨ k.toNat = 2) with h | h | h <;>
      · rw [show k = BitVec.ofNat 32 k.toNat by simp, h]; decide
  have orz : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
  rw [orz, orz, f, e, and_assoc]

theorem mode_bits (a b : Prop) [Decidable a] [Decidable b] :
    ((((if a then (0 : BitVec 32) else 1) &&& (if b then 0 else 1)) ^^^ 1) - 0 == 0) = !(decide a || decide b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addressMode`: Z for data-dependent addressing. -/
theorem addressMode_ok {s : State} (h : Inv s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.Arm.Derive.addressMode) s fun t =>
      VG.Arm.eval .eq t = some (!independent (prm s₀) pass slice) ∧ Only [.r0, .r1, .r2, .r3, .r12] s t := by
  have hk := hp.kind_le
  unfold Impl.Argon2.Arm.Derive.addressMode
  refine wp_ldarg hp h (i := 0) (by decide) fun s₁ u₁ => wp_eor (op2_imm (by decide)) fun s₂ u₂ =>
    wp_eor (op2_imm (by decide)) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have i₃ := h.only o₃ (by decide)
  refine wp_ldloc hp i₃ (d := passOff) (by decide) fun s₄ u₄ => wp_orr (op2_reg _ _) fun s₅ u₅ => ?_
  have o₅ := (o₃.trans (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have i₅ := h.only o₅ (by decide)
  refine wp_ldloc hp i₅ (d := sliceOff) (by decide) fun s₆ u₆ => wp_orr (op2_lsr (by decide)) fun s₇ u₇ =>
    wp_mov (op2_imm (by decide)) fun s₈ u₈ => wp_sub (op2_reg _ _) fun s₉ u₉ =>
    wp_orr (op2_reg _ _) fun s₁₀ u₁₀ => wp_mov (op2_lsr (by decide)) fun s₁₁ u₁₁ =>
    wp_sub (op2_reg _ _) fun s₁₂ u₁₂ => wp_orr (op2_reg _ _) fun s₁₃ u₁₃ =>
    wp_mov (op2_lsr (by decide)) fun s₁₄ u₁₄ => wp_and (op2_reg _ _) fun s₁₅ u₁₅ =>
    wp_eor (op2_imm (by decide)) fun s₁₆ u₁₆ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨?_, ?_⟩
  · have m₅ : s₅.mem = s.mem := o₅.mem
    have v1 : s₈.gpr .r1 = kindV s₀ ^^^ 1 := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
    have v2 : s₈.gpr .r2 = (kindV s₀ ^^^ (2 : BitVec 32)) ||| BitVec.ofNat 32 pass ||| (BitVec.ofNat 32 slice >>> 1) := by
      rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, lw_mem m₅, ps.slice, lw_mem o₃.mem, ps.pass]
    have v12 : s₁₁.gpr .r12 = if kindV s₀ ^^^ 1 = 0 then 0 else 1 := by
      rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .r1 (by decide), u₈.gpr, v1, nz]
    have v0 : s₁₄.gpr .r0 = if (kindV s₀ ^^^ (2 : BitVec 32)) ||| BitVec.ofNat 32 pass ||| (BitVec.ofNat 32 slice >>> 1) = 0
        then 0 else 1 := by
      rw [u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, u₁₂.other .r2 (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
        v2, nz]
    have v16 : s₁₆.gpr .r12 = ((if kindV s₀ ^^^ 1 = 0 then (0 : BitVec 32) else 1) &&&
        (if (kindV s₀ ^^^ (2 : BitVec 32)) ||| BitVec.ofNat 32 pass ||| (BitVec.ofNat 32 slice >>> 1) = 0 then 0 else 1)) ^^^ 1 := by
      rw [u₁₆.gpr, u₁₅.gpr, v0, u₁₄.other _ (by decide), u₁₃.other _ (by decide),
        u₁₂.other _ (by decide), v12]
    have k1 : (kindV s₀ ^^^ 1 = 0) ↔ (kindV s₀).toNat = 1 := by
      rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with e | e | e <;>
        · rw [show kindV s₀ = BitVec.ofNat 32 (kindV s₀).toNat by simp, e]; decide
    have ps' : (BitVec.ofNat 32 slice).toNat < 2 ↔ slice < 2 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have pp : BitVec.ofNat 32 pass = 0 ↔ pass = 0 := by
      constructor
      · intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpass] at this; exact this
      · intro e; rw [e]; rfl
    rw [MdStream.Arm.eval_eq, z, v16, mode_bits, independent_eq hk]
    simp only [k1, id_zero hk, ps', pp, Bool.decide_and, Bool.and_assoc]
  · exact ((((((((((((o₅.trans (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans (Only.of_upd u₈)).trans
      (Only.of_upd u₉)).trans (Only.of_upd u₁₀)).trans (Only.of_upd u₁₁)).trans (Only.of_upd u₁₂)).trans
      (Only.of_upd u₁₃)).trans (Only.of_upd u₁₄)).trans (Only.of_upd u₁₅)).trans (Only.of_upd u₁₆)).trans
      (Only.of_fupd f)).mono (by simp)

end

end VG.Proof.Argon2.Arm.Derive
