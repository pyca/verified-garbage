module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillSteps
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on RISC-V: the state of the filling loops

`FS s₀ pass slice lane index ctr st`: the body at a position of the filling
loops (`Pos`), the memory matrix representing `st`'s, and the address block
cached in `scratch[2048, 3072)` that of the counter in the frame, if it is
not zero (`CacheOk`). `addressMode_ok`: `addressMode` leaves `a5` nonzero
for data-dependent addressing.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_li wp_sub)
open VG.Spec.Argon2 (Block zeroBlock FillState addressBlock independent)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff counterOff)

/-- The address block cached at `scratch + 2048`, for the counter in the frame. -/
def CacheOk (s₀ : State) (pass lane slice ctr : Nat) (s : State) : Prop :=
  ctr < 2 ^ 32 ∧ lw s₀ s counterOff = BitVec.ofNat 64 ctr ∧
    (ctr = 0 ∨ 1 ≤ ctr ∧
      blockAt s.mem (scrP s₀ + BitVec.ofNat 64 2048) = addressBlock (prm s₀) pass lane slice ctr)

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
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with
    h | h | h
  · rw [independent, hv, ite_eq_left h, e1, e2, h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_left h, e3, e3', h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_right (by omega), e4, e5, h]; simp
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
        omega
      rw [hm] at this; exact of_decide_eq_true this
    have hl := ((0 - x) ||| x).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 1
    omega

/-- The second test of `addressMode`: Argon2id in the first two slices of the first pass. -/
theorem id_zero {k : Nat} (hk : k ≤ 2) {pass slice : Nat} (hp : pass < 2 ^ 64) (hs : slice < 4) :
    ((BitVec.ofNat 64 k ^^^ BitVec.ofNat 64 2) ||| BitVec.ofNat 64 pass ||| (BitVec.ofNat 64 slice >>> 1) = 0) ↔
      (k = 2 ∧ pass = 0 ∧ slice < 2) := by
  have e : BitVec.ofNat 64 slice >>> 1 = 0 ↔ slice < 2 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega
  have f : BitVec.ofNat 64 k ^^^ BitVec.ofNat 64 2 = 0 ↔ k = 2 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h <;> subst h <;> decide
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
    WP isa (.block (Impl.Argon2.RISCV64.Derive.nonzero d n t ++ is)) s Q := by
  simp only [Impl.Argon2.RISCV64.Derive.nonzero, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_or fun s₃ u₃ =>
    wp_srl (by decide) fun u u₄ => k u ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other n hnt, u₁.gpr, u₁.other n hnt,
      show BitVec.ofNat 64 0 = 0 from rfl, nz]
  · exact (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
      |>.mono (by simp)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addressMode`: `a5` is nonzero for data-dependent addressing. -/
theorem addressMode_ok {s : State} (h : Inv s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.addressMode) s fun t =>
      VG.RISCV64.eval (.nonzero .a5) t = some (!independent (prm s₀) pass slice) ∧
        Only [.a0, .a1, .a2, .a3, .a4, .a5] s t := by
  have hk := hp.kind_le
  have K : (arg32 s₀ 0).setWidth 64 = BitVec.ofNat 64 (kindV s₀).toNat := ofNat_toNat (toNat_ext32 _)
  unfold Impl.Argon2.RISCV64.Derive.addressMode
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldw hp h (i := 0) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_xor fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_xor fun s₅ u₅ => ?_
  have o₅ := ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have i₅ := h.only o₅
  refine wp_ldloc i₅ (d := passOff) (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ => ?_
  have o₇ := (o₅.trans (Only.of_upd u₆)).trans (Only.of_upd u₇)
  have i₇ := h.only o₇
  refine wp_ldloc i₇ (d := sliceOff) (by decide) fun s₈ u₈ => wp_srl (by decide) fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => ?_
  have o₁₀ := ((o₇.trans (Only.of_upd u₈)).trans (Only.of_upd u₉)).trans (Only.of_upd u₁₀)
  have v4 : s₁₀.gpr .a1 = BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, K]
  have v5 : s₁₀.gpr .a2 = (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 2) |||
      BitVec.ofNat 64 pass ||| (BitVec.ofNat 64 slice >>> 1) := by
    rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₈.other _ (by decide), u₇.gpr,
      u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, K, lw_mem o₇.mem, ps.slice,
      lw_mem o₅.mem, ps.pass]
  refine nonzero_ok (by decide) fun s₁₁ v₁₁ o₁₁ => nonzero_ok (by decide) fun s₁₂ v₁₂ o₁₂ =>
    wp_and fun t ut => WP.block_nil ⟨?_, ?_⟩
  · have r8 : t.gpr .a5 = (if BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 = 0 then 0 else 1) &&&
        (if (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 2) ||| BitVec.ofNat 64 pass |||
          (BitVec.ofNat 64 slice >>> 1) = 0 then 0 else 1) := by
      rw [ut.gpr, o₁₂.gpr _ (by decide), v₁₁, v4, v₁₂, o₁₁.gpr _ (by decide), v5]
    have k1 : (BitVec.ofNat 64 (kindV s₀).toNat ^^^ BitVec.ofNat 64 1 = 0) ↔ (kindV s₀).toNat = 1 := by
      rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with
        e | e | e <;> rw [e] <;> decide
    rw [VG.RISCV64.Wp.eval_nonzero, r8, mode_bits, independent_eq hk]
    simp only [k1, id_zero hk (by omega : pass < 2 ^ 64) hs, Bool.decide_and, Bool.and_assoc]
  · exact (((o₁₀.trans o₁₁).trans o₁₂).trans (Only.of_upd ut)).mono (by simp)

end

end VG.Proof.Argon2.RISCV64.Derive
