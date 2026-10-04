import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillRef

/-!
# Argon2 on ARMv7: the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the locals.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_orr wp_and op2_imm op2_reg op2_lsr)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Sha512.Arm (Only)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- A register after an update, as an `if` on the register. -/
theorem upd_get {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v) (r : Reg) :
    t.gpr r = if r = d then v else s.gpr r := by
  by_cases h : r = d
  · subst h; rw [ite_eq_left rfl, u.gpr]
  · rw [ite_eq_right h, u.other r h]

theorem sel (a c : BitVec 32) (p : Prop) [Decidable p] :
    a ^^^ ((c ^^^ a) &&& (if p then BitVec.allOnes 32 else 0)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [hp]

theorem mask_sub (p : Prop) [Decidable p] {x : BitVec 32} (hx : x = 1) :
    (if p then (0 : BitVec 32) else 1) - x = if p then BitVec.allOnes 32 else 0 := by
  subst hx
  by_cases hp : p <;> simp only [hp, ite_true, ite_false] <;> decide

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 32) :
    BitVec.ofNat 32 x + BitVec.allOnes 32 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat32 h', toNat32 (by omega), BitVec.toNat_allOnes]
  omega

theorem ofNat_eq_zero {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n = 0 ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [toNat32 h] at this
  · rintro rfl; rfl

theorem xor_eq_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0 ↔ a = b := by
  constructor
  · intro e
    have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
    rwa [toNat32 ha, toNat32 hb] at this
  · rintro rfl; simp

theorem ofNat_pred {n : Nat} (h : 1 ≤ n) {x : BitVec 32} (hx : x = 1) :
    BitVec.ofNat 32 n - x = BitVec.ofNat 32 (n - 1) := by
  rw [hx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat h]

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countSelect`: the window's size, to the locals and `r0`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 31)
    (hi : index < (prm s₀).segmentLen) (hl : lane < lanesN s₀) (hrl : rl < lanesN s₀)
    (ha : s.gpr .r0 = BitVec.ofNat 32 base) (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      t.gpr .r0 = BitVec.ofNat 32 (countV base index (rl == lane)) →
      lw s₀ t countOff = BitVec.ofNat 32 (countV base index (rl == lane)) →
      (∀ e, e + 4 ≤ 256 → (countOff + 4 ≤ e ∨ e + 4 ≤ countOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.r0, .r1, .r2, .r3], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.countSelect ++ is)) s Q := by
  have sl := segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.Arm.Derive.countSelect
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_sub (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    wp_sub (op2_reg _ _) fun s₅ u₅ => wp_orr (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_lsr (by decide)) fun s₇ u₇ =>
    wp_sub (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_reg _ _) fun s₉ u₉ => ?_
  have o₉ := ((((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
    (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans (Only.of_upd u₈)).trans (Only.of_upd u₉)
  have h₉ := h.of_only o₉ (by decide)
  refine wp_ldloc hp h₉.fs.inv (d := refLaneOff) (by decide) fun s₁₀ u₁₀ =>
    wp_ldloc hp (h₉.fs.inv.upd u₁₀ (by decide)) (d := laneOff) (by decide) fun s₁₁ u₁₁ =>
    wp_eor (op2_reg _ _) fun s₁₂ u₁₂ => wp_mov (op2_imm (by decide)) fun s₁₃ u₁₃ =>
    wp_sub (op2_reg _ _) fun s₁₄ u₁₄ => wp_orr (op2_reg _ _) fun s₁₅ u₁₅ => wp_mov (op2_lsr (by decide)) fun s₁₆ u₁₆ =>
    wp_sub (op2_imm (by decide)) fun s₁₇ u₁₇ => wp_eor (op2_reg _ _) fun s₁₈ u₁₈ =>
    wp_and (op2_reg _ _) fun s₁₉ u₁₉ => wp_eor (op2_reg _ _) fun s₂₀ u₂₀ => ?_
  have o₂₀ := o₉.trans (((((((((((Only.of_upd u₁₀).trans (Only.of_upd u₁₁)).trans (Only.of_upd u₁₂)).trans
    (Only.of_upd u₁₃)).trans (Only.of_upd u₁₄)).trans (Only.of_upd u₁₅)).trans (Only.of_upd u₁₆)).trans
    (Only.of_upd u₁₇)).trans (Only.of_upd u₁₈)).trans (Only.of_upd u₁₉)).trans (Only.of_upd u₂₀))
  have h₂₀ := h.of_only o₂₀ (by decide)
  -- The value.
  have m : ∀ {t : State} {ds : List Reg}, Only ds s t → ∀ d, lw s₀ t d = lw s₀ s d := fun k d => lw_mem k.mem d
  have mi : lw s₀ s₉ refLaneOff = BitVec.ofNat 32 rl := by rw [m o₉, hr]
  have ml : lw s₀ s₁₀ laneOff = BitVec.ofNat 32 lane := by
    rw [lw_mem u₁₀.mem, m o₉, h.fs.pos.lane]
  have v : s₂₀.gpr .r0 = (s.gpr .r0 + (((((0 : BitVec 32) - lw s₀ s indexOff) ||| lw s₀ s indexOff) >>> 31) - (1 : BitVec 32))) ^^^
      (((s.gpr .r0 + lw s₀ s indexOff - (1 : BitVec 32)) ^^^ (s.gpr .r0 + (((((0 : BitVec 32) - lw s₀ s indexOff) ||| lw s₀ s indexOff) >>> 31) - (1 : BitVec 32)))) &&&
        (((((0 : BitVec 32) - (lw s₀ s₉ refLaneOff ^^^ lw s₀ s₁₀ laneOff)) ||| (lw s₀ s₉ refLaneOff ^^^ lw s₀ s₁₀ laneOff)) >>> 31) - (1 : BitVec 32))) := by
    simp only [upd_get u₂₀, upd_get u₁₉, upd_get u₁₈, upd_get u₁₇, upd_get u₁₆, upd_get u₁₅, upd_get u₁₄, upd_get u₁₃, upd_get u₁₂, upd_get u₁₁, upd_get u₁₀,
      upd_get u₉, upd_get u₈, upd_get u₇, upd_get u₆, upd_get u₅, upd_get u₄, upd_get u₃, upd_get u₂, upd_get u₁, ↓reduceIte, reduceCtorEq]
  have val : s₂₀.gpr .r0 = BitVec.ofNat 32 (countV base index (rl == lane)) := by
    rw [v, mi, ml, h.fs.pos.index, ha, nz, nz, mask_sub _ rfl, mask_sub _ rfl, sel, countV]
    simp only [ofNat_eq_zero (show index < 2 ^ 32 by omega), xor_eq_zero (show rl < 2 ^ 32 by omega)
      (show lane < 2 ^ 32 by omega)]
    by_cases hs : rl = lane
    · simp only [hs, ite_true, show (lane == lane) = true from beq_self_eq_true lane]
      rw [BitVec.ofNat_add_ofNat, ofNat_pred (hsame hs) rfl]
    · simp only [hs, ite_false, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs, Bool.false_eq_true]
      by_cases hi0 : index = 0
      · rw [ite_eq_left hi0, ite_eq_left hi0, add_allOnes (hother hs hi0) (by omega)]
      · rw [ite_eq_right hi0, ite_eq_right hi0, Nat.sub_zero]
        exact BitVec.add_zero _
  refine wp_stloc hp h₂₀.fs.inv (d := countOff) (by decide) fun t it vt ot gt mt => k t ?_ (by rw [gt, val])
    (by rw [vt, val]) (fun e he hd => by rw [ot e he hd, m o₂₀]) (fun r hr => by rw [gt, (o₂₀.mono (es := [.r0, .r1, .r2, .r3]) (by simp)).gpr r hr])
  exact h₂₀.store hp it (d := countOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

end

end VG.Proof.Argon2.Arm.Derive
