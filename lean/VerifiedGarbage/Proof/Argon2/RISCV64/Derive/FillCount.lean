module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillRef
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals

/-!
# Argon2 on RISC-V: the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the frame.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_add wp_subi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.RISCV64.Derive (indexOff laneOff refLaneOff cntOff)

theorem sel (a c : BitVec 64) (p : Prop) [Decidable p] :
    a ^^^ ((c ^^^ a) &&& (if p then BitVec.allOnes 64 else 0)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [hp]

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.allOnes 64 = BitVec.ofNat 64 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_eq_zero {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  · rintro rfl; rfl

theorem xor_eq_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = 0 ↔ a = b := by
  constructor
  · intro e
    have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; simp

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countSelect`: the window's size, to the frame and `a0`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 32)
    (hi : index < (prm s₀).segmentLen) (hl : lane < lanesN s₀) (hrl : rl < lanesN s₀)
    (ha : s.gpr .a0 = BitVec.ofNat 64 base) (hr : lw s₀ s refLaneOff = BitVec.ofNat 64 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr σ J1 J2 t →
      t.gpr .a0 = BitVec.ofNat 64 (countV base index (rl == lane)) →
      lw s₀ t cntOff = BitVec.ofNat 64 (countV base index (rl == lane)) →
      (∀ e, e + 8 ≤ 320 → (cntOff + 8 ≤ e ∨ e + 8 ≤ cntOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.a0, .a1, .a2, .a3], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.countSelect ++ is)) s Q := by
  have sl := segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.RISCV64.Derive.countSelect
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc h.fs.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ =>
    wp_subi (by decide) fun s₃ u₃ => nonzero_ok (by decide) fun s₄ v₄ o₄ =>
    wp_subi (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ => ?_
  have o₆ := (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans o₄).trans
    (Only.of_upd u₅)).trans (Only.of_upd u₆)
  have h₆ := h.of_only o₆
  refine wp_ldloc h₆.fs.inv (d := refLaneOff) (by decide) fun s₇ u₇ =>
    wp_ldloc (h₆.of_only (Only.of_upd u₇)).fs.inv (d := laneOff) (by decide) fun s₈ u₈ =>
    wp_xor fun s₉ u₉ => nonzero_ok (by decide) fun s₁₀ v₁₀ o₁₀ =>
    wp_subi (by decide) fun s₁₁ u₁₁ => wp_xor fun s₁₂ u₁₂ => wp_and fun s₁₃ u₁₃ =>
    wp_xor fun s₁₄ u₁₄ => ?_
  have o₁₄ := o₆.trans ((((((((Only.of_upd u₇).trans (Only.of_upd u₈)).trans (Only.of_upd u₉)).trans
    o₁₀).trans (Only.of_upd u₁₁)).trans (Only.of_upd u₁₂)).trans (Only.of_upd u₁₃)).trans
    (Only.of_upd u₁₄))
  have h₁₄ := h.of_only o₁₄
  have m : ∀ {t : State} {ds : List Reg}, Only ds s t → ∀ d, lw s₀ t d = lw s₀ s d :=
    fun k d => lw_mem k.mem d
  -- The values.
  have r5₁ : s₁.gpr .a2 = BitVec.ofNat 64 index := by rw [u₁.gpr, h.fs.pos.index]
  have X : s₁₁.gpr .a1 = BitVec.ofNat 64 base + BitVec.ofNat 64 index - BitVec.ofNat 64 1 := by
    rw [u₁₁.other _ (by decide), o₁₀.gpr _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), o₄.gpr _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), ha, r5₁]
  have M₁ : s₅.gpr .a3 = if index = 0 then BitVec.allOnes 64 else 0 := by
    rw [u₅.gpr, v₄, u₃.other _ (by decide), u₂.other _ (by decide), r5₁]
    by_cases h0 : index = 0
    · subst h0; decide
    · rw [ite_eq_right (mt (ofNat_eq_zero (by omega)).mp h0), ite_eq_right h0]; decide
  have Y : s₁₁.gpr .a0 = BitVec.ofNat 64 base + (if index = 0 then BitVec.allOnes 64 else 0) := by
    rw [u₁₁.other _ (by decide), o₁₀.gpr _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), o₄.gpr _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha, M₁]
  have M₂ : s₁₁.gpr .a2 = if rl = lane then BitVec.allOnes 64 else 0 := by
    rw [u₁₁.gpr, v₁₀, u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₈.gpr, lw_mem u₇.mem, m o₆, hr,
      (h.of_only o₆).fs.pos.lane]
    by_cases hs : rl = lane
    · rw [hs, BitVec.xor_self, ite_eq_left rfl]; decide
    · rw [ite_eq_right (mt (xor_eq_zero (by omega) (by omega)).mp hs), ite_eq_right hs]; decide
  have val : s₁₄.gpr .a0 = BitVec.ofNat 64 (countV base index (rl == lane)) := by
    rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₃.gpr, u₁₂.gpr,
      u₁₂.other _ (by decide), X, Y, M₂, sel, countV]
    by_cases hs : rl = lane
    · rw [ite_eq_left hs, show (rl == lane) = true from beq_iff_eq.mpr hs, BitVec.ofNat_add_ofNat,
        sub_ofNat (hsame hs)]
      rfl
    · rw [ite_eq_right hs, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs]
      simp only [Bool.false_eq_true, ite_false]
      by_cases hi0 : index = 0
      · simp only [hi0, ite_true]; exact add_allOnes (hother hs hi0) (by omega)
      · simp only [hi0, ite_false, Nat.sub_zero]; exact BitVec.add_zero _
  refine wp_stloc h₁₄.fs.inv (d := cntOff) (by decide) fun t it vt ot gt mt =>
    k t (h₁₄.store hp it (d := cntOff) (by decide) (by decide) mt ot) (by rw [gt, val]) (by rw [vt, val])
      (fun e he hd => by rw [ot e he hd, m o₁₄])
      (fun r hr => by rw [gt, (o₁₄.mono (es := [.a0, .a1, .a2, .a3]) (by simp)).gpr r hr])

end

end VG.Proof.Argon2.RISCV64.Derive
