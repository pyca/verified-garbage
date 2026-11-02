module

import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillRef

/-!
# Argon2 on RISC-V: the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2); `wrap_ok`: its column, from the window's start, modulo the lane
length, by a subtraction corrected by its sign; `refPointer_ok` and
`curPointer_ok`: the reference and current blocks' addresses, to the frame.
-/

@[expose] public section

/-!
# Argon2 on RISC-V: the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the frame.
-/

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

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_add wp_addi wp_sub wp_subi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.RISCV64.Derive (laneOff laneLenOff j1Off refLaneOff startOff cntOff tmpOff curOff)

/-- The position in the window that `j1` selects. -/
def relV (cnt j1 : Nat) : Nat := cnt - 1 - cnt * (j1 * j1 / 2 ^ 32) / 2 ^ 32

theorem mulHi {a b : Nat} (h : a * b < 2 ^ 64) :
    (BitVec.ofNat 64 a * BitVec.ofNat 64 b) >>> 32 = BitVec.ofNat 64 (a * b / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : a % 2 ^ 64 * (b % 2 ^ 64) = a * b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right a hb) h),
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left b ha) h)]
  rw [this, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_arith)]

/-- The sign of `sum - L` as a bit. -/
theorem sign_sub {a b : Nat} (ha : a < 2 ^ 63) (hb : b ≤ 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  by_cases c : a < b
  · rw [ite_eq_left c, show (1 : BitVec 64).toNat = 1 from rfl]; omega_arith
  · rw [ite_eq_right c, show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith

theorem wrap_eq {a b : Nat} (ha : a < 2 * b) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) + (if a < b then (1 : BitVec 64) else 0) * BitVec.ofNat 64 b =
      BitVec.ofNat 64 (a % b) := by
  rw [Proof.Argon2.reference_wrap a b ha]
  by_cases c : a < b
  · rw [ite_eq_left c, ite_eq_left c, show (1 : BitVec 64) * BitVec.ofNat 64 b = BitVec.ofNat 64 b by simp,
      BitVec.sub_add_cancel]
  · rw [ite_eq_right c, ite_eq_right c, sub_ofNat (by omega_arith)]
    simp

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem laneLen_lt : (prm s₀).laneLen < 2 ^ 32 := by
  have := segLen_lt hp
  have := hp.laneLen_eq
  omega_arith

omit hp in
/-- `relative`: `r3 :=` the position in the window. -/
theorem relative_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hj : J1.toNat < 2 ^ 32) {cnt : Nat} (hc : 1 ≤ cnt)
    (hc' : cnt < 2 ^ 32) (hcnt : lw s₀ s cntOff = BitVec.ofNat 64 cnt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a0 = BitVec.ofNat 64 (relV cnt J1.toNat) → Only [.a0, .a1, .a2] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.relative ++ is)) s Q := by
  have x32 := Proof.Argon2.reference_scaled_bound J1.toNat hj
  have lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega_arith) hj
  have sq : J1.toNat * J1.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hj hj) (by decide)
  have cx : cnt * (J1.toNat * J1.toNat / 2 ^ 32) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hc' x32) (by decide)
  unfold Impl.Argon2.RISCV64.Derive.relative
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h.fs.inv (d := j1Off) (by decide) fun s₁ u₁ => wp_mul fun s₂ u₂ =>
    wp_srl (by decide) fun s₃ u₃ => ?_
  have O₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  refine wp_ldloc (h.of_only O₃).fs.inv (d := cntOff) (by decide) fun s₄ u₄ => wp_mul fun s₅ u₅ =>
    wp_srl (by decide) fun s₆ u₆ => wp_subi (by decide) fun s₇ u₇ => wp_sub fun t u => k t ?_ ?_
  · have x₃ : s₃.gpr .a1 = BitVec.ofNat 64 (J1.toNat * J1.toNat / 2 ^ 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [u₃.gpr, u₂.gpr, u₁.gpr, h.j1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
        Nat.mod_eq_of_lt sq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    have c₄ : s₄.gpr .a2 = BitVec.ofNat 64 cnt := by rw [u₄.gpr, lw_mem O₃.mem, hcnt]
    have y₆ : s₆.gpr .a1 = BitVec.ofNat 64 (cnt * (J1.toNat * J1.toNat / 2 ^ 32) / 2 ^ 32) := by
      rw [u₆.gpr, u₅.gpr, c₄, u₄.other .a1 (by decide), x₃, mulHi cx]
    rw [u.gpr, u₇.gpr, u₇.other .a1 (by decide), u₆.other .a2 (by decide), u₅.other .a2 (by decide), c₄, y₆,
      sub_ofNat hc, sub_ofNat (by omega_arith), relV]
  · exact (O₃.trans (((((Only.of_upd u₄).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans
      (Only.of_upd u₇)).trans (Only.of_upd u))).mono (by simp)

/-- `wrap`: `r3 := (start + r3) mod laneLen`. -/
theorem wrap_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) {rel stt : Nat} (hr : rel < (prm s₀).laneLen)
    (hs : stt < (prm s₀).laneLen) (ha : s.gpr .a0 = BitVec.ofNat 64 rel)
    (hst : lw s₀ s startOff = BitVec.ofNat 64 stt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a0 = BitVec.ofNat 64 ((stt + rel) % (prm s₀).laneLen) → Only [.a0, .a1, .a2, .a3] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.wrap ++ is)) s Q := by
  have L32 := laneLen_lt hp
  unfold Impl.Argon2.RISCV64.Derive.wrap
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h.fs.inv (d := startOff) (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  have O₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  refine wp_ldloc (h.of_only O₂).fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
    wp_sub fun s₄ u₄ => wp_srl (by decide) fun s₅ u₅ => wp_mul fun s₆ u₆ => wp_add fun t u => k t ?_ ?_
  · have x₂ : s₂.gpr .a0 = BitVec.ofNat 64 (stt + rel) := by
      rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), ha, hst, BitVec.ofNat_add_ofNat, Nat.add_comm]
    have l₃ : s₃.gpr .a1 = BitVec.ofNat 64 (prm s₀).laneLen := by
      rw [u₃.gpr, lw_mem O₂.mem]; exact h.fs.pr.laneLen
    have d₄ : s₄.gpr .a2 = BitVec.ofNat 64 (stt + rel) - BitVec.ofNat 64 (prm s₀).laneLen := by
      rw [u₄.gpr, u₃.other _ (by decide), x₂, l₃]
    rw [u.gpr, u₆.other .a2 (by decide), u₆.gpr, u₅.other .a2 (by decide), u₅.gpr, u₅.other .a1 (by decide),
      d₄, u₄.other .a1 (by decide), l₃, sign_sub (by omega_arith) (by omega_arith), wrap_eq (by omega_arith)]
  · exact (O₂.trans (((((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans
      (Only.of_upd u₆)).trans (Only.of_upd u))).mono (by simp)

/-- `refPointer`: the address of block `a0` of the reference lane, to the frame. -/
theorem refPointer_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) {col rl : Nat} (hc : col < (prm s₀).laneLen)
    (hrl : rl < lanesN s₀) (ha : s.gpr .a0 = BitVec.ofNat 64 col)
    (hr : lw s₀ s refLaneOff = BitVec.ofNat 64 rl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr σ J1 J2 t →
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 64 ((rl * (prm s₀).laneLen + col) * 1024) →
      (∀ e, e + 8 ≤ 320 → (tmpOff + 8 ≤ e ∨ e + 8 ≤ tmpOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.a0, .a1, .a2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.refPointer ++ is)) s Q := by
  unfold Impl.Argon2.RISCV64.Derive.refPointer Impl.Argon2.RISCV64.HPrime.mov
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addi (by decide) fun s₁ u₁ => ?_
  refine wp_ldloc (h.of_only (Only.of_upd u₁)).fs.inv (d := refLaneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  have h₂ := h.of_only K₂
  refine blockAddr_ok hp h₂.fs.inv h₂.fs.pr hrl hc (by rw [u₂.gpr, lw_mem u₁.mem, hr])
    (by rw [u₂.other _ (by decide), u₁.gpr, ha, BitVec.ofNat_add_ofNat, Nat.add_zero]) fun s₃ a₃ k₃ => ?_
  have K₃ := K₂.trans k₃
  have h₃ := h.of_only K₃
  refine wp_stloc h₃.fs.inv (d := tmpOff) (by decide) fun t it vt ot gt mt =>
    k t (h₃.store hp it (d := tmpOff) (by decide) (by decide) mt ot) (by rw [vt, a₃])
      (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r hr => by
        rw [gt, (K₃.mono (es := [.a0, .a1, .a2]) (by simp)).gpr r hr])

/-- `curPointer`: the address of the current block, to the frame. -/
theorem curPointer_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr σ J1 J2 t →
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 64
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) →
      (∀ e, e + 8 ≤ 320 → (curOff + 8 ≤ e ∨ e + 8 ≤ curOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.a0, .a1, .a2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.curPointer ++ is)) s Q := by
  have hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  unfold Impl.Argon2.RISCV64.Derive.curPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine column_ok h.fs.inv h.fs.pr h.fs.pos fun s₁ c₁ k₁ => ?_
  have h₁ := h.of_only k₁
  refine wp_ldloc h₁.fs.inv (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := k₁.trans (Only.of_upd u₂)
  have h₂ := h.of_only K₂
  refine blockAddr_ok hp h₂.fs.inv h₂.fs.pr hl hc (by rw [u₂.gpr]; exact h₁.fs.pos.lane)
    (by rw [u₂.other _ (by decide), c₁]) fun s₃ a₃ k₃ => ?_
  have K₃ := K₂.trans k₃
  have h₃ := h.of_only K₃
  refine wp_stloc h₃.fs.inv (d := curOff) (by decide) fun t it vt ot gt mt =>
    k t (h₃.store hp it (d := curOff) (by decide) (by decide) mt ot) (by rw [vt, a₃])
      (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r hr => by
        rw [gt, (K₃.mono (es := [.a0, .a1, .a2]) (by simp)).gpr r hr])

end

theorem count_eq (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      countV (baseV p.segmentLen p.laneLen pass slice) index same := by
  unfold Spec.Argon2.referenceCount countV baseV
  by_cases h : pass = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ref_eq (p : Spec.Argon2.Params) (pass lane slice index : Nat) (w : BitVec 64) :
    Spec.Argon2.reference p pass lane slice index w =
      (refLaneV p.lanes pass slice lane (w >>> 32).toNat,
        (startV p.segmentLen p.laneLen pass slice +
          relV (countV (baseV p.segmentLen p.laneLen pass slice) index
            (refLaneV p.lanes pass slice lane (w >>> 32).toNat == lane)) (w &&& 0xffffffff).toNat) %
          p.laneLen) := by
  unfold Spec.Argon2.reference
  simp only [count_eq]
  rfl

theorem lo_lt (w : BitVec 64) : (w &&& 0xffffffff).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hi_lt (w : BitVec 64) : (w >>> 32).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega_arith

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `reference`: the reference and current blocks' addresses, to the frame. -/
theorem reference_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {w : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ (w &&& 0xffffffff) (w >>> 32) s) (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀) (hs : slice < 4) (hi : index < (prm s₀).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.RISCV64.Derive.reference s fun t =>
      RS s₀ pass slice lane index ctr σ (w &&& 0xffffffff) (w >>> 32) t ∧
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 64
        (((Spec.Argon2.reference (prm s₀) pass lane slice index w).1 * (prm s₀).laneLen +
          (Spec.Argon2.reference (prm s₀) pass lane slice index w).2) * 1024) ∧
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 64
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) := by
  have L32 := laneLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [ref_eq]
  generalize hRL : refLaneV (prm s₀).lanes pass slice lane (w >>> 32).toNat = RL
  have hRL' : refLaneV (lanesN s₀) pass slice lane (w >>> 32).toNat = RL := hRL
  have rl_lt : RL < lanesN s₀ := by
    rw [← hRL', refLaneV]; split
    · exact hl
    · exact Nat.mod_lt _ (by omega_arith)
  have first : pass = 0 → slice = 0 → RL = lane := fun a b => by rw [← hRL', refLaneV, ite_eq_left ⟨a, b⟩]
  generalize hB : baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice = B
  have b_le : B ≤ (prm s₀).laneLen := by
    rw [← hB, baseV]; split
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (show slice ≤ 3 by omega_arith)) (by omega_arith))
    · omega_arith
  generalize hST : startV (prm s₀).segmentLen (prm s₀).laneLen pass slice = ST
  have st_lt : ST < (prm s₀).laneLen := by
    rw [← hST, startV]; split
    · omega_arith
    · exact Nat.mod_lt _ (by omega_arith)
  have cpos := Proof.Argon2.reference_count_positive (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) active fun a b => by simp [first a b]
  have clt := Proof.Argon2.reference_count_lt_lane (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) hs hi
  rw [count_eq, hB] at cpos clt
  unfold Impl.Argon2.RISCV64.Derive.reference
  refine WP.seq ((refLane_ok hp h (hi_lt w) hpass hs).mono fun t₁ ⟨h₁, r₁⟩ => ?_)
  rw [hRL'] at r₁
  refine WP.seq ((refStart_ok hp h₁ hpass hs).mono fun t₂ ⟨h₂, r₂, st₂⟩ => ?_)
  rw [hST] at st₂
  refine WP.seq ((countBase_ok hp h₂ hpass).mono fun t₃ ⟨k₃, a₃⟩ => ?_)
  rw [hB] at a₃
  have h₃ := h₂.of_only k₃
  simp only [List.append_assoc]
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.curPointer]
  refine countSelect_ok hp h₃ (base := B) (rl := RL) (by omega_arith) hi hl rl_lt a₃
    (by rw [lw_mem k₃.mem, r₂, r₁]) (fun e => ?_) (fun e e0 => ?_) fun t₄ h₄ a₄ c₄ o₄ g₄ => ?_
  · rw [← hB, baseV]; split
    · rename_i hp0
      by_cases hs0 : slice = 0
      · omega_arith
      · have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega_arith); omega_arith
    · omega_arith
  · have : ¬(pass = 0 ∧ slice = 0) := fun ⟨a, b⟩ => e (first a b)
    rw [← hB, baseV]; split
    · rename_i hp0
      have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega_arith); omega_arith
    · omega_arith
  refine relative_ok h₄ (lo_lt w) (cnt := countV B index (RL == lane)) cpos (by omega_arith) c₄
    fun t₅ a₅ k₅ => ?_
  have h₅ := h₄.of_only k₅
  have rel_lt : relV (countV B index (RL == lane)) (w &&& 0xffffffff).toNat < (prm s₀).laneLen := by
    unfold relV; omega_arith
  refine wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  have h₆ := h₅.of_only k₆
  refine refPointer_ok hp h₆ (Nat.mod_lt _ (by omega_arith)) rl_lt a₆ (by
      rw [lw_mem k₆.mem, lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end

end VG.Proof.Argon2.RISCV64.Derive
