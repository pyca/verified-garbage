import VerifiedGarbage.Proof.Mont.Arm.Words

/-!
# Montgomery arithmetic on 32-bit ARM: a multiply-accumulate step

`mulStep acc src j` adds `r2 · d_j` and the carry `r3` to the digit of the
accumulator at `[r0 + acc + 4j]`, for digit `j` of the number at
`[r12 + src]`, and leaves the carry in `r3` (`mulStep_ok`): with every
operand below `2¹⁶`, `x = u d + t + c` is below `2³²`; its low half is
stored and its high half is the carry. `carryUp` adds the carry into the
digits `D` and `D + 1` (`carryUp_ok`).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul op2_reg op2_lsr op2_lsl
  op2_imm dpVal toNat_add_lt toNat_shr)

/-- A step's sum is below `2³²`. -/
theorem step_lt {u d t c : Nat} (hu : u < 2 ^ 16) (hd : d < 2 ^ 16) (ht : t < 2 ^ 16) (hc : c < 2 ^ 16) :
    u * d + t + c < 2 ^ 32 := by
  have : u * d ≤ (2 ^ 16 - 1) * (2 ^ 16 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem toNat_and_r6 {x m : BitVec 32} (hm : m = VG.Proof.X25519.Arm.mask16) : (x &&& m).toNat = x.toNat % 2 ^ 16 := by
  subst hm; exact VG.Proof.X25519.Arm.toNat_and_mask16 x

/-- `d = ` digit `h` of `w`. -/
theorem wp_half {s : State} {is : List Instr} {Q : State → Prop} {d w : Reg} {h : Nat} (hh : h < 2)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 32 (hdig (s.gpr w).toNat h)) → WP isa (.block is) s' Q) :
    WP isa (.block (half d w h :: is)) s Q := by
  obtain rfl | rfl : h = 0 ∨ h = 1 := by omega
  · refine wp_dp (op2_reg s .r6) fun s' u => k s' ?_
    have e : dpVal .and (s.gpr w) (s.gpr .r6) = BitVec.ofNat 32 (hdig (s.gpr w).toNat 0) := by
      apply BitVec.eq_of_toNat_eq
      rw [dpVal, toNat_and_r6 h6, BitVec.toNat_ofNat]
      simp only [hdig, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      omega
    exact e ▸ u
  · refine wp_mov (op2_lsr (by decide)) fun s' u => k s' ?_
    have e : s.gpr w >>> 16 = BitVec.ofNat 32 (hdig (s.gpr w).toNat 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_shr, BitVec.toNat_ofNat]
      have := (s.gpr w).isLt
      simp only [hdig, Nat.mul_one]
      omega
    exact e ▸ u

/-- `r7 = ` digit `j` of the number at `[r12 + src]`. -/
theorem digitAt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hd : src + 4 * (j / 2) + 4 ≤ size) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .r7 (BitVec.ofNat 32 (pdig s.mem base src j)) → WP isa (.block is) s' Q) :
    WP isa (.block (digitAt src j ++ is)) s Q := by
  simp only [digitAt, List.cons_append, List.nil_append]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hd) fun s₁ u₁ => ?_
  refine wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => k s₂ ?_
  rw [u₁.gpr] at u₂
  exact ⟨u₂.gpr, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩

/-- `[r0 + acc + 4j] += r2 · d_j + r3`, the carry to `r3`. -/
theorem mulStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc src i j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hsrc : src + 4 * (j / 2) + 4 ≤ size) (ht : 4 * i + (acc + 4 * j) + 4 ≤ size)
    (hu : (s.gpr .r2).toNat < 2 ^ 16) (hc : (s.gpr .r3).toNat < 2 ^ 16)
    (htd : w32 s.mem base (4 * i + (acc + 4 * j)) < 2 ^ 16) :
    WP isa (.block (mulStep acc src j)) s fun u =>
      u.mem = s.mem.writeW (off base (4 * i + (acc + 4 * j))) (BitVec.ofNat 32
        (((s.gpr .r2).toNat * pdig s.mem base src j + w32 s.mem base (4 * i + (acc + 4 * j)) +
          (s.gpr .r3).toNat) % 2 ^ 16)) ∧
      (u.gpr .r3).toNat = ((s.gpr .r2).toNat * pdig s.mem base src j +
          w32 s.mem base (4 * i + (acc + 4 * j)) + (s.gpr .r3).toNat) / 2 ^ 16 ∧
      Rest [.r3, .r5, .r7] s u := by
  simp only [mulStep]
  refine digitAt_ok hs h6 hsrc fun s₁ u₁ => ?_
  refine wp_mul fun s₂ u₂ => ?_
  have hs₂ : Scr s₂ base size := hs.of_rest ((u₁.rest (ws := [.r7]) (by simp)).trans (u₂.rest (by simp)))
    (by decide)
  have hp₂ : s₂.gpr .r0 = s₂.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact hp
  refine wp_ldr (hs.off_lt (by omega)) (hs₂.ea_at hp₂ (by omega)) (hs₂.read ht) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  have hs₆ : Scr s₆ base size := hs₂.of_rest (((u₃.rest (ws := [.r5, .r7]) (by simp)).trans
    (u₄.rest (by simp))).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))) (by decide)
  have hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    exact hp₂
  refine wp_str (hs.off_lt (by omega)) (hs₆.ea_at hp₆ (by omega)) (hs₆.write ht) fun s₇ m₇ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₈ u₈ => WP.block_nil ?_
  -- The values along the way.
  have m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
  have r2₁ : s₁.gpr .r2 = s.gpr .r2 := u₁.other _ (by decide)
  have r3₄ : s₄.gpr .r3 = s.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r6₅ : s₅.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]; exact h6
  have r7₃ : s₃.gpr .r7 = s₂.gpr .r7 := u₃.other _ (by decide)
  have r7₄ : s₄.gpr .r7 = s₃.gpr .r7 := u₄.other _ (by decide)
  have r5₄ : s₄.gpr .r5 = s₃.gpr .r5 + s₃.gpr .r7 := u₄.gpr
  have r5₅ : s₅.gpr .r5 = s₄.gpr .r5 + s₄.gpr .r3 := u₅.gpr
  have r5₆ : s₆.gpr .r5 = s₅.gpr .r5 := u₆.other _ (by decide)
  have r7₆ : s₆.gpr .r7 = s₅.gpr .r5 &&& s₅.gpr .r6 := u₆.gpr
  have r5₃ : s₃.gpr .r5 = s₂.mem.readW (off base (4 * i + (acc + 4 * j))) 32 := u₃.gpr
  have r7₂ : s₂.gpr .r7 = s₁.gpr .r2 * s₁.gpr .r7 := u₂.gpr
  have hd : pdig s.mem base src j < 2 ^ 16 := hdig_lt _ _
  have hx := step_lt hu hd htd hc
  have hr7 : (s₂.gpr .r7).toNat = (s.gpr .r2).toNat * pdig s.mem base src j := by
    rw [r7₂, r2₁, u₁.gpr, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := pdig _ _ _ _) (by omega),
      Nat.mod_eq_of_lt (by have := Nat.mul_le_mul (Nat.le_of_lt_succ hu) (Nat.le_of_lt_succ hd); omega)]
  have e3 : (s₃.gpr .r5).toNat = w32 s.mem base (4 * i + (acc + 4 * j)) := by rw [r5₃, m₂]
  have e7 : (s₃.gpr .r7).toNat = (s.gpr .r2).toNat * pdig s.mem base src j := by rw [r7₃, hr7]
  have a1 : (s₄.gpr .r5).toNat = w32 s.mem base (4 * i + (acc + 4 * j)) +
      (s.gpr .r2).toNat * pdig s.mem base src j := by
    rw [r5₄, toNat_add_lt (by rw [e3, e7]; omega), e3, e7]
  have hr5 : (s₅.gpr .r5).toNat = (s.gpr .r2).toNat * pdig s.mem base src j +
      w32 s.mem base (4 * i + (acc + 4 * j)) + (s.gpr .r3).toNat := by
    rw [r5₅, toNat_add_lt (by rw [a1, r3₄]; omega), a1, r3₄]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [u₈.mem, m₇.mem, m₆, r7₆, r6₅]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X25519.Arm.toNat_and_mask16, BitVec.toNat_ofNat, hr5]
    omega
  · rw [u₈.gpr, toNat_shr, m₇.gpr, r5₆, hr5]
  · refine (((u₁.rest (ws := [.r3, .r5, .r7]) (by simp)).trans (u₂.rest (by simp))).trans
      ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
      (((u₅.rest (by simp)).trans (u₆.rest (by simp))).trans ((m₇.rest _).trans (u₈.rest (by simp))))

end VG.Proof.Mont.Arm
