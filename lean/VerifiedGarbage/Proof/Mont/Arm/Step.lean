module

public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Impl.Mont.Arm
import Mathlib.Tactic.SplitIfs

/-!
# Montgomery arithmetic on 32-bit ARM: a multiply-accumulate step

`mulStep acc rb d j` adds `r2 · d_j` and the carry `r3` to the digit of the
accumulator at `[r0 + acc + 4j]`, for digit `j` of the number at
`[rb + d]` (`src` bytes into the working space, `rb` at `src - d`), and leaves the carry in `r3` (`mulStep_ok`): with every
operand below `2¹⁶`, `x = u d + t + c` is below `2³²`; its low half is
stored and its high half is the carry. `carryUp` adds the carry into the
digits `D` and `D + 1` (`carryUp_ok`).
-/

@[expose] public section

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

/-- `r7 = ` digit `j` of the number at `[rb + d]`, which is `src = K + d`
bytes into the working space when `rb = r12 + K`. -/
theorem digitAt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {rb : Reg} {K d src j : Nat}
    (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = src)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hd : src + 4 * (j / 2) + 4 ≤ size) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .r7 (BitVec.ofNat 32 (pdig s.mem base src j)) → WP isa (.block is) s' Q) :
    WP isa (.block (digitAt rb d j ++ is)) s Q := by
  simp only [digitAt, List.cons_append, List.nil_append]
  have ea : State.addr (s.gpr rb + BitVec.ofNat 32 (d + 4 * (j / 2))) = off base (src + 4 * (j / 2)) := by
    rw [← hK, Nat.add_assoc]; exact hs.ea_off hb (by omega)
  refine wp_ldr (hs.off_lt (d := d + 4 * (j / 2)) (by omega)) ea (hs.read hd) fun s₁ u₁ => ?_
  refine wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => k s₂ ?_
  rw [u₁.gpr] at u₂
  exact ⟨u₂.gpr, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩

/-- `mla d n m a`: `d = n · m + a`. -/
theorem wp_mla {s : State} {is : List Instr} {Q : State → Prop} {d n m a : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m + s.gpr a) → WP isa (.block is) s' Q) :
    WP isa (.block (.mla d n m a :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `[r0 + acc + 4j] += r2 · d_j + r3`, the carry to `r3`. -/
theorem mulStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc src i j : Nat}
    {rb : Reg} {K d : Nat} (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = src)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hsrc : src + 4 * (j / 2) + 4 ≤ size) (ht : 4 * i + (acc + 4 * j) + 4 ≤ size)
    (hu : (s.gpr .r2).toNat < 2 ^ 16) (hc : (s.gpr .r3).toNat < 2 ^ 16)
    (htd : w32 s.mem base (4 * i + (acc + 4 * j)) < 2 ^ 16) :
    WP isa (.block (mulStep acc rb d j)) s fun u =>
      u.mem = s.mem.writeW (off base (4 * i + (acc + 4 * j))) (BitVec.ofNat 32
        (((s.gpr .r2).toNat * pdig s.mem base src j + w32 s.mem base (4 * i + (acc + 4 * j)) +
          (s.gpr .r3).toNat) % 2 ^ 16)) ∧
      (u.gpr .r3).toNat = ((s.gpr .r2).toNat * pdig s.mem base src j +
          w32 s.mem base (4 * i + (acc + 4 * j)) + (s.gpr .r3).toNat) / 2 ^ 16 ∧
      Rest [.r3, .r5, .r7] s u := by
  simp only [mulStep]
  refine digitAt_ok hs hb hK h6 hsrc fun s₁ u₁ => ?_
  have hs₁ : Scr s₁ base size := hs.of_rest (u₁.rest (ws := [.r7]) (by simp)) (by decide)
  have hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]
    exact hp
  refine wp_ldr (hs.off_lt (by omega)) (hs₁.ea_at hp₁ (by omega)) (hs₁.read ht) fun s₂ u₂ => ?_
  refine wp_mla fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have hs₅ : Scr s₅ base size := hs₁.of_rest (((u₂.rest (ws := [.r5, .r7]) (by simp)).trans
    (u₃.rest (by simp))).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))) (by decide)
  have hp₅ : s₅.gpr .r0 = s₅.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
    exact hp₁
  refine wp_str (hs.off_lt (by omega)) (hs₅.ea_at hp₅ (by omega)) (hs₅.write ht) fun s₆ m₆ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₇ u₇ => WP.block_nil ?_
  -- The values along the way.
  have m₁ : s₁.mem = s.mem := u₁.mem
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have r2₂ : s₂.gpr .r2 = s.gpr .r2 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (pdig s.mem base src j) := by
    rw [u₂.other _ (by decide), u₁.gpr]
  have r5₂ : s₂.gpr .r5 = s.mem.readW (off base (4 * i + (acc + 4 * j))) 32 := by rw [u₂.gpr, m₁]
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r6₄ : s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact h6
  have r5₃ : s₃.gpr .r5 = s₂.gpr .r2 * s₂.gpr .r7 + s₂.gpr .r5 := u₃.gpr
  have r5₄ : s₄.gpr .r5 = s₃.gpr .r5 + s₃.gpr .r3 := u₄.gpr
  have r5₅ : s₅.gpr .r5 = s₄.gpr .r5 := u₅.other _ (by decide)
  have r7₅ : s₅.gpr .r7 = s₄.gpr .r5 &&& s₄.gpr .r6 := u₅.gpr
  have hd : pdig s.mem base src j < 2 ^ 16 := hdig_lt _ _
  have hx := step_lt hu hd htd hc
  have hmul : (s.gpr .r2).toNat * pdig s.mem base src j < 2 ^ 32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hu) (Nat.le_of_lt_succ hd); omega
  have hprod : (s₂.gpr .r2 * s₂.gpr .r7).toNat = (s.gpr .r2).toNat * pdig s.mem base src j := by
    rw [r2₂, r7₂, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := pdig _ _ _ _) (by omega),
      Nat.mod_eq_of_lt hmul]
  have e2 : (s₂.gpr .r5).toNat = w32 s.mem base (4 * i + (acc + 4 * j)) := by rw [r5₂]
  have a1 : (s₃.gpr .r5).toNat = (s.gpr .r2).toNat * pdig s.mem base src j +
      w32 s.mem base (4 * i + (acc + 4 * j)) := by
    rw [r5₃, toNat_add_lt (by rw [hprod, e2]; omega), hprod, e2]
  have hr5 : (s₄.gpr .r5).toNat = (s.gpr .r2).toNat * pdig s.mem base src j +
      w32 s.mem base (4 * i + (acc + 4 * j)) + (s.gpr .r3).toNat := by
    rw [r5₄, toNat_add_lt (by rw [a1, r3₃]; omega), a1, r3₃]
  refine ⟨?_, ?_, ?_⟩
  · rw [u₇.mem, m₆.mem, m₅, r7₅, r6₄]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X25519.Arm.toNat_and_mask16, BitVec.toNat_ofNat, hr5]
    omega
  · rw [u₇.gpr, toNat_shr, m₆.gpr, r5₅, hr5]
  · refine (((u₁.rest (ws := [.r3, .r5, .r7]) (by simp)).trans (u₂.rest (by simp))).trans
      ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
      ((u₅.rest (by simp)).trans ((m₆.rest _).trans (u₇.rest (by simp))))

end VG.Proof.Mont.Arm
