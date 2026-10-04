import VerifiedGarbage.Proof.Argon2.Arm.Derive.Locals

/-!
# Argon2 on ARMv7: the parameters

`parameters_ok`: the body's first instructions point `r11` to the locals and
store there `4 · lanes` (the divisor), the segment length (by the fixed-time
division), the lane length and its size in bytes (`Prm`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov op2_lsl)
open VG.Impl.Argon2.Arm.Derive (parameters divisorOff segLenOff laneLenOff strideOff argOff)

/-- The parameters in the locals. -/
structure Prm (s₀ s : State) : Prop where
  divisor : lw s₀ s divisorOff = BitVec.ofNat 32 (4 * lanesN s₀)
  segLen : lw s₀ s segLenOff = BitVec.ofNat 32 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 32 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 32 ((prm s₀).laneLen * 1024)

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.keep {s₀ s t : State} (h : Inv s₀ s) (k : Divide.Keep s t) : Inv s₀ t :=
  h.step k.sp (k.other _ (by decide) (by decide) (by decide)) k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

/-- `x << n`, as a number, when it does not overflow. -/
theorem shl_nat {x : BitVec 32} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 32) : (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.addSp .r11 0 :: parameters) ++ is)) (entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, List.cons_append, List.append_assoc]
  refine inv_start fun s₁ i₁ _ _ => ?_
  refine wp_ldarg hp i₁ (i := Impl.Argon2.Arm.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  have e₃ : (s₃.gpr .r2).toNat = 4 * lanesN s₀ := by
    rw [u₃.gpr, u₂.gpr, shl_nat (by have : (arg s₀ 7).toNat < 2 ^ 24 := hL; show (arg s₀ 7).toNat * 4 < _; omega)]
    show (arg s₀ 7).toNat * 4 = 4 * (arg s₀ 7).toNat
    omega
  refine wp_stloc hp i₃ (d := divisorOff) (by decide) fun s₄ i₄ v₄ _ g₄ _ => ?_
  refine wp_ldarg hp i₄ (i := Impl.Argon2.Arm.Derive.memoryCostArg) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide)
  have r2₅ : s₅.gpr .r2 = s₃.gpr .r2 := by rw [u₅.other _ (by decide), g₄]
  refine Divide.code_ok (D := s₃.gpr .r2) (by rw [e₃]; omega) (by rw [e₃]; omega) r2₅ fun s₆ c₆ _ k₆ => ?_
  have i₆ := i₅.keep k₆
  rw [u₅.gpr, e₃] at c₆
  have c₆' : (s₆.gpr .r1).toNat = (prm s₀).segmentLen := by rw [c₆, hseg]; rfl
  refine wp_stloc hp i₆ (d := segLenOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ _ => ?_
  have hll : (prm s₀).laneLen ≤ blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  have hsegL : (prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_mov (op2_lsl (by decide)) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈ (by decide)
  have e₈ : (s₈.gpr .r1).toNat = (prm s₀).laneLen := by
    rw [u₈.gpr, g₇, shl_nat (by rw [c₆']; omega), c₆', hlane]; omega
  refine wp_stloc hp i₈ (d := laneLenOff) (by decide) fun s₉ i₉ v₉ o₉ g₉ _ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₀ u₁₀ => ?_
  have i₁₀ := i₉.upd u₁₀ (by decide)
  have e₁₀ : (s₁₀.gpr .r1).toNat = (prm s₀).laneLen * 1024 := by
    rw [u₁₀.gpr, g₉, shl_nat (by rw [e₈]; omega), e₈]
  refine wp_stloc hp i₁₀ (d := strideOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ _ _ => k s₁₁ i₁₁ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), lw_mem u₈.mem,
      o₇ _ (by decide) (by decide), lw_mem k₆.mem, lw_mem u₅.mem, v₄]
    exact BitVec.eq_of_toNat_eq (by rw [e₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), lw_mem u₈.mem, v₇]
    exact BitVec.eq_of_toNat_eq (by rw [c₆', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, v₉]
    exact BitVec.eq_of_toNat_eq (by rw [e₈, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])

end

end VG.Proof.Argon2.Arm.Derive
