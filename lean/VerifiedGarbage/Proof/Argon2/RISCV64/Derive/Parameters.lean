module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Divide
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body

/-!
# Argon2 on RISC-V: the parameters

`parameters_ok`: the body's first computation stores the segment length (by
the fixed-time division of the memory cost by `4 · lanes`), the lane length
and its size in bytes in the frame (`Prm`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd)
open VG.Proof.Argon2.RISCV64 (wp_sll)
open VG.Impl.Argon2.RISCV64.Derive (parameters segLenOff laneLenOff strideOff)

/-- The parameters in the frame. -/
structure Prm (s₀ s : State) : Prop where
  segLen : lw s₀ s segLenOff = BitVec.ofNat 64 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 64 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 64 ((prm s₀).laneLen * 1024)

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.divide {s₀ s t : State} (h : Inv s₀ s) (k : Divide.KeepD s t) : Inv s₀ t :=
  h.step k.sp (k.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (k.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (k.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun r hr => k.other _ (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

theorem Prm.of_mem {s₀ s t : State} (pr : Prm s₀ s) (h : t.mem = s.mem) : Prm s₀ t :=
  ⟨by rw [lw_mem h]; exact pr.segLen, by rw [lw_mem h]; exact pr.laneLen,
    by rw [lw_mem h]; exact pr.stride⟩

/-- `x << n`, as a number, when it does not overflow. -/
theorem shl_nat {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toNat_ext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem ofNat_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; simp

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {s : State} (h : Inv s₀ s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block (parameters ++ is)) s Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hb := hp.blocks_eq
  have hbl := hp.blocks_le
  have hm := mcost_lt s₀
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, List.cons_append, List.append_assoc]
  refine wp_ldw hp h (i := Impl.Argon2.RISCV64.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := h.upd u₂
  refine wp_sll (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  have e₃ : (s₃.gpr .a2).toNat = 4 * lanesN s₀ := by
    rw [u₃.gpr, u₂.gpr, shl_nat (by rw [toNat_ext32]; show lanesN s₀ * 4 < _; omega), toNat_ext32]
    show lanesN s₀ * 4 = _
    omega
  refine wp_ldw hp i₃ (i := Impl.Argon2.RISCV64.Derive.memoryCostArg) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₃.upd u₅
  refine Divide.code_ok (D := 4 * lanesN s₀) (by omega) (by omega)
    (by rw [u₅.other _ (by decide), e₃]) fun s₆ c₆ _ k₆ => ?_
  have i₆ := i₅.divide k₆
  have c₆' : (s₆.gpr .a3).toNat = (prm s₀).segmentLen := by
    rw [c₆, u₅.gpr, hseg, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    rfl
  refine wp_stloc i₆ (d := segLenOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ _ => ?_
  have hll : (prm s₀).laneLen ≤ mcostN s₀ :=
    Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)) hbl
  refine wp_sll (by decide) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈
  have e₈ : (s₈.gpr .a3).toNat = (prm s₀).laneLen := by
    rw [u₈.gpr, g₇, shl_nat (by rw [c₆']; omega), c₆', hlane]; omega
  refine wp_stloc i₈ (d := laneLenOff) (by decide) fun s₉ i₉ v₉ o₉ g₉ _ => ?_
  refine wp_sll (by decide) fun s₁₀ u₁₀ => ?_
  have i₁₀ := i₉.upd u₁₀
  have e₁₀ : (s₁₀.gpr .a3).toNat = (prm s₀).laneLen * 1024 := by
    rw [u₁₀.gpr, g₉, shl_nat (by rw [e₈]; omega), e₈]
  refine wp_stloc i₁₀ (d := strideOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ _ _ =>
    k s₁₁ i₁₁ ⟨?_, ?_, ?_⟩
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide),
      lw_mem u₈.mem, v₇]
    exact ofNat_toNat c₆'
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, v₉]
    exact ofNat_toNat e₈
  · rw [v₁₁]
    exact ofNat_toNat e₁₀

end

end VG.Proof.Argon2.RISCV64.Derive
