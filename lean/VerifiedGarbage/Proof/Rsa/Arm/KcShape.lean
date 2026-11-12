module

public import VerifiedGarbage.Proof.Rsa.Arm.KcFnBase
public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck

/-! # The checks of an RSA key on ARMv7: whether the key is balanced

`shape_ok`: `shape` sets Z when `p` and `q` both have `2 w` bytes and `w` is
even (`w` the modulus' words), and changes only `r0`–`r3` and the flags.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.X25519.Arm

/-- `p` and `q` of `2 w` bytes, `w` even. -/
abbrev Balanced (iS : Nat) (σ : State) : Prop :=
  (stackArg σ 3).toNat = 2 * (geo iS σ).w ∧ (stackArg σ 5).toNat = 2 * (geo iS σ).w ∧ (geo iS σ).w % 2 = 0

theorem shape_z {K P Q : BitVec 32} (hK : K.toNat ≤ 1024) :
    ((((P ^^^ (((K + 3) >>> 2) <<< 1)) ||| (Q ^^^ (((K + 3) >>> 2) <<< 1))) ||| (((K + 3) >>> 2) &&& 1)) - 0
        == 0) =
      decide (P.toNat = 2 * ((K.toNat + 3) / 4) ∧ Q.toNat = 2 * ((K.toNat + 3) / 4) ∧ (K.toNat + 3) / 4 % 2 = 0) := by
  have hW : (K + 3) >>> 2 = BitVec.ofNat 32 ((K.toNat + 3) / 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (3 : BitVec 32).toNat = 3 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have h2 : BitVec.ofNat 32 ((K.toNat + 3) / 4) <<< 1 = BitVec.ofNat 32 (2 * ((K.toNat + 3) / 4)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have h1 : BitVec.ofNat 32 ((K.toNat + 3) / 4) &&& 1 = BitVec.ofNat 32 ((K.toNat + 3) / 4 % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact Nat.and_one_is_mod _
  have eP : ∀ X : BitVec 32, X = BitVec.ofNat 32 (2 * ((K.toNat + 3) / 4)) ↔ X.toNat = 2 * ((K.toNat + 3) / 4) :=
    fun X => ⟨fun e => by rw [e, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega),
      fun e => BitVec.eq_of_toNat_eq (by rw [e, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm)⟩
  have e0 : BitVec.ofNat 32 ((K.toNat + 3) / 4 % 2) = 0#32 ↔ (K.toNat + 3) / 4 % 2 = 0 :=
    ⟨fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact this, fun e => by rw [e]⟩
  have hz : ∀ x : BitVec 32, (x - 0 == 0) = decide (x = 0#32) := fun x => by
    rw [show x - 0 = x from BitVec.sub_zero x]; cases h : decide (x = 0#32) <;> simp_all
  rw [hW, h2, h1, hz]
  apply Bool.eq_iff_iff.mpr
  simp only [ decide_eq_true_eq, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, eP, e0, and_assoc]

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

/-- `shape`: Z if the key is balanced; only `r0`–`r3` and the flags change. -/
theorem shape_ok {σ s : State} (h : FnBase nA iS ins σ s) (h11 : s.gpr .r11 = σ.gpr .r1) (h5 : 5 < nA)
    {Q : State → Prop}
    (k : ∀ t, FnBase nA iS ins σ t → Rest [.r0, .r1, .r2, .r3] s t → t.mem = s.mem →
      t.z = decide (Balanced iS σ) → Q t) :
    WP isa (.block (shape 12 20)) s Q := by
  have kb := h.pre.kb
  unfold shape VG.Impl.Rsa.Arm.KeyDiv.shape
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have b2 := h.of_rest ((u1.rest (ws := [.r0, .r1, .r2, .r3]) (by simp)).trans (u2.rest (by simp)))
    (u2.mem.trans u1.mem)
  refine b2.ldrSp (i := 3) (by omega) (by decide) fun s3 b3 u3 => ?_
  refine b3.ldrSp (i := 5) h5 (by decide) fun s4 b4 u4 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_dp (op2_imm (by decide)) fun s9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun s10 u10 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  have r4 : Rest [.r0, .r1, .r2, .r3] s2 s4 := (u3.rest (by simp)).trans (u4.rest (by simp))
  have r10 : Rest [.r0, .r1, .r2, .r3] s4 t :=
    (((((((u5.rest (by simp)).trans (u6.rest (by simp))).trans (u7.rest (by simp))).trans (u8.rest (by simp))).trans
      (u9.rest (by simp))).trans (u10.rest (by simp))).trans (ut.rest _))
  have m10 : t.mem = s4.mem := by
    rw [ut.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem]
  refine k t (b4.of_rest r10 m10) (((u1.rest (by simp)).trans (u2.rest (by simp))).trans (r4.trans r10))
    (by rw [m10, u4.mem, u3.mem, u2.mem, u1.mem]) ?_
  have e0 : s10.gpr .r0 = (((stackArg σ 3 ^^^ (((σ.gpr .r1 + 3) >>> 2) <<< 1)) |||
      (stackArg σ 5 ^^^ (((σ.gpr .r1 + 3) >>> 2) <<< 1))) ||| (((σ.gpr .r1 + 3) >>> 2) &&& 1)) := by
    simp (disch := decide) only [u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr,
      u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, h11,
      dpVal]
  rw [zt, e0]
  exact shape_z kb.2

end

end VG.Proof.Rsa.Arm.KeyCheck
