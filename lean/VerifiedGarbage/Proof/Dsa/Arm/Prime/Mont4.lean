module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp7

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont3
import VerifiedGarbage.Proof.Bignum.Arm.Setup
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint6
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont1
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.RvMont4

/-! # A candidate on ARMv7: Montgomery multiplication's base and header

`montSet`: its base into frame word 0 and `r0`, `w` into `r7`
(`montSet_vp`); `setup` (`setup_vp`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The stage of the exponent, as a stage of the key working space alone. -/
abbrev KX (P : CP) (E : State → Prop) (L : List Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (AX P σ) L (V3 P σ) [sUsed] s

/-- Before `setup`. -/
abbrev SB (P : CP) (E : State → Prop) (σ s : State) : Prop :=
  KX P E LX σ s ∧ s.gpr .r0 = P.M0 ∧ s.gpr .r7 = BitVec.ofNat 32 P.w ∧ s.gpr .r3 = 0 ∧
    s.mem.readW (State.addr P.sp) 32 = P.M0

/-- After `setup`. -/
abbrev SC (P : CP) (E : State → Prop) (σ s : State) : Prop :=
  KX P E LX σ s ∧ Layout s.mem (State.addr P.M0) P.lenM ∧ wOf s.mem (State.addr P.M0) = P.w ∧
    s.gpr .r0 = P.M0 ∧ s.mem.readW (State.addr P.sp) 32 = P.M0

section
variable {P : CP}

theorem montSet_eq : montSet = (ptr .r0 mBase ++ ([.dp .sub .r0 .r0 (.imm 256)] : List Instr)) ++
    (.addSp .r12 0 :: [.str .r0 .r12 0, .ldrSp .r7 foL, .mov .r7 (.shifted .r7 .lsr 3), .mov .r3 (.imm 0)]) := rfl

theorem In.rW0_rS {σ : State} (pre : In P σ) : P.rS.Disjoint P.rW0 :=
  pre.sF.sub_right (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 88) (by decide) |>
    fun h => by simpa using h)

/-- `montSet`. -/
theorem montSet_vp {E : State → Prop} : VP (SX P E) (.block montSet) (SB P E) := by
  rw [montSet_eq]
  refine VP.block_append (G := fun σ s => SX P E σ s ∧ s.gpr .r0 = P.M0)
    (VP.kv montHead_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_) ?_
  · have pre := h.pre
    refine ptr_ok hw (r := .r0) (by decide) (by decide) fun s1 p1 r1 m1 hw1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => WP.block_nil ⟨⟨e, ?_, ?_⟩, ?_⟩
    · exact h.of_rest ((r1.mono (by simp)).trans (u2.rest (ws := [.r0]) (by simp))) (u2.mem.trans m1)
    · exact hw1.of_upd u2 (by decide) (by decide) (by decide)
    · have e := pre.oM_eq
      have hm : arr P.W mBase - 256 = P.oM := by omega
      rw [u2.gpr, dpVal, p1, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl,
        VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega), hm]
  · refine VP.stk (by decide) (by decide) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, r0⟩ => ?_
    · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
    have pre := h.pre
    have spf := pre.spFit
    have sp : s.sp = P.sp := h.sp.trans pre.sp
    refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u1 h1 => ?_
    refine wp_str (a := State.addr P.sp) (by decide)
      (by rw [h1.gpr, sp, BitVec.add_zero, BitVec.add_zero]) ⟨P.rFr,
        by rw [h1.wr, h.wr, pre.wr]; simp, by
          simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩ fun u2 m2 => ?_
    have v0 : u1.gpr .r0 = P.M0 := by rw [h1.other _ (by decide), r0]
    have h2 := h.w0 (P.M0) (by rw [m2.mem, h1.mem, v0]) (by rw [m2.sp, h1.sp]) (by rw [m2.rd, h1.rd])
      (by rw [m2.wr, h1.wr])
    have sv : u2.mem.readW (State.addr P.sp) 32 = P.M0 := by
      rw [m2.mem, Mem.readW_writeW_self32, v0]
    refine h2.ldrSp (o := foL) (by decide) fun u3 v3 => ?_
    rw [pre.wL] at v3
    refine wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mov (op2_imm (by decide)) fun t v5 => WP.block_nil ?_
    have r5 : Rest [.r7, .r3] u2 t := (v3.rest (by simp)).trans ((v4.rest (by simp)).trans (v5.rest (by simp)))
    have m5 : t.mem = u2.mem := by rw [v5.mem, v4.mem, v3.mem]
    refine ⟨⟨e, h2.of_rest r5 m5⟩, ?_, ?_, v5.gpr, by rw [m5]; exact sv⟩
    · rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), m2.gpr, v0]
    · rw [v5.other _ (by decide), v4.gpr, v3.gpr]
      apply BitVec.eq_of_toNat_eq
      have := pre.k2
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [CP.w]; omega

/-- `setup`. -/
theorem setup_vp {E : State → Prop} : VP (SB P E) VG.Impl.Bignum.Arm.setup (SC P E) := by
  refine VP.of_ct (fun σ₁ σ₂ s t tr1 tr2 u v h e1 e2 =>
    ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.2.1.trans h.2.2.1.symm) e1 e2, trivial⟩)
    fun σ s ⟨⟨e, h⟩, r0, r7, r3, sv⟩ => ?_
  have pre := h.pre
  have hw := pre.w4
  refine WP.mono (setup_ok s (pre.workspaceM h.wr) (by omega) (by omega)
    (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes, CP.lenM]; omega) r0 r7 r3)
    fun t ⟨lay, wd, t0, outs, rest⟩ => ⟨⟨e, ?_⟩, lay, wd, t0, ?_⟩
  · have f := frame_of_outs (n := 256) outs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> decide)
    have k := keep_of_frameH pre f
    refine h.core k (by simp only [List.mem_range'_1]; intro j hj; simp only [nArr]; omega) (by simp) rest.sp rest.rd
      rest.wr (h.arrs_keep k (fun j hj hj' => by
        simp only [List.mem_range'_1] at hj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [mBase, aCm1, aTwo, aOne, aC] at hj' <;> omega)
        (by simp)) (h.sl_keep k (by simp) (by simp)) h.live_lt h.ls_ok
  · have f := frame_of_outs (n := 256) outs (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> decide)
    rw [← sv]
    refine f.readW (r := P.rW0) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    refine pre.rW0_rM.sub_right ?_
    show Region.Sub ⟨State.addr P.M0, 256⟩ ⟨State.addr P.M0, 8 * P.lenM⟩
    have := Offset.sub_base (State.addr P.M0) (d := 0) (n := 256) (k := 8 * P.lenM) (by simp only [CP.lenM]; omega)
    simpa only [BitVec.add_zero] using this

end

end VG.Proof.Dsa.Arm.Prime
