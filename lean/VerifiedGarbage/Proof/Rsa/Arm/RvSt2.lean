module

public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint3
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: more steps of the candidates as pieces

`g` into `[mG]` (`St.pstoreG`), the count of bits `c` into `sCnt`
(`St.pcnt0`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem relCT_assoc' {Q R : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa Q (.seq a (.seq b c)) R) : RelCT isa Q (.seq (.seq a b) c) R := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem VP.assoc' {F G : State → State → Prop} {a b c : Prog isa} (h : VP F (.seq a (.seq b c)) G) :
    VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_assoc' h.ct⟩

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- `[mG] := sCand + 2`, from `[mG] = 0`. -/
theorem St.pstoreG (hc : sCand ∈ LS) (hmG : mG ∈ L)
    (hv : ∀ σ, E σ → V σ sCand + 2 < 2 ^ 32 ∧ A σ mG = 0) (hlW : ∀ j ∈ LW, mG / 2 ≠ j) :
    VP (St P E A L AW LW V LS P.w nArr) (.block storeG)
      (St P E (fun σ => upd (A σ) mG (V σ sCand + 2)) (mG :: L) AW LW V LS P.w nArr) := by
  refine VP.ctx storeG_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  obtain ⟨lt, z⟩ := hv σ e
  refine ptr_ok hw (r := .r0) (by decide) (j := mG) (by decide) fun s1 p1 r1 m1 hw1 => ?_
  obtain ⟨h1, -⟩ := h.reg hw r1 m1
  have hm1 := hm.of_rest r1 m1
  refine h1.ldrSlot hw1 hc (r := .r1) (by decide) fun s2 h2 hw2 u2 => ?_
  have hm2 := hm1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hw3⟩ := h2.reg hw2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  have hm3 := hm2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine storeLow_ok hw3 (j := mG) (by decide) (by rw [u3.other _ (by decide), u2.other _ (by decide), p1])
    fun t ht kt vt rt _ => WP.block_nil ⟨e, h3.write_w kt (by decide) (by simp) (by rw [rt.gpr _ (by simp), h3.r8])
      rt.sp rt.rd rt.wr ?_ hlW (by simp), hm3.of_keep1 h3.bs kt (by decide) (by decide) (by simp) rt.sp rt.rd rt.wr,
      ht⟩
  rw [vt, h3.arrs mG hmG, z, Nat.zero_div, Nat.mul_zero, Nat.add_zero, u3.gpr, dpVal, u2.gpr,
    show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lt]

/-- `e_len` and `d_len` from the stack. -/
theorem St.pldrLens {v N : Nat} :
    VP (St P E A L AW LW V LS v N) (.block ([(Reg.r1, aoEl), (Reg.r2, aoDl)].map fun p => Instr.ldrSp p.1 p.2))
      (fun σ s => St P E A L AW LW V LS v N σ s ∧ s.gpr .r1 = BitVec.ofNat 32 P.el ∧
        s.gpr .r2 = BitVec.ofNat 32 P.dl) := by
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hm, hw⟩ => ?_
  · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
  · refine h.bs.ldrSp (o := aoEl) (by decide) (by decide) (by decide) fun s1 u1 => ?_
    have r1 := u1.rest (ws := [.r1]) (by simp)
    obtain ⟨h1, hw1⟩ := h.reg hw r1 u1.mem
    refine h1.bs.ldrSp (o := aoDl) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
    have r2 := u2.rest (ws := [.r2]) (by simp)
    obtain ⟨ht, hwt⟩ := h1.reg hw1 r2 u2.mem
    exact ⟨⟨e, ht, (hm.of_rest r1 u1.mem).of_rest r2 u2.mem, hwt⟩,
      by rw [u2.other _ (by decide), u1.gpr, h.bs.pre.aEl], by rw [u2.gpr, h.bs.pre.aDl]⟩

/-- `sCnt := c`. -/
theorem St.pcntTail {v N : Nat} :
    VP (fun σ s => St P E A L AW LW V LS v N σ s ∧ s.gpr .r1 = BitVec.ofNat 32 P.el ∧
        s.gpr .r2 = BitVec.ofNat 32 P.dl) (.block cntTail)
      (St P E A L AW LW (fun σ => upd (V σ) sCnt P.c) (sCnt :: LS) v N) := by
  refine VP.ctx cntTail_taint (fun _ _ h => h.1.2.2.2) fun σ s ⟨⟨e, h, hm, hw⟩, r1, r2⟩ => ?_
  have el2 := h.bs.pre.el2; have dl2 := h.bs.pre.dl2; have k2 := h.bs.pre.k2
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  have r12 := (u1.rest (ws := [.r1]) (by simp)).trans (u2.rest (by simp))
  have m12 := u2.mem.trans u1.mem
  obtain ⟨h2, hw2⟩ := h.reg hw r12 m12
  refine h2.strSlot_m (hm.of_rest r12 m12) hw2 (d := sCnt) (r := .r1) (by decide)
    fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  have c : (s2.gpr .r1).toNat = P.c := by
    rw [u2.gpr, u1.gpr, dpVal, r1, r2]
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [RP.c]
    omega
  rw [c] at ht; exact ht

end

end VG.Proof.Rsa.Arm.Recover
