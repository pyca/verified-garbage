module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr6
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr2
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont8
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont5
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.MillerRabin.Arm.Win
import VerifiedGarbage.Proof.Rsa.Arm.RvCand1

/-! # A candidate on ARMv7: the round on the witness (`mrCall_vp`)

The witness into Montgomery multiplication's array 1, times `R² mod c` into
its array 5 (its Montgomery form), the round's working space (`wsLen_vp`),
the round (`round_vp`), the context, and its result into `sF`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Operand)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem wsLen_eq : wsLen = ([(Reg.r0, 0), (Reg.r1, aoSl), (Reg.r2, foL)].map fun p => Instr.ldrSp p.1 p.2) ++
    ([.mov .r2 (.shifted .r2 .lsr 3), .mov .r3 (.imm 21), .mul .r2 .r2 .r3, .dp .add .r2 .r2 (.imm 30),
      .dp .sub .r1 .r1 (.reg .r2)] : List Instr) := rfl

/-- Before the round: Montgomery multiplication's array 5 is `b σ` in Montgomery form. -/
abbrev SR (P : CP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (b : State → Nat) (σ s : State) : Prop :=
  (E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧ numAt s.mem (State.addr P.M0) P.w 5 < cv P σ ∧
    numAt s.mem (State.addr P.M0) P.w 5 = b σ % cv P σ * 2 ^ (64 * P.w) % cv P σ

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- The round's working space: Montgomery multiplication's base into `r0`, and its 64-bit words into `r1`. -/
theorem wsLen_vp {b : State → Nat} :
    VP (SR P E A L V LS b) (.block wsLen)
      (fun σ s => SR P E A L V LS b σ s ∧ s.gpr .r0 = P.M0 ∧ s.gpr .r1 = BitVec.ofNat 32 P.lenR) := by
  rw [wsLen_eq]
  refine VP.block_append (G := fun σ s => SR P E A L V LS b σ s ∧ s.gpr .r0 = P.M0 ∧
    s.gpr .r1 = BitVec.ofNat 32 P.SL ∧ s.gpr .r2 = BitVec.ofNat 32 P.L) ?_ ?_
  · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp])
      fun σ s ⟨⟨e, h⟩, m, lt, val⟩ => ?_
    have spw : s.sp = P.sp := h.sp.trans h.pre.sp
    refine h.bk.ldrSpV (o := 0) (by decide) (by decide) (m.toMSp.fw0 spw) fun s1 u1 => ?_
    have h1 := h.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem
    refine h1.ldrSp (o := aoSl) (by decide) fun s2 u2 => ?_
    have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
    refine h2.ldrSp (o := foL) (by decide) fun s3 u3 => WP.block_nil ?_
    have h3 := h2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    exact ⟨⟨⟨e, h3⟩, ((m.of_upd u1).of_upd u2).of_upd u3, by rw [m3]; exact lt, by rw [m3]; exact val⟩,
      by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr],
      by rw [u3.other _ (by decide), u2.gpr, h.pre.aSl],
      by rw [u3.gpr, h.pre.wL]⟩
  · refine VP.taint [] wsTail_taint (fun _ _ _ _ _ _ r hr => by simp at hr)
      fun σ s ⟨⟨⟨e, h⟩, m, lt, val⟩, r0, r1, r2⟩ => ?_
    have pre := h.pre
    refine wp_mov (op2_lsr (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => wp_mul fun s3 u3 =>
      wp_dp (op2_imm (by decide)) fun s4 u4 => wp_dp (op2_reg _ _) fun s5 u5 => WP.block_nil ?_
    have rs : Rest [.r1, .r2, .r3] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))))
    have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨⟨e, h.of_rest rs m5⟩, m.of_rest rs m5, by rw [m5]; exact lt, by rw [m5]; exact val⟩,
      by rw [rs.gpr _ (by decide), r0], ?_⟩
    rw [u5.gpr, dpVal, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), r1, u4.gpr, dpVal, u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, r2]
    apply BitVec.eq_of_toNat_eq
    have hL := pre.L_eq; have k2 := pre.k2; have lf := pre.lenR_fit; have zl := pre.Z_le
    simp only [CP.lenR, CP.oM, CP.Z, CP.w] at lf zl hL ⊢
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (21 : BitVec 32).toNat = 21 from rfl, show (30 : BitVec 32).toNat = 30 from rfl,
      Nat.mod_eq_of_lt (show P.L < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show P.SL < 2 ^ 32 by omega),
      show P.L / 2 ^ 3 = P.L / 8 from rfl, Nat.mod_eq_of_lt (show P.L / 8 * 21 < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show P.L / 8 * 21 + 30 < 2 ^ 32 by omega)]
    omega

theorem r2v_eq (P : CP) (σ : State) : r2v P σ = 2 ^ (64 * P.w) * 2 ^ (64 * P.w) % cv P σ := by
  rw [← Nat.pow_add, show 64 * P.w + 64 * P.w = 128 * P.w by omega]

/-- The round on the witness of iteration `k`: its result into `sF`. -/
theorem mrCall_vp (v : RoundImpl) {k : Nat} :
    VP (fun σ s => St P E (AF P k) LF (VF P k) LSF σ s ∧ MS P σ s) (seqs (mrCall v.name v.code))
      (fun σ s => St P E (AF P k) LF (fun σ => upd (VF P k σ) sF (rv P σ k)) (sF :: LSF) σ s ∧ MS P σ s) := by
  simp only [mrCall, seqs]
  refine VP.seq (VP.withMS (St.pcopy copy1X_taint (by decide) (by simp) (by decide)) (fun σ s h => h.inSp)
    (copy_keepM (by decide) (by simp) (by decide) (by decide))) ?_
  refine VP.seq St.pmont0 ?_
  refine VP.seq ((St.pmontOp (o := 5) (a := 1) (b := 4) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ (by decide) (by decide)
    (na := fun σ => (wf P σ k).1) (nb := r2v P) (L' := LF) (fun σ s h m => ⟨?_, m.r2⟩)
    (fun σ _ pre => Nat.mod_lt _ (by have := cv_gt pre; omega))
    (fun j hj => ⟨by mem_sub, by mem_sub, by mem_sub, by mem_sub⟩)).mono (fun _ _ h => h)
    (G' := SR P E (fun σ => upd (AF P k σ) (mBase + 1) (AF P k σ aH1)) LF (VF P k) LSF (fun σ => (wf P σ k).1))
    fun σ s ⟨k', m, lt, val⟩ => ⟨k', m, lt, ?_⟩) ?_
  · have pre := h.2.1.pre
    have e := h.2.1.arrs (mBase + 1) (by simp)
    simp only [upd_self] at e
    rw [pre.numAt_eq (by rw [e]; exact wf_lt pre k), e]
  · have pre := k'.2.pre
    have hc := cv_gt pre
    rw [r2v_eq] at val
    exact x5_val (R_coprime pre) lt (by omega) val
  refine VP.seq wsLen_vp ?_
  refine VP.seq (round_vp v (by simp) (by simp) (by simp) (by decide) (fun σ _ => ?_) (fun σ _ => ?_)
    (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AW, AB2]
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AW, AB2]
  · rfl
  have pS : VP (fun σ s => St P E (fun σ => upd (AF P k σ) (mBase + 1) (AF P k σ aH1)) LF (VF P k) LSF σ s ∧
      (MS P σ s ∧ (s.gpr .r0).toNat = if Proof.MillerRabin.Round.round (cv P σ) (wf P σ k).1 then 1 else 0))
      (.block [.str .r0 .r8 sF])
      (fun σ s => St P E (fun σ => upd (AF P k σ) (mBase + 1) (AF P k σ aH1)) LF
        (fun σ => upd (VF P k σ) sF (rv P σ k)) (sF :: LSF) σ s ∧ MS P σ s) :=
    VP.kv strF_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m, r⟩ =>
      h.strM m hw (d := sF) (by decide) fun t ht hwt mt _ => WP.block_nil ⟨⟨e, by rw [r] at ht; exact ht, hwt⟩, mt⟩
  refine (VP.block_append (VP.ctx (X := fun σ s => MS P σ s ∧
      (s.gpr .r0).toNat = if Proof.MillerRabin.Round.round (cv P σ) (wf P σ k).1 then 1 else 0)
      fun σ s t ⟨m, r⟩ mem rest => ⟨m.of_rest rest mem, by rw [rest.gpr _ (by decide)]; exact r⟩) pS).mono
    (fun _ _ h => h)
    fun σ s ⟨h, m⟩ => ⟨h.mono (fun j hj => ⟨hj, upd_ne _ _ (by intro e; rw [e] at hj; revert hj; decide)⟩)
      (fun d hd => ⟨hd, rfl⟩), m⟩

end

end VG.Proof.Dsa.Arm.Prime
