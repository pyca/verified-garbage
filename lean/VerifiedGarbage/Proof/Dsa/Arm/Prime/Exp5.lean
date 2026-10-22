module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Exp4
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Loads

/-! # A candidate on ARMv7: `sigMasks` and `powWord` as a piece (`St.psigPow`) -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

/-- The header words the masks and the word `2^(t mod 64)` set, from `t`. -/
def VSg (t : Nat) (V : Nat → Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd V sS1 (sg (BitVec.ofNat 32 t)).1.toNat) sS2 (sg (BitVec.ofNat 32 t)).2.1.toNat)
    sS3 (sg (BitVec.ofNat 32 t)).2.2.toNat) sLo (pw (BitVec.ofNat 32 t)).1.toNat) sHi (pw (BitVec.ofNat 32 t)).2.toNat

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem St.psigPow (cert : Cert (.block (sigMasks ++ powWord))) (ht : sTc ∈ LS) (hlt : ∀ σ, E σ → V σ sTc < 2 ^ 32) :
    VP (St P E A L V LS) (.block (sigMasks ++ powWord))
      (St P E A L (fun σ => VSg (V σ sTc) (V σ)) (sHi :: sLo :: sS3 :: sS2 :: sS1 :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    have tl := hlt σ e
    generalize et : V σ sTc = t at tl
    have ht' : V σ sTc = t := et
    simp only [sigMasks, powWord, VG.Impl.Bignum.Arm.TwoPower.code, List.cons_append, List.nil_append, List.append_assoc]
    refine h.ldr hw ht (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    rw [ht'] at u1
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => wp_dp (op2_imm (by decide)) fun s3 u3 =>
      wp_mov (op2_lsr (by decide)) fun s4 u4 => wp_dp (op2_imm (by decide)) fun s5 u5 =>
      wp_dp (op2_imm (by decide)) fun s6 u6 => wp_mov (op2_lsr (by decide)) fun s7 u7 =>
      wp_dp (op2_imm (by decide)) fun s8 u8 => wp_dp (op2_imm (by decide)) fun s9 u9 =>
      wp_mov (op2_lsr (by decide)) fun s10 u10 => wp_dp (op2_imm (by decide)) fun s11 u11 => ?_
    have k11 : Rest [.r1, .r2, .r3, .r4] s1 s11 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans ((u7.rest (by simp)).trans
      ((u8.rest (by simp)).trans ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans (u11.rest (by simp))))))))))
    have m11 : s11.mem = s1.mem := by
      rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
    have h11 := h1.of_rest k11 m11
    have hw11 := hw1.rest k11
    -- The masks.
    have x3 : s2.gpr .r1 = BitVec.ofNat 32 t &&& 3 := by rw [u2.gpr, dpVal, u1.gpr]
    have z4 : s4.gpr .r2 = (sg (BitVec.ofNat 32 t)).2.2 := by
      rw [u4.gpr, u3.gpr, dpVal, x3]; rfl
    have x7 : s7.gpr .r3 = ((BitVec.ofNat 32 t &&& 3 ^^^ 1) - 1) >>> 31 := by
      rw [u7.gpr, u6.gpr, dpVal, u5.gpr, dpVal, u4.other _ (by decide), u3.other _ (by decide), x3]
    have x10 : s10.gpr .r4 = ((BitVec.ofNat 32 t &&& 3 ^^^ 3) - 1) >>> 31 := by
      rw [u10.gpr, u9.gpr, dpVal, u8.gpr, dpVal, u7.other _ (by decide), u6.other _ (by decide),
        u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), x3]
    have s1v : s11.gpr .r3 = (sg (BitVec.ofNat 32 t)).1 := by
      rw [u11.gpr, dpVal, u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), x7]; rfl
    refine h11.str hw11 (d := sS1) (by decide) fun s12 h12 hw12 m12 => ?_
    rw [s1v] at h12
    refine wp_dp (op2_reg _ _) fun s13 u13 => ?_
    have h13 := h12.of_rest (u13.rest (ws := [.r4]) (by simp)) u13.mem
    have hw13 := hw12.of_upd u13 (by decide) (by decide) (by decide)
    have s2v : s13.gpr .r4 = (sg (BitVec.ofNat 32 t)).2.1 := by
      rw [u13.gpr, dpVal, m12.gpr, u11.other _ (by decide), x10, u11.other _ (by decide), u10.other _ (by decide),
        u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
        u5.other _ (by decide), z4]; rfl
    refine h13.str hw13 (d := sS2) (by decide) fun s14 h14 hw14 m14 => ?_
    rw [s2v] at h14
    have s3v : s14.gpr .r2 = (sg (BitVec.ofNat 32 t)).2.2 := by
      rw [m14.gpr, u13.other _ (by decide), m12.gpr, u11.other _ (by decide), u10.other _ (by decide),
        u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
        u5.other _ (by decide), z4]
    refine h14.str hw14 (d := sS3) (by decide) fun s15 h15 hw15 m15 => ?_
    rw [s3v] at h15
    -- The word.
    refine h15.ldr hw15 (by simp [ht]) (r := .r1) (by decide) fun s16 h16 hw16 u16 => ?_
    have t16 : upd (upd (upd (V σ) sS1 (sg (BitVec.ofNat 32 t)).1.toNat) sS2 (sg (BitVec.ofNat 32 t)).2.1.toNat)
        sS3 (sg (BitVec.ofNat 32 t)).2.2.toNat sTc = t := by
      simp (config := {decide := true}) only [upd, ↓reduceIte]; exact ht'
    rw [t16] at u16
    refine wp_dp (op2_imm (by decide)) fun s17 u17 => wp_mov (op2_imm (by decide)) fun s18 u18 => ?_
    have x18 : s18.gpr .r1 = BitVec.ofNat 32 t &&& 63 := by rw [u18.other _ (by decide), u17.gpr, dpVal, u16.gpr]
    refine powStep_ok (by decide) x18 u18.gpr fun s19 k19 m19 x19 y19 => ?_
    refine powStep_ok (by decide) x19 y19 fun s20 k20 m20 x20 y20 => ?_
    refine powStep_ok (by decide) x20 y20 fun s21 k21 m21 x21 y21 => ?_
    refine powStep_ok (by decide) x21 y21 fun s22 k22 m22 x22 y22 => ?_
    refine powStep_ok (by decide) x22 y22 fun s23 k23 m23 x23 y23 => ?_
    refine wp_mov (op2_lsr (by decide)) fun s24 u24 => wp_dp (op2_imm (by decide)) fun s25 u25 =>
      wp_mov (op2_imm (by decide)) fun s26 u26 => wp_dp (op2_reg _ _) fun s27 u27 =>
      wp_dp (op2_reg _ _) fun s28 u28 => wp_dp (op2_reg _ _) fun s29 u29 => ?_
    have k29 : Rest [.r1, .r2, .r3, .r4] s16 s29 :=
      ((u17.rest (by simp)).trans ((u18.rest (by simp)).trans (((k19.trans (k20.trans (k21.trans (k22.trans
        k23))))).mono (by simp)))).trans ((u24.rest (by simp)).trans ((u25.rest (by simp)).trans
        ((u26.rest (by simp)).trans ((u27.rest (by simp)).trans ((u28.rest (by simp)).trans (u29.rest (by simp)))))))
    have m29 : s29.mem = s16.mem := by
      rw [u29.mem, u28.mem, u27.mem, u26.mem, u25.mem, u24.mem, m23, m22, m21, m20, m19, u18.mem, u17.mem]
    have h29 := h16.of_rest k29 m29
    have hw29 := hw16.rest k29
    have b25 : s25.gpr .r3 = (BitVec.ofNat 32 t &&& 63) >>> 5 &&& 1 := by
      rw [u25.gpr, dpVal, u24.gpr, x23]
    have hi28 : s28.gpr .r3 = (pw (BitVec.ofNat 32 t)).2 := by
      rw [u28.gpr, dpVal, u27.gpr, dpVal, u26.gpr, u26.other _ (by decide), b25, u27.other _ (by decide),
        u26.other _ (by decide), u25.other _ (by decide), u24.other _ (by decide), y23]; rfl
    have lo29 : s29.gpr .r2 = (pw (BitVec.ofNat 32 t)).1 := by
      rw [u29.gpr, dpVal, u28.other _ (by decide), u27.other _ (by decide), u26.other _ (by decide),
        u25.other _ (by decide), u24.other _ (by decide), y23, hi28]; rfl
    have hi29 : s29.gpr .r3 = (pw (BitVec.ofNat 32 t)).2 := by rw [u29.other _ (by decide), hi28]
    refine h29.str hw29 (d := sLo) (by decide) fun s30 h30 hw30 m30 => ?_
    rw [lo29] at h30
    refine h30.str hw30 (d := sHi) (by decide) fun s31 h31 hw31 m31 => WP.block_nil ⟨e, ?_, hw31⟩
    rw [m30.gpr, hi29] at h31
    show KS P σ (A σ) L (VSg (V σ sTc) (V σ)) _ s31
    rw [ht']
    exact h31

end

end VG.Proof.Dsa.Arm.Prime
