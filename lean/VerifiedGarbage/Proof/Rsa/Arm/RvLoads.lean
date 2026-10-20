module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs
public import VerifiedGarbage.Proof.Rsa.Arm.RvBase
public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

import VerifiedGarbage.Proof.Rsa.Arm.RvLoad
import VerifiedGarbage.Proof.Rsa.Arm.RvCtx
import VerifiedGarbage.Proof.Rsa.Arm.RvMM
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.RvKS
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-! # `vg_rsa_recover_primes` on ARMv7: the working space set up, and the numbers read

`LS P σ A s`: the working space with `w` words, `w` in the division's header,
and every array's `w + 2` words holding `A`. `loads_vp`: from the start of
the body, every array is zero but `n`, `e` and `d` (`Aload`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

structure LS (P : RP) (σ : State) (A : Nat → Nat) (s : State) : Prop where
  bs : Bs P σ s
  ws : Ws s P.B P.Z P.w nArr
  cnt : s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w
  full : ∀ j < nArr, val32 s.mem (State.addr P.B) (arr P.w j) (P.w + 2) = A j

/-- The arrays after the loads. -/
def Aload (P : RP) (σ : State) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) aN P.n) (2 * wE) P.e) (2 * wD) (dv P σ)

section
variable {P : RP}

/-- `setupK` after the base and `n_len` are loaded. -/
theorem setupKTail_ok {σ s : State} (h : Bs P σ s) (r8 : s.gpr .r8 = P.B) (r9 : s.gpr .r9 = BitVec.ofNat 32 P.K) :
    WP isa (.block setupKTail) s fun t => Bs P σ t ∧ Ws t P.B P.Z P.w nArr ∧
      t.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w ∧
      t.gpr .r0 = P.B + BitVec.ofNat 32 hdr ∧ t.gpr .lr = BitVec.ofNat 32 (nArr * (P.w + 2)) ∧
      t.gpr .r3 = 0 ∧ Outside (State.addr P.B) 16 4 s.mem t.mem := by
  have pre := h.pre
  have sz := pre.sizes
  have k1 := pre.k1; have k2 := pre.k2
  have wl := sz.wle
  unfold setupKTail
  simp only [List.cons_append, List.append_assoc]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  have h9 : s4.gpr .r9 = BitVec.ofNat 32 P.w := by
    rw [u4.gpr, dpVal, u3.gpr, u2.gpr, u1.gpr, dpVal, r9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (7 : BitVec 32).toNat = 7 from rfl, show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [RP.w, RP.w6]
    omega
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (by omega) h9 fun s5 h7 r5 m5 => ?_
  have r45 : Rest [.r9, .r7] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (r5.mono (by simp)))))
  have m45 : s5.mem = s.mem := m5.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem)))
  have ws5 : Ws s5 P.B P.Z P.w nArr :=
    ⟨pre.fS, by rw [r45.wr]; exact h.rS_mem, sz.fits, by show 0 < 2 * P.w6 + 2; omega, by omega, h7,
      by rw [r45.gpr _ (by decide), r8], by rw [r5.gpr _ (by decide), h9]⟩
  refine wp_strSlot ws5 (d := 16) (by decide) fun s6 u6 => ?_
  have ws6 := ws5.of_mupd u6
  have o6 := writeW32_outside s5.mem (State.addr P.B) (d := 16) (s5.gpr .r9) (by decide)
  rw [← u6.mem] at o6
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_mul fun s9 u9 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u11 => WP.block_nil ?_
  have rt : Rest [.r0, .lr, .r3] s6 t := (u7.rest (by simp)).trans ((u8.rest (by simp)).trans
    ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans (u11.rest (by simp)))))
  have mt : t.mem = s6.mem := by rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]
  have ot : Outside (State.addr P.B) 16 4 s.mem t.mem := by rw [mt, ← m45]; exact o6
  have hz := hdr_Z sz
  refine ⟨h.of_frame (fun x hx => ot x (.inr ?_)) (by rw [rt.sp, u6.sp, r45.sp]) (by rw [rt.rd, u6.rd, r45.rd])
      (by rw [rt.wr, u6.wr, r45.wr]), ws6.rest rt, ?_, ?_, ?_, by rw [u11.gpr], ot⟩
  · have := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at this
    simp only [ofs, hdr] at *; omega
  · rw [mt, u6.mem, Mem.readW_writeW_self32, ws5.r9]
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr,
      dpVal, u6.gpr, ws5.r8]
  · rw [u11.other _ (by decide), u10.gpr, u9.gpr, u8.gpr, u8.other _ (by decide), u7.other _ (by decide), u6.gpr,
      ws5.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArr, S]
    rw [Nat.mod_eq_of_lt (a := 44) (by decide), Nat.mod_eq_of_lt (a := 4 * (P.w + 2)) (by omega),
      Nat.mod_eq_of_lt (a := 44 * (4 * (P.w + 2))) (by omega), Nat.mod_eq_of_lt (a := 44 * (P.w + 2)) (by omega)]
    omega

theorem zero_ls {σ s : State} (h : Bs P σ s) (hw : Ws s P.B P.Z P.w nArr)
    (cnt : s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w)
    (p0 : s.gpr .r0 = P.B + BitVec.ofNat 32 hdr) (plr : s.gpr .lr = BitVec.ofNat 32 (nArr * (P.w + 2)))
    (r3 : s.gpr .r3 = 0) : WP isa VG.Impl.Bignum.Arm.zero s (LS P σ fun _ => 0) := by
  have sz := h.pre.sizes
  have fits := sz.fits
  have nfit : hdr + 4 * (nArr * (P.w + 2)) ≤ P.Z := by
    have e : arr P.w nArr = hdr + 4 * (nArr * (P.w + 2)) := by
      show hdr + nArr * (4 * (P.w + 2)) = _; rw [Nat.mul_left_comm]
    rw [← e]; exact fits
  refine WP.mono (zero_ok s (base := P.B) (size := P.Z) (o := hdr) (n := nArr * (P.w + 2))
    ⟨h.pre.fS, nfit, ⟨P.rS, h.rS_mem, Region.contains_self _ _⟩⟩ (Nat.mul_pos (by decide) (by omega)) p0 plr r3)
    fun t inv => ?_
  refine ⟨h.of_frame (fun x hx => inv.outside x (.inr ?_)) inv.rest.sp inv.rest.rd inv.rest.wr,
    hw.rest inv.rest, ?_, fun j hj => ?_⟩
  · have := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at this
    simp only [ofs] at *; omega
  · refine (BitVec.eq_of_toNat_eq ?_).trans cnt
    exact inv.outside.w32 (d := 16) (by simp only [hdr]; omega) (by decide)
  · have := VG.Proof.Rsa.Arm.CrtValues.val32_zero_part inv.value (a := j * (P.w + 2)) (c := P.w + 2) (by
      have := Nat.mul_le_mul_right (P.w + 2) (show j + 1 ≤ nArr by omega)
      rw [Nat.succ_mul] at this; omega)
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-- `loadArg o j`: array `j` := the number whose pointer and length are the
frame words `o` and `o + 4`. -/
theorem loadArg_vp {o j : Nat} {E : State → Prop} {A : State → Nat → Nat} {src : BitVec 32} {k : Nat}
    (cert : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.CrtValues.load j) hc).isSome = true)
    (hj : j < nArr) (ho : 56 ≤ o) (ho' : o + 8 ≤ 88) (ho4 : o % 4 = 0)
    (hin : ∀ σ, In P σ → fw σ.mem P o = src ∧ fw σ.mem P (o + 4) = BitVec.ofNat 32 k ∧
      InRegions (σ.rd ++ σ.wr) (State.addr src) k ∧ Region.Disjoint ⟨State.addr src, k⟩ P.rS ∧
      Region.Disjoint ⟨State.addr src, k⟩ P.rFr ∧ src.toNat + k ≤ 2 ^ 32 ∧ 0 < k ∧ k ≤ P.K) :
    VP (fun σ s => E σ ∧ LS P σ (A σ) s) (seqs (loadArg o j)) (fun σ s => E σ ∧
      LS P σ (upd (A σ) j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr src) k))) s) := by
  simp only [loadArg, seqs]
  refine VP.seq (G := fun σ s => (E σ ∧ LS P σ (A σ) s) ∧ s.gpr .r4 = src ∧ s.gpr .r6 = BitVec.ofNat 32 k) ?_ ?_
  · show VP _ (.block ([(Reg.r4, o), (Reg.r6, o + 4)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
    · rw [h₁.2.bs.sp, h₁.2.bs.pre.sp, h₂.2.bs.sp, h₂.2.bs.pre.sp]
    · obtain ⟨e1, e2, -⟩ := hin σ h.bs.pre
      refine h.bs.ldrSp (o := o) (by omega) (by omega) ho4 fun s1 u1 => ?_
      have r1 := u1.rest (ws := [.r4]) (by simp)
      have b1 := h.bs.of_rest r1 u1.mem
      refine b1.ldrSp (o := o + 4) (by omega) (by omega) (by omega) fun t u2 => WP.block_nil ?_
      have r2 := u2.rest (ws := [.r6]) (by simp)
      refine ⟨⟨e, ⟨b1.of_rest r2 u2.mem, (h.ws.rest r1).rest r2, by rw [u2.mem, u1.mem]; exact h.cnt,
        by rw [u2.mem, u1.mem]; exact h.full⟩⟩, by rw [u2.other .r4 (by simp), u1.gpr, e1], by rw [u2.gpr, e2]⟩
  · refine VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h⟩, p4, p6⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]
      · rw [h₁.1.2.ws.r7, h₂.1.2.ws.r7]
      · rw [h₁.1.2.ws.r8, h₂.1.2.ws.r8]
      · rw [h₁.1.2.ws.r9, h₂.1.2.ws.r9]
    · obtain ⟨-, -, rd, sS, sF, fit, hk, hkK⟩ := hin σ h.bs.pre
      refine WP.mono (load_ok' h.bs h.ws hj rd sS sF fit hk hkK p4 p6) fun t ⟨bt, wt, k, v, r⟩ => ⟨e, bt, wt, ?_, ?_⟩
      · refine (BitVec.eq_of_toNat_eq ?_).trans h.cnt
        exact k.slot (e := 16) (by decide) (by simp)
      · intro i hi
        by_cases e' : i = j
        · subst e'; rw [upd_self, v]
        · rw [upd_ne _ _ e', ← h.full i hi]
          refine k.full (fun x hx ex => e' (by simp at hx; rw [← ex, hx])) (by simp) (fit_w h.bs.pre.sizes hi)

end

end VG.Proof.Rsa.Arm.Recover
