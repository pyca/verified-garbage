module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdSqrtW

import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.RdTaint
import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.MaskRow
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ctx
import VerifiedGarbage.Proof.Framework.Arm.Keep
import VerifiedGarbage.Proof.Rsa.Arm.KdNorm
import VerifiedGarbage.Proof.Rsa.RecoverDet
import Mathlib.Tactic.Ring

/-! # `vg_rsa_recover_primes_det` on ARMv7: the square root's digits

A digit's pieces: the estimate, `T = R - q̂ (2 s β + q̂)` in place by a row, the corrections, each a row
with a scalar 0 or 1, and `D := 2 s'`; and the math of the digits.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Rsa (sub32 b2n)

section
variable {P : RP}

/-! ## The estimate's words -/

theorem shr1_or (x y : BitVec 32) :
    (x >>> 1 ||| y <<< 31).toNat = x.toNat / 2 + y.toNat % 2 * 2 ^ 31 := by
  have hx := x.isLt
  have hb : x.toNat >>> 1 < 2 ^ 31 := by rw [Nat.shiftRight_eq_div_pow]; omega_using []
  have ha : y.toNat <<< 31 % 2 ^ 32 = 2 ^ 31 * (y.toNat % 2) := by rw [Nat.shiftLeft_eq]; omega_using []
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, ha, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt hb, Nat.shiftRight_eq_div_pow]
  omega_using []

/-- `⌊a / 2⌋` from `a`'s four words, `a < 2^97`. -/
theorem half_words {a : Nat} (ha : a < 2 ^ 97) :
    a / 2 = (a % 2 ^ 32 / 2 + a / 2 ^ 32 % 2 ^ 32 % 2 * 2 ^ 31) +
      (a / 2 ^ 32 % 2 ^ 32 / 2 + a / 2 ^ 64 % 2 ^ 32 % 2 * 2 ^ 31) * 2 ^ 32 +
      (a / 2 ^ 64 % 2 ^ 32 / 2 + a / 2 ^ 96 % 2 ^ 32 % 2 * 2 ^ 31) * 2 ^ 64 := by
  omega_using [ha]

end

section
variable {P : RP}

/-- Two header words written, `d := x` and `e := y`. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.slot2 {σ s t : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {d e x y v : Nat}
    (h : KS P σ A live AW liveW V ls s) (k : Keep P.B v [] [d, e] s.mem t.mem)
    (hd : SlotOk d) (he : SlotOk e) (hls : ∀ c ∈ ls, (c + 4 ≤ d ∨ d + 4 ≤ c) ∧ (c + 4 ≤ e ∨ e + 4 ≤ c))
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (ed : slot t.mem P.B d = x) (ee : slot t.mem P.B e = y) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    KS P σ A live AW liveW (upd (upd V d x) e y) (e :: d :: ls) t := by
  have kw : Keep P.B P.w [] [d, e] s.mem t.mem := fun y hy => k y fun r hr => hy r (by simpa [ranges] using hr)
  have hds : ∀ c ∈ [d, e], SlotOk c := fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; rcases hc with rfl | rfl <;> with_reducible assumption
  refine h.core kw (by simp) hds r8 sp rd wr (h.arrs_w kw (by simp) hds) h.live_lt (h.arrsW_w kw (by simp) hds)
    h.liveW_lt (fun c hc => ?_) (fun c hc => ?_)
  · simp only [List.mem_cons] at hc
    by_cases c1 : c = e
    · subst c1; rw [upd_self]; exact ee
    · rw [upd_ne _ _ c1]
      by_cases c2 : c = d
      · subst c2; rw [upd_self]; exact ed
      · rw [upd_ne _ _ c2]
        have hc' : c ∈ ls := by grind
        rw [kw.slot (h.ls_ok c hc').1 (fun f hf => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl
          · exact (hls c hc').1
          · exact (hls c hc').2), h.sl c hc']
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · exact he
    · exact hd
    · exact h.ls_ok c hc

/-- The registers of an offset added to an address (`r1` to `r10`), the same in both runs. -/
theorem offRegs {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat} {k i : Nat} :
    ∀ σ₁ σ₂ s₁ s₂, (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r10 = P.B + BitVec.ofNat 32 k ∧
        s.gpr .r1 = BitVec.ofNat 32 i) σ₁ s₁ →
      (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r10 = P.B + BitVec.ofNat 32 k ∧
        s.gpr .r1 = BitVec.ofNat 32 i) σ₂ s₂ →
      ∀ r ∈ [Reg.r1, .r10, .r7, .r8, .r9], s₁.gpr r = s₂.gpr r := by
  intro σ₁ σ₂ s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.2, h₂.2.2]
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
  · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
  · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]

open VG.Impl.Rsa.Arm.KeyDiv (sD sD1 sV sQ sMk sU0 sU2) in
open VG.Proof.Rsa.Arm.KeyDiv (quot_ok refine3_ok quotRegs refineRegs) in
/-- The digit's estimate: `q̂ = min(⌊U / D⌋, β - 1)` for `U` the three words of `⌊R / 2⌋` from word
`m - 1` of `R = [wRr]` and `D = (d, d₁)`, from `quot`'s and `refine3`'s conditions. -/
theorem est_vp {ar o m : Nat} (hm : 1 ≤ m) (hmW : o + m + 3 ≤ P.W) {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat} (hRr : ar ∈ LW)
    (hLS : ∀ d ∈ LS, d ≠ sU0 ∧ d ≠ sU2 ∧ (d + 4 ≤ sMk ∨ sMk + 4 ≤ d) ∧ (d + 4 ≤ sQ ∨ sQ + 4 ≤ d))
    (hD : sD ∈ LS) (hD1 : sD1 ∈ LS) (hVs : sV ∈ LS)
    (vd : ∀ σ, E σ → 2 ^ 31 ≤ V σ sD) (vV : ∀ σ, E σ → V σ sV = (2 ^ 64 - 1) / V σ sD - 2 ^ 32)
    (hRb : ∀ σ, E σ → (AW σ ar / 2 ^ (32 * o)) < 2 ^ (32 * (m + 2) + 1))
    (hu2 : ∀ σ, E σ → (AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) / 2 ^ 64 ≤ V σ sD)
    (hUD : ∀ σ, E σ → (AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) < (2 ^ 32 + 1) * (V σ sD * 2 ^ 32 + V σ sD1))
    (hge : ∀ σ, E σ → min ((AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) / (V σ sD * 2 ^ 32 + V σ sD1)) (2 ^ 32 - 1) ≤
      (if (AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) / 2 ^ 64 = V σ sD then 2 ^ 32 - 1 else
        (AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) / 2 ^ 32 / V σ sD))
    (hle : ∀ σ, E σ → (if (AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) / 2 ^ 64 = V σ sD then 2 ^ 32 - 1 else
        (AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) / 2 ^ 32 / V σ sD) ≤
      min ((AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) / (V σ sD * 2 ^ 32 + V σ sD1)) (2 ^ 32 - 1) + 2) :
    VP (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r10 = P.B + BitVec.ofNat 32 (arr P.W ar + 4 * o) ∧
        s.gpr .r1 = BitVec.ofNat 32 (4 * m))
      (.block estBody)
      (Dk P E A L AW LW (fun σ => upd (V σ) sQ (min ((AW σ ar / 2 ^ (32 * o)) / 2 ^ (32 * (m - 1) + 1) /
        (V σ sD * 2 ^ 32 + V σ sD1)) (2 ^ 32 - 1))) (sQ :: LS) P.W 22) := by
  refine VP.taint _ estBody_taint offRegs fun σ s ⟨⟨e, h, hv⟩, p10, p1⟩ => ?_
  have sz := h.sizes
  have Wl := sz.Wle
  have fR := fitZ_W sz (h.liveW_lt ar hRr)
  have nw := hv.nowrap
  simp only [S] at fR
  have x0 := h.arrsW ar hRr
  simp only [num] at x0
  have hu2 := hu2 σ e
  have hUD := hUD σ e
  have hge := hge σ e
  have hle := hle σ e
  have hR := hRb σ e
  generalize eR : (AW σ ar / 2 ^ (32 * o)) = R at hR hu2 hUD hge hle
  -- the four words `m - 1 .. m + 2` of `R`
  generalize ea : R / 2 ^ (32 * (m - 1)) = a
  have ha : a < 2 ^ 97 := by
    rw [← ea, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hR (Nat.pow_le_pow_right (by decide) (by omega_using []))
  have wd : ∀ i, i < 4 → w32 s.mem (State.addr P.B) (arr P.W ar + 4 * (o + (m - 1)) + 4 * i) =
      a / 2 ^ (32 * i) % 2 ^ 32 := fun i hi => by
    rw [show arr P.W ar + 4 * (o + (m - 1)) + 4 * i = arr P.W ar + 4 * (o + (m - 1 + i)) by omega_using [],
      w32_digit _ _ _ (show o + (m - 1 + i) < P.W by omega_using [hm, hmW, hi]), x0,
      show 32 * (o + (m - 1 + i)) = 32 * o + 32 * (m - 1 + i) by omega_using [], Nat.pow_add, ← Nat.div_div_eq_div_mul, eR,
      ← ea, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 3; omega_using []
  simp only [estBody, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r10]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r10]) (by simp)) u2.mem
  have q10 : s2.gpr .r10 = P.B + BitVec.ofNat 32 (arr P.W ar + 4 * (o + (m - 1))) := by
    rw [u2.gpr, dpVal, u1.gpr, dpVal, p10, p1, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_ofNat_eq _ (by omega_using [hm]) (by decide)]
    congr 2; omega_using [hm]
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine wp_ldr (by decide) (by rw [q10, BitVec.add_zero, hv2.addr (by omega_using [hmW, fR])]) (hv2.read (by omega_using [hmW, fR])) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine wp_ldr (by decide) (by rw [u3.other _ (by decide), q10, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc,
    hv3.addr (by omega_using [hmW, fR])]) (hv3.read (by omega_using [hmW, fR])) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine wp_ldr (by decide) (by rw [u4.other _ (by decide), u3.other _ (by decide), q10,
    VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, hv4.addr (by omega_using [hmW, fR])]) (hv4.read (by omega_using [hmW, fR])) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r2]) (by simp)) u5.mem
  refine wp_ldr (by decide) (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), q10,
    VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, hv5.addr (by omega_using [hmW, fR])]) (hv5.read (by omega_using [hmW, fR])) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r3]) (by simp)) u6.mem
  have g0 : (s6.gpr .r0).toNat = a % 2 ^ 32 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr]
    show w32 s2.mem (State.addr P.B) (arr P.W ar + 4 * (o + (m - 1))) = _
    rw [m2, ← Nat.add_zero (arr P.W ar + 4 * (o + (m - 1))), show (0 : Nat) = 4 * 0 from rfl, wd 0 (by decide)]; simp
  have g1 : (s6.gpr .r1).toNat = a / 2 ^ 32 % 2 ^ 32 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    show w32 s3.mem (State.addr P.B) (arr P.W ar + 4 * (o + (m - 1)) + 4) = _
    rw [u3.mem, m2, show (4 : Nat) = 4 * 1 from rfl, wd 1 (by decide)]
  have g2 : (s6.gpr .r2).toNat = a / 2 ^ 64 % 2 ^ 32 := by
    rw [u6.other _ (by decide), u5.gpr]
    show w32 s4.mem (State.addr P.B) (arr P.W ar + 4 * (o + (m - 1)) + 8) = _
    rw [u4.mem, u3.mem, m2, show (8 : Nat) = 4 * 2 from rfl, wd 2 (by decide)]
  have g3 : (s6.gpr .r3).toNat = a / 2 ^ 96 % 2 ^ 32 := by
    rw [u6.gpr]
    show w32 s5.mem (State.addr P.B) (arr P.W ar + 4 * (o + (m - 1)) + 12) = _
    rw [u5.mem, u4.mem, u3.mem, m2, show (12 : Nat) = 4 * 3 from rfl, wd 3 (by decide)]
  have hw := half_words ha
  have hU : R / 2 ^ (32 * (m - 1) + 1) = a / 2 := by
    rw [← ea, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  rw [hU] at hu2 hUD hge hle
  -- `u₀`, `u₁`, `u₂`
  refine wp_mov (op2_lsr (by decide)) fun s7 u7 => ?_
  obtain ⟨h7, hv7⟩ := h6.reg hv6 (u7.rest (ws := [.r0]) (by simp)) u7.mem
  refine wp_dp (op2_lsl (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r0]) (by simp)) u8.mem
  have v0 : (s8.gpr .r0).toNat = a % 2 ^ 32 / 2 + a / 2 ^ 32 % 2 ^ 32 % 2 * 2 ^ 31 := by
    rw [u8.gpr, dpVal, u7.gpr, u7.other _ (by decide), shr1_or, g0, g1]
  refine h8.strSlot hv8 (d := sU0) (r := .r0) (by decide) fun s9 h9 hv9 g9 _ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
  obtain ⟨h10, hv10⟩ := h9.reg hv9 (u10.rest (ws := [.r11]) (by simp)) u10.mem
  refine wp_dp (op2_lsl (by decide)) fun s11 u11 => ?_
  obtain ⟨h11, hv11⟩ := h10.reg hv10 (u11.rest (ws := [.r11]) (by simp)) u11.mem
  refine wp_mov (op2_lsr (by decide)) fun s12 u12 => ?_
  obtain ⟨h12, hv12⟩ := h11.reg hv11 (u12.rest (ws := [.r2]) (by simp)) u12.mem
  refine wp_dp (op2_lsl (by decide)) fun s13 u13 => ?_
  obtain ⟨h13, hv13⟩ := h12.reg hv12 (u13.rest (ws := [.r2]) (by simp)) u13.mem
  have r9eq : ∀ r, r ≠ .r0 → s9.gpr r = s6.gpr r := fun r hr => by
    rw [g9, u8.other _ hr, u7.other _ hr]
  have v11 : s11.gpr .r11 = BitVec.ofNat 32 (a / 2 ^ 32 % 2 ^ 32 / 2 + a / 2 ^ 64 % 2 ^ 32 % 2 * 2 ^ 31) := by
    apply BitVec.eq_of_toNat_eq
    rw [u11.gpr, dpVal, u10.gpr, u10.other _ (by decide), r9eq _ (by decide), r9eq _ (by decide), shr1_or, g1, g2,
      BitVec.toNat_ofNat]
    omega_using []
  have v2 : (s13.gpr .r2).toNat = a / 2 ^ 64 % 2 ^ 32 / 2 + a / 2 ^ 96 % 2 ^ 32 % 2 * 2 ^ 31 := by
    rw [u13.gpr, dpVal, u12.gpr, u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide),
      u11.other _ (by decide), u10.other _ (by decide), r9eq _ (by decide), r9eq _ (by decide), shr1_or, g2, g3]
  refine h13.strSlot hv13 (d := sU2) (r := .r2) (by decide) fun s14 h14 hv14 g14 _ => ?_
  refine wp_mov (op2_reg _ _) fun s15 u15 => ?_
  obtain ⟨h15, hv15⟩ := h14.reg hv14 (u15.rest (ws := [.r12]) (by simp)) u15.mem
  rw [v2] at h15
  rw [v0] at h15
  generalize eu0 : a % 2 ^ 32 / 2 + a / 2 ^ 32 % 2 ^ 32 % 2 * 2 ^ 31 = u0 at h15 hw
  generalize eu1 : a / 2 ^ 32 % 2 ^ 32 / 2 + a / 2 ^ 64 % 2 ^ 32 % 2 * 2 ^ 31 = u1 at v11 hw
  generalize eu2 : a / 2 ^ 64 % 2 ^ 32 / 2 + a / 2 ^ 96 % 2 ^ 32 % 2 * 2 ^ 31 = u2 at h15 hw
  have lu1 : u1 < 2 ^ 32 := by omega_using [eu1]
  have lu2 : u2 < 2 ^ 32 := by omega_using [eu2]
  have lu0 : u0 < 2 ^ 32 := by omega_using [eu0]
  have eU2 : a / 2 / 2 ^ 64 = u2 := by omega_using [hle, hge, hUD, hu2, ea, ha, g0, g1, g2, g3, hU, v0, v2, eu0, eu1, eu2, hw, lu2]
  have eU1 : a / 2 / 2 ^ 32 = u2 * 2 ^ 32 + u1 := by omega_using [hle, hge, hUD, hu2, ea, ha, g0, g1, g2, g3, hU, v0, v2, eu0, eu1, eu2, hw, lu1, lu2, eU2]
  rw [eU2] at hu2 hge hle
  rw [eU1] at hge hle
  -- `quot` and `refine3`
  have d0 := vd σ e
  have dl : V σ sD < 2 ^ 32 := by rw [← h.sl _ hD]; exact BitVec.isLt _
  have d1l : V σ sD1 < 2 ^ 32 := by rw [← h.sl _ hD1]; exact BitVec.isLt _
  have sl15 : ∀ c ∈ LS, slot s15.mem P.B c = V σ c := fun c hc => by
    have := h15.sl c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
    rwa [upd_ne _ _ (hLS c hc).2.1, upd_ne _ _ (hLS c hc).1] at this
  have r12_15 : s15.gpr .r12 = P.B := by rw [u15.gpr, h14.r8]
  have r11_15 : s15.gpr .r11 = BitVec.ofNat 32 u1 := by
    rw [u15.other _ (by decide), g14, u13.other _ (by decide), u12.other _ (by decide), v11]
  have hW15 := hv15.m
  have sU2v : slot s15.mem P.B sU2 = u2 := by
    have := h15.sl sU2 (List.mem_cons_self ..); rwa [upd_self] at this
  have sU0v : slot s15.mem P.B sU0 = u0 := by
    have := h15.sl sU0 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rwa [upd_ne _ _ (show sU0 ≠ sU2 by decide), upd_self] at this
  refine quot_ok hW15 r12_15 (u1 := u1) (d := V σ sD) (u2 := u2) r11_15 (sl15 _ hD) sU2v
    ((sl15 _ hVs).trans (vV σ e)) d0 dl hu2 lu1 fun t1 q1 k1 r11 r12 R1 => ?_
  have hd2 : ∀ c, c + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr → (c + 4 ≤ sMk ∨ sMk + 4 ≤ c) → (c + 4 ≤ sQ ∨ sQ + 4 ≤ c) →
      slot t1.mem P.B c = slot s15.mem P.B c := fun c hc h1 h2 => k1.slot hc fun f hf => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · rcases h1 with h1 | h1 <;> omega_using [h1]
    · rcases h2 with h2 | h2 <;> omega_using [h2]
  refine refine3_ok (hW15.of R1.wr) r12 (q0 := if u2 = V σ sD then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / V σ sD)
    (u1 := u1) (by rw [r11, r11_15]) lu1 q1 (U := a / 2)
    (by rw [hd2 sU2 (by decide) (by decide) (by decide), hd2 sU0 (by decide) (by decide) (by decide), sU2v, sU0v]; omega_using [hUD, ea, ha, g0, g1, g2, g3, hU, v0, v2, eu0, eu1, hle, hge, hu2, eu2, hw, lu1, lu2, lu0, eU2, eU1])
    (D := V σ sD * 2 ^ 32 + V σ sD1)
    (by rw [hd2 sD (by decide) (by decide) (by decide), hd2 sD1 (by decide) (by decide) (by decide), sl15 _ hD,
      sl15 _ hD1])
    (by omega_using [hUD]) hUD hge hle fun t2 q2 k2 r12' R2 => ?_
  refine wp_mov (op2_reg _ _) fun t3 u3 => ?_
  have k13 : Keep P.B P.W [] [sMk, sQ] s15.mem t3.mem := by
    rw [u3.mem]; exact k1.trans (k2.mono (by simp) (by simp))
  have r83 : t3.gpr .r8 = P.B := by rw [u3.gpr, r12']
  have R3 : Rest (quotRegs ++ refineRegs ++ [.r8]) s15 t3 :=
    ((R1.mono (by simp)).trans (R2.mono (by simp))).trans (u3.rest (by simp))
  have K3 := h15.slot2 (x := slot t3.mem P.B sMk) (y := min (a / 2 / (V σ sD * 2 ^ 32 + V σ sD1)) (2 ^ 32 - 1)) k13
    (by decide) (by decide) (fun c hc => by
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · decide
      · decide
      · exact ⟨(hLS c hc).2.2.1, (hLS c hc).2.2.2⟩) r83 R3.sp R3.rd R3.wr rfl (by rw [u3.mem]; exact q2) (by decide)
  refine WP.mono (ctxW_ok K3.bs K3.r8 K3.cnt) fun t4 ⟨hvt4, rt4, mt4⟩ => ⟨e, ?_, hvt4⟩
  refine (K3.of_rest rt4 mt4 (by decide)).mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩)
    (fun d hd => ⟨?_, ?_⟩)
  · rfl
  · rcases List.mem_cons.mp hd with rfl | hd
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)))
  · rcases List.mem_cons.mp hd with rfl | hd
    · beta_reduce; simp only [upd_self]; rw [eR, hU]
    · have hdQ : d ≠ sQ := fun h0 => by have := (hLS d hd).2.2.2; rw [h0] at this; omega_using [hm, hmW, p10, p1, Wl, fR, nw, x0, eR, hR, hUD, ea, ha, q10, g0, g1, g2, g3, hU, v0, v2, eu0, eu1, v11, hle, hge, hu2, eu2, hw, lu1, lu2, lu0, eU2, eU1, d0, dl, d1l, r12_15, r11_15, sU2v, sU0v, q1, r11, r12, q2, r12', r83, h0, this]
      have hdMk : d ≠ sMk := fun h0 => by have := (hLS d hd).2.2.1; rw [h0] at this; omega_using [hm, hmW, p10, p1, Wl, fR, nw, x0, eR, hR, hUD, ea, ha, q10, g0, g1, g2, g3, hU, v0, v2, eu0, eu1, v11, hle, hge, hu2, eu2, hw, lu1, lu2, lu0, eU2, eU1, d0, dl, d1l, r12_15, r11_15, sU2v, sU0v, q1, r11, r12, q2, r12', r83, hdQ, h0, this]
      beta_reduce
      simp only [upd_ne _ _ hdQ, upd_ne _ _ hdMk, upd_ne _ _ (hLS d hd).2.1, upd_ne _ _ (hLS d hd).1]

end

/-! ## A correction -/

section
variable {P : RP}

/-- The arrays after a correction: `E = 2 q̂ - 1`, `F` and `[wRr]` the corrected remainder, `G` and `T`
its scratch. -/
abbrev fixE (x : Nat) : Nat := (2 * x + 2 ^ 64 - 1) % 2 ^ 64
abbrev fixG (n t c x : Nat) : Nat := if t / 2 ^ (32 * n - 1) = 0 then 0 else sub32 n c (sub32 n 0 (fixE x))
abbrev fixR (n t c x : Nat) : Nat := sub32 n t (sub32 n 0 (fixG n t c x))

theorem sub32_lt (n a b : Nat) : sub32 n a b < 2 ^ (32 * n) := by
  unfold sub32; exact Nat.mod_lt _ (Nat.two_pow_pos _)

end

/-! ## Windows of words of the wide arrays -/

section
variable {P : RP}

/-- `[j]`'s low `o` words and its words from `o`. -/
theorem num_split (m : Mem) (B : BitVec 32) {W j o : Nat} (ho : o ≤ W) :
    num m B W j % 2 ^ (32 * o) = val32 m (State.addr B) (arr W j) o ∧
    num m B W j / 2 ^ (32 * o) = val32 m (State.addr B) (arr W j + 4 * o) (W - o) :=
  mod_div_of (Nat.two_pow_pos _) (val32_lt _ _ _ _) (numW_at m B W j o ho)

/-- `[j]`'s `n` words from word `o`. -/
theorem num_win (m : Mem) (B : BitVec 32) {W j o n : Nat} (hon : o + n ≤ W) :
    val32 m (State.addr B) (arr W j + 4 * o) n = num m B W j / 2 ^ (32 * o) % 2 ^ (32 * n) := by
  rw [(num_split m B (j := j) (show o ≤ W by omega_using [hon])).2, val32_lo _ _ _ (show n ≤ W - o by omega_using [hon])]

/-- A write of `[j]`'s `n` words from word `o`. -/
theorem num_win_write {m m' : Mem} {B : BitVec 32} {W j o n : Nat} (hon : o + n ≤ W)
    (O : Outside (State.addr B) (arr W j + 4 * o) (4 * n) m m') (hf : arr W j + 4 * W ≤ 2 ^ 64) :
    num m' B W j = setWin (num m B W j) o n (val32 m' (State.addr B) (arr W j + 4 * o) n) := by
  have s1 := num_split m B (j := j) (show o ≤ W by omega_using [hon])
  have s2 := num_split m B (j := j) (show o + n ≤ W from hon)
  have lo : val32 m' (State.addr B) (arr W j) o = val32 m (State.addr B) (arr W j) o :=
    O.val32 (Or.inl (by omega_using [])) (by omega_using [hon, hf])
  have hi : val32 m' (State.addr B) (arr W j + 4 * (o + n)) (W - (o + n)) =
      val32 m (State.addr B) (arr W j + 4 * (o + n)) (W - (o + n)) :=
    O.val32 (Or.inr (by omega_using [])) (by omega_using [hon, hf])
  have ap := val32_append m' (State.addr B) (arr W j + 4 * o) n (W - (o + n))
  rw [show n + (W - (o + n)) = W - o by omega_using [hon], show arr W j + 4 * o + 4 * n = arr W j + 4 * (o + n) by omega_using []] at ap
  rw [numW_at m' B W j o (by omega_using [hon]), lo, ap, hi, ← s1.1, ← s2.2]

end

/-! ## A row at word offsets -/

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- The row's value: `[a]`'s window plus `x` times `[c]`'s, plus `c₀`. -/
abbrev rowV (AW : Nat → Nat) (a c oa oc n x c0 : Nat) : Nat :=
  AW a / 2 ^ (32 * oa) % 2 ^ (32 * n) + x * (AW c / 2 ^ (32 * oc) % 2 ^ (32 * n)) + c0

open VG.Proof.Bignum.Arm in
/-- `row` on the `n` words of the wide `[a]` from word `oa` and of `[c]` from word `oc`: the window
`(win a + x win c + c₀) mod 2^(32 n)`, the carry out in `r11`, and `r1` and `r8` kept. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.rowAt {a c oa oc n : Nat} (h : KS P σ A live AW liveW V ls s)
    (hv : Ws s P.B P.Z P.W 22) (ha : a ∈ liveW) (hc : c ∈ liveW) (hac : a ≠ c) (hn : 0 < n)
    (hoa : oa + n ≤ P.W) (hoc : oc + n ≤ P.W) (hl : ∀ i ∈ live, i / 2 ≠ a)
    (p0 : s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W a + 4 * oa))
    (p12 : s.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W c + 4 * oc))
    (plr : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa VG.Impl.Bignum.Arm.row s fun t =>
      KS P σ A live (upd AW a (setWin (AW a) oa n
        (rowV AW a c oa oc n (s.gpr .r1).toNat (s.gpr .r11).toNat % 2 ^ (32 * n)))) (a :: liveW) V ls t ∧
      VG.Proof.Rsa.Arm.KeyDiv.WsM t P.B P.Z P.W 22 ∧
      (t.gpr .r11).toNat = rowV AW a c oa oc n (s.gpr .r1).toNat (s.gpr .r11).toNat / 2 ^ (32 * n) ∧
      t.gpr .r1 = s.gpr .r1 ∧ t.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W a + 4 * (oa + n)) ∧
      t.gpr .r8 = P.B ∧ t.wr = s.wr := by
  have sz := h.sizes
  have Wl := sz.Wle
  have nw := hv.nowrap
  have a22 := h.liveW_lt a ha
  have c22 := h.liveW_lt c hc
  have fa := fitZ_W sz a22
  have fc := fitZ_W sz c22
  have fa' := fit_W sz a22
  have dac := arr_disj (w := P.W) hac
  simp only [S] at fa fc fa' dac
  have rc : RowCtx s P.B P.Z (arr P.W a + 4 * oa) (arr P.W c + 4 * oc) n :=
    ⟨nw, by omega_using [hoa, fa], by omega_using [hoc, fc], by omega_using [hoa, hoc, dac], hv.writable⟩
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .lr]
    (row_ok s rc hn p0 p12 plr) (by decide)) fun t ⟨inv, kv⟩ => ?_
  have k1 : Keep P.B P.W [a] [] s.mem t.mem :=
    Keep.of_arr (d := 4 * oa) inv.outside (by simp only [S]; omega_using [hoa]) (by simp)
  have vv := inv.value
  rw [num_win s.mem P.B hoa, num_win s.mem P.B hoc, h.arrsW a ha, h.arrsW c hc] at vv
  have hl' := val32_lt t.mem (State.addr P.B) (arr P.W a + 4 * oa) n
  have ev : num t.mem P.B P.W a = setWin (AW a) oa n
      (rowV AW a c oa oc n (s.gpr .r1).toNat (s.gpr .r11).toNat % 2 ^ (32 * n)) := by
    rw [num_win_write hoa inv.outside (by omega_using [fa']), h.arrsW a ha]
    congr 1
    simp only [rowV]
    rw [← vv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl']
  have r8 : t.gpr .r8 = P.B := by rw [kv.gpr _ (by decide), h.r8]
  refine ⟨h.write_W k1 a22 (by simp) r8 kv.sp kv.rd kv.wr ev hl (by simp), ⟨nw, kv.wr ▸ hv.writable, hv.fits⟩,
    ?_, inv.rest.gpr .r1 (by decide), ?_, r8, kv.wr⟩
  · simp only [rowV]
    rw [← vv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hl', Nat.zero_add]
  · rw [inv.outPtr, Nat.add_assoc, ← Nat.mul_add]

open VG.Proof.Bignum.Arm in
/-- `maskRow` on the `n` words of the wide `[a]` from word `oa` and of `[c]` from word `oc`, under the mask in
`r1`: as `KS.rowAt`, with the scalar the mask's bit. -/
theorem _root_.VG.Proof.Rsa.Arm.Recover.KS.maskRowAt {a c oa oc n : Nat} (h : KS P σ A live AW liveW V ls s)
    (hv : Ws s P.B P.Z P.W 22) (ha : a ∈ liveW) (hc : c ∈ liveW) (hac : a ≠ c) (hn : 0 < n)
    (hoa : oa + n ≤ P.W) (hoc : oc + n ≤ P.W) (hl : ∀ i ∈ live, i / 2 ≠ a)
    (p0 : s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W a + 4 * oa))
    (p12 : s.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W c + 4 * oc))
    (plr : s.gpr .lr = BitVec.ofNat 32 n) (hm : s.gpr .r1 = 0 ∨ s.gpr .r1 = BitVec.allOnes 32) :
    WP isa VG.Impl.Bignum.Arm.maskRow s fun t =>
      KS P σ A live (upd AW a (setWin (AW a) oa n
        (rowV AW a c oa oc n ((s.gpr .r1).toNat / (2 ^ 32 - 1)) (s.gpr .r11).toNat % 2 ^ (32 * n))))
        (a :: liveW) V ls t ∧
      VG.Proof.Rsa.Arm.KeyDiv.WsM t P.B P.Z P.W 22 ∧
      (t.gpr .r11).toNat = rowV AW a c oa oc n ((s.gpr .r1).toNat / (2 ^ 32 - 1)) (s.gpr .r11).toNat / 2 ^ (32 * n) ∧
      t.gpr .r1 = s.gpr .r1 ∧ t.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W a + 4 * (oa + n)) ∧
      t.gpr .r8 = P.B ∧ t.wr = s.wr := by
  have sz := h.sizes
  have Wl := sz.Wle
  have nw := hv.nowrap
  have a22 := h.liveW_lt a ha
  have c22 := h.liveW_lt c hc
  have fa := fitZ_W sz a22
  have fc := fitZ_W sz c22
  have fa' := fit_W sz a22
  have dac := arr_disj (w := P.W) hac
  simp only [S] at fa fc fa' dac
  have rc : RowCtx s P.B P.Z (arr P.W a + 4 * oa) (arr P.W c + 4 * oc) n :=
    ⟨nw, by omega_using [hoa, fa], by omega_using [hoc, fc], by omega_using [hoa, hoc, dac], hv.writable⟩
  refine WP.mono (maskRow_ok s rc hn p0 p12 plr hm) fun t ⟨q0, _, out, q1, vv, rest⟩ => ?_
  have k1 : Keep P.B P.W [a] [] s.mem t.mem :=
    Keep.of_arr (d := 4 * oa) out (by simp only [S]; omega_using [hoa]) (by simp)
  rw [num_win s.mem P.B hoa, num_win s.mem P.B hoc, h.arrsW a ha, h.arrsW c hc] at vv
  have hl' := val32_lt t.mem (State.addr P.B) (arr P.W a + 4 * oa) n
  have ev : num t.mem P.B P.W a = setWin (AW a) oa n
      (rowV AW a c oa oc n ((s.gpr .r1).toNat / (2 ^ 32 - 1)) (s.gpr .r11).toNat % 2 ^ (32 * n)) := by
    rw [num_win_write hoa out (by omega_using [fa']), h.arrsW a ha]
    congr 1
    simp only [rowV]
    rw [← vv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl']
  have r8 : t.gpr .r8 = P.B := by rw [rest.gpr _ (by decide), h.r8]
  refine ⟨h.write_W k1 a22 (by simp) r8 rest.sp rest.rd rest.wr ev hl (by simp),
    ⟨nw, rest.wr ▸ hv.writable, hv.fits⟩, ?_, q1, ?_, r8, rest.wr⟩
  · simp only [rowV]
    rw [← vv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hl', Nat.zero_add]
  · rw [q0, Nat.add_assoc, ← Nat.mul_add]

/-- Registers fixed by a state predicate, and `r7`–`r9` by its workspace: the same in both runs. -/
theorem pinW {F : State → State → Prop} {rs : List Reg} (hws : ∀ σ s, F σ s → Ws s P.B P.Z P.W 22)
    (hp : ∀ r ∈ rs, ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.gpr r = s₂.gpr r) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs ++ ([.r7, .r8, .r9] : List Reg), s₁.gpr r = s₂.gpr r := by
  intro σ₁ σ₂ s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hp r hr σ₁ σ₂ s₁ s₂ h₁ h₂
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [(hws _ _ h₁).r7, (hws _ _ h₂).r7]
    · rw [(hws _ _ h₁).r8, (hws _ _ h₂).r8]
    · rw [(hws _ _ h₁).r9, (hws _ _ h₂).r9]

theorem setWin_div_hi {x o n v : Nat} (hv : v < 2 ^ (32 * n)) :
    setWin x o n v / 2 ^ (32 * (o + n)) = x / 2 ^ (32 * (o + n)) := by
  rw [pow32_add, ← Nat.div_div_eq_div_mul, (setWin_mod_div x o n v).2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hv, Nat.zero_add, pow32_add]

open VG.Impl.Rsa.Arm.KeyDiv (sQ) in
/-- `T = R - q̂ D'` in place: `R`'s `n` words from word `b` plus `q̂ C'` (`[wE]`'s `n` words from word `m`)
plus `q̂` by a row, then `R`'s word `b + n` less `q̂` plus the carry; the context back. -/
theorem msRow_vp {b m n : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hn : 0 < n) (hbn : b + n + 1 ≤ P.W) (hmn : m + n ≤ P.W) (hR : wR ∈ LW) (hE : wE ∈ LW) (hQ : sQ ∈ LS)
    (hL : ∀ j ∈ L, j / 2 ≠ wR) :
    VP (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wR + 4 * b) ∧
        s.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W wE + 4 * m) ∧ s.gpr .lr = BitVec.ofNat 32 n)
      (.seq (.block [.ldr .r1 .r8 sQ, .mov .r11 (.reg .r1)]) (.seq VG.Impl.Bignum.Arm.row
        (.block (([.ldr .r2 .r0 0, .dp .add .r2 .r2 (.reg .r11), .dp .sub .r2 .r2 (.reg .r1), .str .r2 .r0 0] :
          List Instr) ++ VG.Impl.Rsa.Arm.Recover.ctxW))))
      (Dk P E A L (fun σ => upd (AW σ) wR (setW (setWin (AW σ wR) b n
          (rowV (AW σ) wR wE b m n (V σ sQ) (V σ sQ) % 2 ^ (32 * n))) (b + n)
          ((2 ^ 32 - V σ sQ + (AW σ wR / 2 ^ (32 * (b + n)) % 2 ^ 32 +
            rowV (AW σ) wR wE b m n (V σ sQ) (V σ sQ) / 2 ^ (32 * n)) % 2 ^ 32) % 2 ^ 32))) LW V LS P.W 22) := by
  refine VP.taint _ msRow_taint (pinW (fun _ _ h => h.1.2.2) fun r hr σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hv⟩, p0, p12, plr⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  have ql : V σ sQ < 2 ^ 32 := by rw [← h.sl _ hQ]; exact BitVec.isLt _
  rw [WP.seq_iff]
  refine h.ldrSlot hv hQ (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun u u2 => WP.block_nil ?_
  obtain ⟨hu, hvu⟩ := h1.reg hv1 (u2.rest (ws := [.r11]) (by simp)) u2.mem
  have r1v : (u.gpr .r1).toNat = V σ sQ := by
    rw [u2.other _ (by decide), u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
  have r11v : (u.gpr .r11).toNat = V σ sQ := by
    rw [u2.gpr, u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
  rw [WP.seq_iff]
  refine WP.mono (hu.rowAt (oa := b) (oc := m) hvu hR hE (by decide) hn (by omega_using [hbn]) hmn hL
    (by rw [u2.other _ (by decide), u1.other _ (by decide), p0])
    (by rw [u2.other _ (by decide), u1.other _ (by decide), p12])
    (by rw [u2.other _ (by decide), u1.other _ (by decide), plr])) fun t ⟨ht, hvt, c11, c1, c0, c8, cw⟩ => ?_
  rw [r1v, r11v] at ht c11
  have q1 : (t.gpr .r1).toNat = V σ sQ := by rw [c1, r1v]
  refine ht.ldrWo hvt (List.mem_cons_self ..) (i := b + n) (i0 := b + n) (by omega_using [hbn]) (by omega_using []) (by decide) c0
    (by decide) fun t1 ht1 hvt1 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t2 u4 => ?_
  have ht2 := ht1.of_rest (u4.rest (ws := [.r2]) (by simp)) u4.mem (by decide)
  refine wp_dp (op2_reg _ _) fun t3 u5 => ?_
  have ht3 := ht2.of_rest (u5.rest (ws := [.r2]) (by simp)) u5.mem (by decide)
  refine ht3.strWo (hvt1.of (u5.wr.trans u4.wr)) (List.mem_cons_self ..) (i := b + n) (i0 := b + n) (by omega_using [hbn])
    (by omega_using []) (by decide) (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), c0])
    (fun j hj => hL j hj) fun t4 ht4 hvt4 e4 w4 => ?_
  refine WP.mono (ctxW_ok ht4.bs ht4.r8 ht4.cnt) fun t5 ⟨hvt5, rt5, mt5⟩ => ⟨e, ?_, hvt5⟩
  have hw : (t3.gpr .r2).toNat = (2 ^ 32 - V σ sQ + (AW σ wR / 2 ^ (32 * (b + n)) % 2 ^ 32 +
      rowV (AW σ) wR wE b m n (V σ sQ) (V σ sQ) / 2 ^ (32 * n)) % 2 ^ 32) % 2 ^ 32 := by
    have wd : (BitVec.ofNat 32 (upd (AW σ) wR (setWin (AW σ wR) b n
        (rowV (AW σ) wR wE b m n (V σ sQ) (V σ sQ) % 2 ^ (32 * n))) wR / 2 ^ (32 * (b + n)) % 2 ^ 32)).toNat =
        AW σ wR / 2 ^ (32 * (b + n)) % 2 ^ 32 := by
      rw [BitVec.toNat_ofNat, Nat.mod_mod, upd_self, setWin_div_hi (Nat.mod_lt _ (Nat.two_pow_pos _))]
    have cl : rowV (AW σ) wR wE b m n (V σ sQ) (V σ sQ) / 2 ^ (32 * n) < 2 ^ 32 := by
      rw [← c11]; exact BitVec.isLt _
    rw [u5.gpr, dpVal, BitVec.toNat_sub, u4.gpr, dpVal, BitVec.toNat_add, u4.other _ (by decide), u3.gpr,
      u3.other .r1 (by decide), u3.other .r11 (by decide), wd, c11, q1]
  refine (ht4.of_rest rt5 mt5 (by decide)).mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨?_, ?_⟩)
    (fun d hd => ⟨hd, rfl⟩)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)
  · by_cases c : j = wR
    · subst c; simp only [upd_self]; rw [hw]
    · simp only [upd_ne _ _ c]

theorem lsl2_val {n : Nat} (_hn : 4 * n < 2 ^ 32) : BitVec.ofNat 32 n <<< 2 = BitVec.ofNat 32 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- The masked `q̂ - 1`: `x (q̂ - 1)` for the sign `x`. -/
theorem mask_val (q : BitVec 32) {x : Nat} (hx : x ≤ 1) :
    ((q - 1) &&& (0 - BitVec.ofNat 32 x)).toNat = x * ((q.toNat + 2 ^ 32 - 1) % 2 ^ 32) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl
  · rw [show (0 : BitVec 32) - BitVec.ofNat 32 0 = 0#32 by decide, BitVec.and_zero, BitVec.toNat_zero, Nat.zero_mul]
  · rw [show (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
      BitVec.toNat_sub, Nat.one_mul, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_using []

/-- The top word of `R`'s `n + 1` words from `b`. -/
abbrev topW (y b n : Nat) : Nat := y / 2 ^ (32 * (b + n)) % 2 ^ 32

open VG.Impl.Rsa.Arm.KeyDiv (sQ) in
/-- A correction's row: the sign `x` of `T` (`R`'s `n + 1` words from `b`), `T`'s low `n` words plus `x D'`
(`[wD]`'s `n` words from `m`) plus `x (q̂ - 1)` by a row, the carry into `T`'s top word, the context back,
`q̂ := q̂ - x` (also in `r2`), and `m`'s offset in `r4`. -/
theorem corrRow_vp {b m n : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hn : 0 < n) (hbn : b + n + 1 ≤ P.W) (hmn : m + n ≤ P.W) (hR : wR ∈ LW) (hD : wD ∈ LW) (hQ : sQ ∈ LS)
    (hCm : sCm ∈ LS) (vCm : ∀ σ, E σ → V σ sCm = 4 * m) (hL : ∀ j ∈ L, j / 2 ≠ wR) :
    VP (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wR + 4 * b) ∧
        s.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W wD + 4 * m) ∧ s.gpr .lr = BitVec.ofNat 32 n)
      (.seq (.block corrPre) (.seq VG.Impl.Bignum.Arm.maskRow (.block corrPost)))
      (fun σ s => Dk P E A L (fun σ => upd (AW σ) wR (setW (setWin (AW σ wR) b n
          (rowV (AW σ) wR wD b m n (topW (AW σ wR) b n / 2 ^ 31)
            (topW (AW σ wR) b n / 2 ^ 31 * ((V σ sQ + 2 ^ 32 - 1) % 2 ^ 32)) % 2 ^ (32 * n))) (b + n)
          ((topW (AW σ wR) b n + rowV (AW σ) wR wD b m n (topW (AW σ wR) b n / 2 ^ 31)
            (topW (AW σ wR) b n / 2 ^ 31 * ((V σ sQ + 2 ^ 32 - 1) % 2 ^ 32)) / 2 ^ (32 * n)) % 2 ^ 32))) LW
        (fun σ => upd (V σ) sQ ((2 ^ 32 - topW (AW σ wR) b n / 2 ^ 31 + V σ sQ) % 2 ^ 32)) LS P.W 22 σ s ∧
        s.gpr .r4 = BitVec.ofNat 32 (4 * m) ∧
        s.gpr .r2 = BitVec.ofNat 32 ((2 ^ 32 - topW (AW σ wR) b n / 2 ^ 31 + V σ sQ) % 2 ^ 32)) := by
  refine VP.taint _ corrRow_taint (pinW (fun _ _ h => h.1.2.2) fun r hr σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hv⟩, p0, p12, plr⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  have sz := h.sizes
  have Wl := sz.Wle
  have ql : V σ sQ < 2 ^ 32 := by rw [← h.sl _ hQ]; exact BitVec.isLt _
  generalize eT : topW (AW σ wR) b n = T
  have Tl : T < 2 ^ 32 := by rw [← eT]; exact Nat.mod_lt _ (by decide)
  rw [WP.seq_iff]
  simp only [corrPre]
  -- the sign
  refine wp_dp (op2_lsl (by decide)) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r2]) (by simp)) u1.mem
  have q2 : s1.gpr .r2 = P.B + BitVec.ofNat 32 (arr P.W wR + 4 * (b + n)) := by
    rw [u1.gpr, dpVal, p0, plr, lsl2_val (by omega_using [hbn, Wl]), VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
    congr 2; omega_using []
  refine h1.ldrWo hv1.m hR (i := b + n) (i0 := b + n) (by omega_using [hbn]) (by omega_using []) (by decide) q2 (by decide)
    fun s2 h2 _ u2 => ?_
  have hv2 : Ws s2 P.B P.Z P.W 22 := hv1.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  have x1 : (s3.gpr .r1).toNat = T / 2 ^ 31 := by
    rw [u3.gpr, u2.gpr, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
      Nat.shiftRight_eq_div_pow]
    simp only [topW] at eT; rw [eT]
  have xb : T / 2 ^ 31 ≤ 1 := by omega_using [Tl]
  refine h3.ldrSlot hv3 hQ (r := .r2) (by decide) fun s4 h4 hv4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r11]) (by simp)) u5.mem
  refine wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r3]) (by simp)) u6.mem
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  obtain ⟨h7, hv7⟩ := h6.reg hv6 (u7.rest (ws := [.r3]) (by simp)) u7.mem
  refine wp_dp (op2_reg _ _) fun s8' u8 => ?_
  obtain ⟨h8', hv8'⟩ := h7.reg hv7 (u8.rest (ws := [.r11]) (by simp)) u8.mem
  refine wp_mov (op2_reg _ _) fun s8 u8m => WP.block_nil ?_
  obtain ⟨h8, hv8⟩ := h8'.reg hv8' (u8m.rest (ws := [.r1]) (by simp)) u8m.mem
  have e1 : s3.gpr .r1 = BitVec.ofNat 32 (T / 2 ^ 31) := by
    apply BitVec.eq_of_toNat_eq; rw [x1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [Tl])]
  have e3 : s7.gpr .r3 = 0 - BitVec.ofNat 32 (T / 2 ^ 31) := by
    rw [u7.gpr, dpVal, u6.gpr, u6.other .r1 (by decide), u5.other .r1 (by decide), u4.other .r1 (by decide), e1]
  have r1_8 : s8.gpr .r1 = 0 - BitVec.ofNat 32 (T / 2 ^ 31) := by
    rw [u8m.gpr, u8.other _ (by decide), e3]
  have hm8 : s8.gpr .r1 = 0 ∨ s8.gpr .r1 = BitVec.allOnes 32 := by
    rw [r1_8]; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp xb with h0 | h0 <;> rw [h0] <;> decide
  have x8 : (s8.gpr .r1).toNat / (2 ^ 32 - 1) = T / 2 ^ 31 := by
    rw [r1_8]; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp xb with h0 | h0 <;> rw [h0] <;> decide
  have c8 : (s8.gpr .r11).toNat = T / 2 ^ 31 * ((V σ sQ + 2 ^ 32 - 1) % 2 ^ 32) := by
    have e11 : s7.gpr .r11 = s4.gpr .r2 - 1 := by
      rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, dpVal]
    rw [u8m.other _ (by decide), u8.gpr, dpVal, e11, e3, mask_val _ xb, u4.gpr, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ql]
  have g0 : ∀ r, r = .r0 ∨ r = .r12 ∨ r = .lr → s8.gpr r = s.gpr r := fun r hr => by
    rcases hr with rfl | rfl | rfl <;>
      rw [u8m.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
        u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
        u1.other _ (by decide)]
  -- the row
  rw [WP.seq_iff]
  refine WP.mono (h8.maskRowAt (oa := b) (oc := m) hv8 hR hD (by decide) hn (by omega_using [hbn]) hmn hL
    (by rw [g0 _ (Or.inl rfl), p0]) (by rw [g0 _ (Or.inr (Or.inl rfl)), p12])
    (by rw [g0 _ (Or.inr (Or.inr rfl)), plr]) hm8) fun t ⟨ht, hvt, c11, c1, c0, c8', cw⟩ => ?_
  rw [x8, c8] at ht c11
  have xt : t.gpr .r1 = 0 - BitVec.ofNat 32 (T / 2 ^ 31) := by rw [c1, r1_8]
  -- the carry into the top word
  simp only [corrPost, List.cons_append, List.nil_append]
  refine ht.ldrWo hvt (List.mem_cons_self ..) (i := b + n) (i0 := b + n) (by omega_using [hbn]) (by omega_using []) (by decide) c0
    (by decide) fun t1 ht1 hvt1 u9 => ?_
  refine wp_dp (op2_reg _ _) fun t2 u10 => ?_
  have ht2 := ht1.of_rest (u10.rest (ws := [.r2]) (by simp)) u10.mem (by decide)
  refine ht2.strWo (hvt1.of u10.wr) (List.mem_cons_self ..) (i := b + n) (i0 := b + n) (by omega_using [hbn]) (by omega_using [])
    (by decide) (by rw [u10.other _ (by decide), u9.other _ (by decide), c0]) (fun j hj => hL j hj)
    fun t3 ht3 hvt3 e3 w3 => ?_
  refine WP.block_append_iff.mpr (WP.mono (ctxW_ok ht3.bs ht3.r8 ht3.cnt) fun t4 ⟨hvt4, rt4, mt4⟩ => ?_)
  have ht4 := ht3.of_rest rt4 mt4 (by decide)
  refine ht4.ldrSlot hvt4 hQ (r := .r2) (by decide) fun t5 ht5 hvt5 u11 => ?_
  refine wp_dp (op2_reg _ _) fun t6 u12 => ?_
  obtain ⟨ht6, hvt6⟩ := ht5.reg hvt5 (u12.rest (ws := [.r2]) (by simp)) u12.mem
  refine ht6.strSlot hvt6 (d := sQ) (r := .r2) (by decide) fun t7 ht7 hvt7 e7 _ => ?_
  refine ht7.ldrSlot hvt7 (List.mem_cons_of_mem _ hCm) (r := .r4) (by decide) fun t8 ht8 hvt8 u13 => WP.block_nil ?_
  have r1_5 : t5.gpr .r1 = t.gpr .r1 := by
    rw [u11.other _ (by decide), rt4.gpr _ (by decide), e3, u10.other _ (by decide), u9.other _ (by decide)]
  have q6 : (t6.gpr .r2).toNat = (2 ^ 32 - T / 2 ^ 31 + V σ sQ) % 2 ^ 32 := by
    rw [u12.gpr, dpVal, BitVec.toNat_add, u11.gpr, r1_5, xt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp xb with h0 | h0 <;> rw [h0] <;> simp <;> omega_using []
  have q8 : t8.gpr .r2 = BitVec.ofNat 32 ((2 ^ 32 - T / 2 ^ 31 + V σ sQ) % 2 ^ 32) := by
    rw [u13.other _ (by decide), e7]
    apply BitVec.eq_of_toNat_eq; rw [q6, BitVec.toNat_ofNat, Nat.mod_mod]
  have hw : (t2.gpr .r2).toNat = (T + rowV (AW σ) wR wD b m n (T / 2 ^ 31)
      (T / 2 ^ 31 * ((V σ sQ + 2 ^ 32 - 1) % 2 ^ 32)) / 2 ^ (32 * n)) % 2 ^ 32 := by
    rw [u10.gpr, dpVal, BitVec.toNat_add, u9.gpr, u9.other _ (by decide), c11, BitVec.toNat_ofNat, Nat.mod_mod, upd_self,
      setWin_div_hi (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [topW] at eT; rw [eT]
  refine ⟨⟨e, ht8.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj), ?_⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, ?_⟩), hvt8⟩, ?_, q8⟩
  · by_cases c : j = wR
    · subst c; simp only [upd_self]; rw [hw, ← eT]
    · simp only [upd_ne _ _ c]
  · by_cases c : d = sQ
    · subst c; simp only [upd_self]; rw [q6, ← eT]
    · simp only [upd_ne _ _ c]
  · rw [u13.gpr]; simp only [upd_ne _ _ (show sCm ≠ sQ by decide)]; rw [vCm σ e]

/-! ## A digit's small pieces -/

/-- `ptr rb j` and `r1 := 4 i` from the slot `d`. -/
theorem ptrSlot_vp {rb : Reg} (hrb : rb ∉ [.r7, .r8, .r9, .r1]) {j d i : Nat} {L LW LS : List Nat}
    {E : State → Prop} {A AW V : State → Nat → Nat} (hj : j < 22) (hd : d ∈ LS) (vd : ∀ σ, E σ → V σ d = 4 * i)
    (cert : DCert (.block (ptr rb j ++ ([.ldr .r1 .r8 d] : List Instr)))) :
    VP (Dk P E A L AW LW V LS P.W 22) (.block (ptr rb j ++ ([.ldr .r1 .r8 d] : List Instr)))
      (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr rb = P.B + BitVec.ofNat 32 (arr P.W j) ∧
        s.gpr .r1 = BitVec.ofNat 32 (4 * i)) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
    ptr_ok hv (r := rb) (by simp at hrb ⊢; grind) (j := j) (by omega_using [hj]) fun s1 p1 r1 m1 hv1 =>
      (h.of_rest r1 m1 (by simp at hrb ⊢; grind)).ldrSlot hv1 (d := d) hd (r := .r1) (by decide)
        fun t ht hvt u => WP.block_nil ⟨⟨e, ht, hvt⟩, by rw [u.other _ (by simp at hrb ⊢; grind), p1],
          by rw [u.gpr, vd σ e]⟩

/-- The estimate's offset: `r10 += r1`, then `r1 := 4 i'` from the slot `d`. -/
theorem estOff_vp {k i i' : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hd : sMo ∈ LS) (vd : ∀ σ, E σ → V σ sMo = 4 * i') :
    VP (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r10 = P.B + BitVec.ofNat 32 k ∧
        s.gpr .r1 = BitVec.ofNat 32 (4 * i)) (.block estOff)
      (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r10 = P.B + BitVec.ofNat 32 (k + 4 * i) ∧
        s.gpr .r1 = BitVec.ofNat 32 (4 * i')) :=
  VP.taint _ estOff_taint offRegs fun σ s ⟨⟨e, h, hv⟩, p10, p1⟩ => by
    unfold estOff
    refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
    obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r10]) (by simp)) u1.mem
    refine h1.ldrSlot hv1 (d := sMo) hd (r := .r1) (by decide) fun t ht hvt u => WP.block_nil
      ⟨⟨e, ht, hvt⟩, ?_, by rw [u.gpr, vd σ e]⟩
    rw [u.other _ (by decide), u1.gpr, dpVal, p10, p1, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]

/-- `r := 4 m` from `sCm`. -/
theorem ldCm_vp {r : Reg} (hr : r ∉ [.r7, .r8, .r9]) {m : Nat} {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat} (hCm : sCm ∈ LS) (vCm : ∀ σ, E σ → V σ sCm = 4 * m)
    (cert : DCert (.block [.ldr r .r8 sCm])) :
    VP (Dk P E A L AW LW V LS P.W 22) (.block [.ldr r .r8 sCm])
      (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr r = BitVec.ofNat 32 (4 * m)) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
    h.ldrSlot hv hCm (r := r) hr fun t ht hvt u => WP.block_nil ⟨⟨e, ht, hvt⟩, by rw [u.gpr, vCm σ e]⟩

/-- Pointer `rb := ` the address of word `m` of `[j]` from the offset `4 m` in `ro`. -/
theorem ptrOff_ok {rb ro : Reg} (hrb : rb ∉ [.r7, .r8, .r9]) (hro : ro ≠ rb) {j m : Nat} {σ s : State}
    {A AW V : Nat → Nat} {L LW LS : List Nat} {rest : List Instr} {Q : State → Prop} (hj : j < 22)
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) (po : s.gpr ro = BitVec.ofNat 32 (4 * m))
    (k : ∀ t, KS P σ A L AW LW V LS t → Ws t P.B P.Z P.W 22 →
      t.gpr rb = P.B + BitVec.ofNat 32 (arr P.W j + 4 * m) → Rest [rb] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ptr rb j ++ ([.dp .add rb rb (.reg ro)] : List Instr) ++ rest)) s Q := by
  rw [List.append_assoc]
  refine ptr_ok hv (r := rb) (by simpa using hrb) (j := j) (by omega_using [hj]) fun s1 p1 r1 m1 hv1 => ?_
  have h1 := h.of_rest r1 m1 (by simp at hrb ⊢; grind)
  refine wp_dp (op2_reg _ _) fun t u => ?_
  obtain ⟨ht, hvt⟩ := h1.reg hv1 (u.rest (ws := [rb]) (by simp)) u.mem (by simp at hrb ⊢; grind)
    (by simp at hrb ⊢; grind) (by simp at hrb ⊢; grind)
  refine k t ht hvt ?_ ((r1.trans (u.rest (by simp))).mono (by simp))
  rw [u.gpr, dpVal, p1, r1.gpr _ (by simpa using hro), po, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]

/-- `ptrOff_ok` with the addition consed onto the rest. -/
theorem ptrOffC_ok {rb ro : Reg} (hrb : rb ∉ [.r7, .r8, .r9]) (hro : ro ≠ rb) {j m : Nat} {σ s : State}
    {A AW V : Nat → Nat} {L LW LS : List Nat} {rest : List Instr} {Q : State → Prop} (hj : j < 22)
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) (po : s.gpr ro = BitVec.ofNat 32 (4 * m))
    (k : ∀ t, KS P σ A L AW LW V LS t → Ws t P.B P.Z P.W 22 →
      t.gpr rb = P.B + BitVec.ofNat 32 (arr P.W j + 4 * m) → Rest [rb] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ptr rb j ++ (.dp .add rb rb (.reg ro) :: rest))) s Q := by
  have := ptrOff_ok hrb hro hj h hv po k
  rwa [List.append_assoc, List.singleton_append] at this

open VG.Impl.Rsa.Arm.KeyDiv (sQ) in
/-- `setQ`: `q̂` into `[wD]`'s word `m`, `β - 1 - q̂` into `[wE]`'s. -/
theorem setQ_vp {m : Nat} (hm : m < P.W) {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hD : wD ∈ LW) (hE : wE ∈ LW) (hQ : sQ ∈ LS) (hL : ∀ j ∈ L, j / 2 ≠ wD ∧ j / 2 ≠ wE) :
    VP (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r3 = BitVec.ofNat 32 (4 * m)) (.block setQ)
      (Dk P E A L (fun σ => upd (upd (AW σ) wD (setW (AW σ wD) m (V σ sQ))) wE
        (setW (AW σ wE) m (2 ^ 32 - 1 - V σ sQ))) LW V LS P.W 22) := by
  refine VP.taint _ setQ_taint (pinW (fun _ _ h => h.1.2.2) fun r hr σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hv⟩, p3⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; rw [h₁.2, h₂.2]
  have ql : V σ sQ < 2 ^ 32 := by rw [← h.sl _ hQ]; exact BitVec.isLt _
  unfold setQ
  simp only [List.cons_append, List.nil_append]
  refine h.ldrSlot hv hQ (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine ptrOff_ok (rb := .r2) (ro := .r3) (by decide) (by decide) (j := wD) (m := m) (by decide) h1 hv1
    (by rw [u1.other _ (by decide), p3]) fun s2 h2 hv2 p2 r2 => ?_
  refine h2.strWo hv2.m hD (i := m) (i0 := m) hm (by omega_using []) (by decide) p2 (fun j hj => (hL j hj).1)
    fun s3 h3 hv3' e3 w3 => ?_
  have hv3 : Ws s3 P.B P.Z P.W 22 := hv2.of (by rw [e3]) (by rw [e3]) (by rw [e3]) w3
  refine wp_mvn (op2_reg _ _) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine ptrOff_ok (rb := .r2) (ro := .r3) (by decide) (by decide) (j := wE) (m := m) (by decide) h4 hv4
    (by rw [u4.other _ (by decide), e3, r2.gpr _ (by decide), u1.other _ (by decide), p3]) fun s5 h5 hv5 p5 r5 => ?_
  refine h5.strWo hv5.m (List.mem_cons_of_mem _ hE) (i := m) (i0 := m) hm (by omega_using []) (by decide) p5
    (fun j hj => (hL j hj).2) fun t ht hvt' et wt => WP.block_nil ⟨e, ?_, hv5.of (by rw [et]) (by rw [et]) (by rw [et]) wt⟩
  have v1 : (s2.gpr .r1).toNat = V σ sQ := by
    rw [r2.gpr _ (by decide), u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
  have v4 : (s5.gpr .r1).toNat = 2 ^ 32 - 1 - V σ sQ := by
    rw [r5.gpr _ (by decide), u4.gpr, BitVec.toNat_not, e3, v1]
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj), ?_⟩)
    (fun d hd => ⟨hd, rfl⟩)
  by_cases c1 : j = wE
  · subst c1; simp only [upd_self, upd_ne _ _ (show wE ≠ wD by decide)]; rw [v4]
  · by_cases c2 : j = wD
    · subst c2; simp only [upd_self, upd_ne _ _ c1]; rw [v1]
    · simp only [upd_ne _ _ c1, upd_ne _ _ c2]

/-- `dPtrs d`: `r0 :=` the address of `[wR]`'s word `b`, `r12 :=` that of `[d]`'s word `m`, `lr := n`. -/
theorem dPtrs_vp {d b m n : Nat} (hd22 : d < 22) {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat} (hPo : sPo ∈ LS) (hCm : sCm ∈ LS) (hLn : sLn ∈ LS)
    (vPo : ∀ σ, E σ → V σ sPo = 4 * b) (vCm : ∀ σ, E σ → V σ sCm = 4 * m) (vLn : ∀ σ, E σ → V σ sLn = n + 1)
    (_hn : n + 1 < 2 ^ 32) (cert : DCert (.block (dPtrs d))) :
    VP (Dk P E A L AW LW V LS P.W 22) (.block (dPtrs d))
      (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wR + 4 * b) ∧
        s.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W d + 4 * m) ∧ s.gpr .lr = BitVec.ofNat 32 n) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    unfold dPtrs
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptr_ok hv (r := .r0) (by decide) (j := wR) (by decide) fun s1 p1 r1 m1 hv1 => ?_
    have h1 := h.of_rest r1 m1 (by decide)
    refine h1.ldrSlot hv1 hPo (r := .r1) (by decide) fun s2 h2 hv2 u2 => ?_
    refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
    obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r0]) (by simp)) u3.mem
    refine ptr_ok hv3 (r := .r12) (by decide) (j := d) (by omega_using [hd22]) fun s4 p4 r4 m4 hv4 => ?_
    have h4 := h3.of_rest r4 m4 (by decide)
    refine h4.ldrSlot hv4 hCm (r := .r1) (by decide) fun s5 h5 hv5 u5 => ?_
    refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
    obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r12]) (by simp)) u6.mem
    refine h6.ldrSlot hv6 hLn (r := .lr) (by decide) fun s7 h7 hv7 u7 => ?_
    refine wp_dp (op2_imm (by decide)) fun t ut => WP.block_nil ?_
    obtain ⟨ht, hvt⟩ := h7.reg hv7 (ut.rest (ws := [.lr]) (by simp)) ut.mem
    refine ⟨⟨e, ht, hvt⟩, ?_, ?_, ?_⟩
    · rw [ut.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
        r4.gpr _ (by decide), u3.gpr, dpVal, u2.other _ (by decide), p1, u2.gpr, vPo σ e,
        VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
    · rw [ut.other _ (by decide), u7.other _ (by decide), u6.gpr, dpVal, u5.other _ (by decide), p4, u5.gpr,
        vCm σ e, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
    · rw [ut.gpr, dpVal, u7.gpr, vLn σ e]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
      omega_using []

open VG.Impl.Rsa.Arm.KeyDiv (sQ) in
/-- `corrSet`: `q̂` (`r2`) into `[wD]`'s word `m`. -/
theorem corrSet_vp {m : Nat} (hm : m < P.W) {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hD : wD ∈ LW) (hQ : sQ ∈ LS) (hL : ∀ j ∈ L, j / 2 ≠ wD) :
    VP (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r4 = BitVec.ofNat 32 (4 * m) ∧
        s.gpr .r2 = BitVec.ofNat 32 (V σ sQ)) (.block corrSet)
      (Dk P E A L (fun σ => upd (AW σ) wD (setW (AW σ wD) m (V σ sQ))) LW V LS P.W 22) := by
  refine VP.taint _ corrSet_taint (pinW (fun _ _ h => h.1.2.2) fun r hr σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hv⟩, p4, p2⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; rw [h₁.2.1, h₂.2.1]
  have ql : V σ sQ < 2 ^ 32 := by rw [← h.sl _ hQ]; exact BitVec.isLt _
  unfold corrSet
  refine ptrOff_ok (rb := .r3) (ro := .r4) (by decide) (by decide) (j := wD) (m := m) (by decide) h hv p4
    fun s1 h1 hv1 p1 r1 => ?_
  refine h1.strWo hv1.m hD (i := m) (i0 := m) hm (by omega_using []) (by decide) p1 (fun j hj => hL j hj)
    fun t ht hvt' et wt => WP.block_nil ⟨e, ?_, hv1.of (by rw [et]) (by rw [et]) (by rw [et]) wt⟩
  have v2 : (s1.gpr .r2).toNat = V σ sQ := by
    rw [r1.gpr _ (by decide), p2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  by_cases c : j = wD
  · subst c; simp only [upd_self]; rw [v2]
  · simp only [upd_ne _ _ c]

theorem setW_div_succ {y i v : Nat} (hv : v < 2 ^ 32) : setW y i v / 2 ^ (32 * (i + 1)) = y / 2 ^ (32 * (i + 1)) := by
  rw [setW_eq_win]; exact setWin_div_hi (by simpa using hv)

open VG.Impl.Rsa.Arm.KeyDiv (sQ) in
/-- `finishQ`: `[wD]`'s word `m` := `2 q`'s low word and word `m + 1` plus its top bit, and `[wE]`'s the
complements. -/
theorem finishQ_vp {m : Nat} (hm : m + 1 < P.W) {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat} (hD : wD ∈ LW) (hE : wE ∈ LW) (hQ : sQ ∈ LS)
    (hL : ∀ j ∈ L, j / 2 ≠ wD ∧ j / 2 ≠ wE) :
    VP (fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (4 * m)) (.block finishQ)
      (Dk P E A L (fun σ => upd (upd (AW σ)
        wD (setW (setW (AW σ wD) m (2 * V σ sQ % 2 ^ 32)) (m + 1)
          ((AW σ wD / 2 ^ (32 * (m + 1)) % 2 ^ 32 + V σ sQ / 2 ^ 31) % 2 ^ 32)))
        wE (setW (setW (AW σ wE) m (2 ^ 32 - 1 - 2 * V σ sQ % 2 ^ 32)) (m + 1)
          ((2 ^ 32 - V σ sQ / 2 ^ 31 + AW σ wE / 2 ^ (32 * (m + 1)) % 2 ^ 32) % 2 ^ 32))) LW V LS P.W 22) := by
  refine VP.taint _ finishQ_taint (pinW (fun _ _ h => h.1.2.2) fun r hr σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    fun σ s ⟨⟨e, h, hv⟩, p1⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; rw [h₁.2, h₂.2]
  have ql : V σ sQ < 2 ^ 32 := by rw [← h.sl _ hQ]; exact BitVec.isLt _
  unfold finishQ
  rw [List.append_assoc]
  refine ptrOff_ok (rb := .r12) (ro := .r1) (by decide) (by decide) (j := wE) (m := m) (by decide) h hv p1
    fun s1 h1 hv1 p12 r1' => ?_
  refine ptrOffC_ok (rb := .r10) (ro := .r1) (by decide) (by decide) (j := wD) (m := m) (by decide) h1 hv1
    (by rw [r1'.gpr _ (by decide), p1]) fun s2 h2 hv2 p10 r2' => ?_
  refine h2.ldrSlot hv2 hQ (r := .r1) (by decide) fun s3 h3 hv3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r2]) (by simp)) u4.mem
  have q10 : s4.gpr .r10 = P.B + BitVec.ofNat 32 (arr P.W wD + 4 * m) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), p10]
  have q12 : s4.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W wE + 4 * m) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), r2'.gpr _ (by decide), p12]
  have va : (s4.gpr .r2).toNat = 2 * V σ sQ % 2 ^ 32 := by
    rw [u4.gpr, dpVal, u3.gpr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]; omega_using []
  refine h4.strWo hv4.m hD (i := m) (i0 := m) (by omega_using [hm]) (by omega_using []) (by decide) q10 (fun j hj => (hL j hj).1)
    fun s5 h5 _ e5 w5 => ?_
  have hv5 : Ws s5 P.B P.Z P.W 22 := hv4.of (by rw [e5]) (by rw [e5]) (by rw [e5]) w5
  refine wp_mvn (op2_reg _ _) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r2]) (by simp)) u6.mem
  refine h6.strWo hv6.m (List.mem_cons_of_mem _ hE) (i := m) (i0 := m) (by omega_using [hm]) (by omega_using []) (by decide)
    (by rw [u6.other _ (by decide), e5, q12]) (fun j hj => (hL j hj).2) fun s7 h7 _ e7 w7 => ?_
  have hv7 : Ws s7 P.B P.Z P.W 22 := hv6.of (by rw [e7]) (by rw [e7]) (by rw [e7]) w7
  refine wp_mov (op2_lsr (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have r10_8 : s8.gpr .r10 = P.B + BitVec.ofNat 32 (arr P.W wD + 4 * m) := by
    rw [u8.other _ (by decide), e7, u6.other _ (by decide), e5, q10]
  have r12_8 : s8.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W wE + 4 * m) := by
    rw [u8.other _ (by decide), e7, u6.other _ (by decide), e5, q12]
  have hb : (s8.gpr .r3).toNat = V σ sQ / 2 ^ 31 := by
    rw [u8.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e7, u6.other _ (by decide), e5,
      u4.other _ (by decide), u3.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ql]
  refine h8.ldrWo hv8.m (List.mem_cons_of_mem _ hD |> List.mem_cons_of_mem _) (i := m + 1) (i0 := m) (by omega_using [hm])
    (by omega_using []) (by decide) r10_8 (by decide) fun s9 h9 _ u9 => ?_
  have hv9 : Ws s9 P.B P.Z P.W 22 := hv8.of_upd u9 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s10 u10 => ?_
  obtain ⟨h10, hv10⟩ := h9.reg hv9 (u10.rest (ws := [.r4]) (by simp)) u10.mem
  refine h10.strWo hv10.m (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (i := m + 1) (i0 := m) (by omega_using [hm])
    (by omega_using []) (by decide) (by rw [u10.other _ (by decide), u9.other _ (by decide), r10_8])
    (fun j hj => (hL j hj).1) fun s11 h11 _ e11 w11 => ?_
  have hv11 : Ws s11 P.B P.Z P.W 22 := hv10.of (by rw [e11]) (by rw [e11]) (by rw [e11]) w11
  refine h11.ldrWo hv11.m (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (i := m + 1) (i0 := m) (by omega_using [hm]) (by omega_using []) (by decide)
    (by rw [e11, u10.other _ (by decide), u9.other _ (by decide), r12_8]) (by decide) fun s12 h12 _ u12 => ?_
  have hv12 : Ws s12 P.B P.Z P.W 22 := hv11.of_upd u12 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s13 u13 => ?_
  obtain ⟨h13, hv13⟩ := h12.reg hv12 (u13.rest (ws := [.r4]) (by simp)) u13.mem
  refine h13.strWo hv13.m (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (i := m + 1) (i0 := m) (by omega_using [hm]) (by omega_using []) (by decide)
    (by rw [u13.other _ (by decide), u12.other _ (by decide), e11, u10.other _ (by decide),
      u9.other _ (by decide), r12_8]) (fun j hj => (hL j hj).2) fun t ht _ et wt =>
    WP.block_nil ⟨e, ?_, hv13.of (by rw [et]) (by rw [et]) (by rw [et]) wt⟩
  have hb10 : (s9.gpr .r3).toNat = V σ sQ / 2 ^ 31 := by rw [u9.other _ (by decide), hb]
  have hbl : V σ sQ / 2 ^ 31 < 2 ^ 32 := by omega_using [ql]
  have vD : (s10.gpr .r4).toNat = (AW σ wD / 2 ^ (32 * (m + 1)) % 2 ^ 32 + V σ sQ / 2 ^ 31) % 2 ^ 32 := by
    rw [u10.gpr, dpVal, BitVec.toNat_add, u9.gpr, u9.other .r3 (by decide), hb, BitVec.toNat_ofNat, Nat.mod_mod]
    simp only [upd_self, upd_ne _ _ (show wD ≠ wE by decide)]
    rw [setW_div_succ (BitVec.isLt _)]
  have vE : (s13.gpr .r4).toNat = (2 ^ 32 - V σ sQ / 2 ^ 31 + AW σ wE / 2 ^ (32 * (m + 1)) % 2 ^ 32) % 2 ^ 32 := by
    rw [u13.gpr, dpVal, BitVec.toNat_sub, u12.gpr, u12.other .r3 (by decide), e11, u10.other .r3 (by decide), hb10,
      BitVec.toNat_ofNat, Nat.mod_mod]
    simp only [upd_self, upd_ne _ _ (show wE ≠ wD by decide)]
    rw [setW_div_succ (BitVec.isLt _)]
  have vNa : (s6.gpr .r2).toNat = 2 ^ 32 - 1 - 2 * V σ sQ % 2 ^ 32 := by
    rw [u6.gpr, BitVec.toNat_not, e5, va]
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  · simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hj)))
  · by_cases c1 : j = wE
    · subst c1
      simp only [upd_self, upd_ne _ _ (show wE ≠ wD by decide)]
      rw [vE, vNa]
    · by_cases c2 : j = wD
      · subst c2
        simp only [upd_self, upd_ne _ _ c1]
        rw [vD, va]
      · simp only [upd_ne _ _ c1, upd_ne _ _ c2]

open VG.Impl.Rsa.Arm.KeyDiv (sD1) in
/-- `finishD1`: `d₁ :=` the word `W / 2 - 2` of `[wD] / 2`. -/
theorem finishD1_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} (hW : 4 ≤ P.W)
    (hD : wD ∈ LW) :
    VP (Dk P E A L AW LW V LS P.W 22) (.block finishD1)
      (Dk P E A L AW LW (fun σ => upd (V σ) sD1 (AW σ wD / 2 ^ (32 * (P.W / 2 - 2)) % 2 ^ 32 / 2 +
        AW σ wD / 2 ^ (32 * (P.W / 2 - 1)) % 2 ^ 32 % 2 * 2 ^ 31)) (sD1 :: LS) P.W 22) :=
  VP.dctx finishD1_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    have sz := h.sizes
    have Wl := sz.Wle
    have fD := fitZ_W sz (show wD < 22 by decide)
    simp only [S] at fD
    unfold finishD1
    refine ptr_ok hv (r := .r12) (by decide) (j := wD) (by decide) fun s1 p1 r1 m1 hv1 => ?_
    have h1 := h.of_rest r1 m1 (by decide)
    refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
    obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r12]) (by simp)) u2.mem
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
    obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r12]) (by simp)) u3.mem
    have q3 : s3.gpr .r12 = P.B + BitVec.ofNat 32 (arr P.W wD + 4 * (P.W / 2 - 2)) := by
      rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, hv1.r9, VG.Proof.Rsa.Arm.KeyDiv.shl1_val (by omega_using [Wl]),
        VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
        sub_ofNat_eq _ (by omega_using [hW]) (by decide)]
      have : P.W = 2 * P.w + 2 := rfl
      congr 2; omega_using [hW, this]
    refine h3.ldrWo hv3.m hD (i := P.W / 2 - 2) (i0 := P.W / 2 - 2) (by omega_using [hW]) (by omega_using []) (by decide) q3
      (by decide) fun s4 h4 _ u4 => ?_
    have hv4 : Ws s4 P.B P.Z P.W 22 := hv3.of_upd u4 (by decide) (by decide) (by decide)
    refine h4.ldrWo hv4.m hD (i := P.W / 2 - 1) (i0 := P.W / 2 - 2) (by omega_using [hW]) (by omega_using [hW]) (by decide)
      (by rw [u4.other _ (by decide), q3]) (by decide) fun s5 h5 _ u5 => ?_
    have hv5 : Ws s5 P.B P.Z P.W 22 := hv4.of_upd u5 (by decide) (by decide) (by decide)
    refine wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
    obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r2]) (by simp)) u6.mem
    refine wp_dp (op2_lsl (by decide)) fun s7 u7 => ?_
    obtain ⟨h7, hv7⟩ := h6.reg hv6 (u7.rest (ws := [.r2]) (by simp)) u7.mem
    refine h7.strSlot hv7 (d := sD1) (r := .r2) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
    have v : (s7.gpr .r2).toNat = AW σ wD / 2 ^ (32 * (P.W / 2 - 2)) % 2 ^ 32 / 2 +
        AW σ wD / 2 ^ (32 * (P.W / 2 - 1)) % 2 ^ 32 % 2 * 2 ^ 31 := by
      rw [u7.gpr, dpVal, u6.gpr, u6.other .r3 (by decide), shr1_or, u5.other .r2 (by decide), u4.gpr, u5.gpr,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_mod]
    rwa [v] at ht

/-- The next digit's offsets and length. -/
theorem digNext_vp {po mo ln cm : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hPo : sPo ∈ LS) (hMo : sMo ∈ LS) (hLn : sLn ∈ LS) (hCm : sCm ∈ LS) (vPo : ∀ σ, E σ → V σ sPo = po)
    (vMo : ∀ σ, E σ → V σ sMo = mo) (vLn : ∀ σ, E σ → V σ sLn = ln) (vCm : ∀ σ, E σ → V σ sCm = cm)
    (hmo : mo + 4 < 2 ^ 32) (hln : ln + 1 < 2 ^ 32) :
    VP (Dk P E A L AW LW V LS P.W 22) (.block digNext)
      (Dk P E A L AW LW (fun σ => upd (upd (upd (upd (V σ) sPo ((po + 2 ^ 32 - 8) % 2 ^ 32)) sMo (mo + 4))
        sLn (ln + 1)) sCm ((cm + 2 ^ 32 - 4) % 2 ^ 32)) LS P.W 22) :=
  VP.dctx digNext_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    have lpo : po < 2 ^ 32 := by rw [← vPo σ e, ← h.sl _ hPo]; exact BitVec.isLt _
    have lcm : cm < 2 ^ 32 := by rw [← vCm σ e, ← h.sl _ hCm]; exact BitVec.isLt _
    unfold digNext
    refine h.ldrSlot hv hPo (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
    refine h2.strSlot hv2 (d := sPo) (r := .r1) (by decide) fun s3 h3 hv3 _ _ => ?_
    refine h3.ldrSlot hv3 (List.mem_cons_of_mem _ hMo) (r := .r1) (by decide) fun s4 h4 hv4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
    obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
    refine h5.strSlot hv5 (d := sMo) (r := .r1) (by decide) fun s6 h6 hv6 _ _ => ?_
    refine h6.ldrSlot hv6 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hLn)) (r := .r1) (by decide)
      fun s7 h7 hv7 u7 => ?_
    refine wp_dp (op2_imm (by decide)) fun s8 u8 => ?_
    obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r1]) (by simp)) u8.mem
    refine h8.strSlot hv8 (d := sLn) (r := .r1) (by decide) fun s9 h9 hv9 _ _ => ?_
    refine h9.ldrSlot hv9 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hCm))) (r := .r1)
      (by decide) fun s10 h10 hv10 u10 => ?_
    refine wp_dp (op2_imm (by decide)) fun s11 u11 => ?_
    obtain ⟨h11, hv11⟩ := h10.reg hv10 (u11.rest (ws := [.r1]) (by simp)) u11.mem
    refine h11.strSlot hv11 (d := sCm) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
    have e2 : (s2.gpr .r1).toNat = (po + 2 ^ 32 - 8) % 2 ^ 32 := by
      rw [u2.gpr, dpVal, u1.gpr, vPo σ e, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lpo,
        show (8 : BitVec 32).toNat = 8 from rfl]; omega_using []
    have e5 : (s5.gpr .r1).toNat = mo + 4 := by
      rw [u5.gpr, dpVal, u4.gpr]
      simp only [upd_ne _ _ (show sMo ≠ sPo by decide)]
      rw [vMo σ e, BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]; omega_using [hmo]
    have e8 : (s8.gpr .r1).toNat = ln + 1 := by
      rw [u8.gpr, dpVal, u7.gpr]
      simp only [upd_ne _ _ (show sLn ≠ sPo by decide), upd_ne _ _ (show sLn ≠ sMo by decide)]
      rw [vLn σ e, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]; omega_using [hln]
    have e11 : (s11.gpr .r1).toNat = (cm + 2 ^ 32 - 4) % 2 ^ 32 := by
      rw [u11.gpr, dpVal, u10.gpr]
      simp only [upd_ne _ _ (show sCm ≠ sPo by decide), upd_ne _ _ (show sCm ≠ sMo by decide),
        upd_ne _ _ (show sCm ≠ sLn by decide)]
      rw [vCm σ e, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lcm,
        show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
    rw [e11, e8, e5, e2] at ht
    exact ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨by simp [hd], rfl⟩)

end

/-! ## The digits' math: the roots of `X'`'s top `2 j` words -/

section
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa.RecoverDet (isqrt_sq_le lt_succ_isqrt_sq)
open VG.Proof.Bignum.SqrtRem (IsDigit sqrt_of_rem)

/-- `X'`'s top `2 j` words, of `W`. -/
abbrev topA (W x j : Nat) : Nat := x / 2 ^ (32 * (W - 2 * j))
abbrev sJ (W x j : Nat) : Nat := isqrt (topA W x j)
abbrev rJ (W x j : Nat) : Nat := topA W x j - sJ W x j * sJ W x j

theorem le_isqrt {s x : Nat} (h : s * s ≤ x) : s ≤ isqrt x := by
  refine Nat.le_of_not_lt fun c => ?_
  have := lt_succ_isqrt_sq x
  have : (isqrt x + 1) * (isqrt x + 1) ≤ s * s := Nat.mul_le_mul c c
  omega_arith

theorem rJ_le {W x j : Nat} : sJ W x j * sJ W x j + rJ W x j = topA W x j ∧ rJ W x j ≤ 2 * sJ W x j := by
  have lo := isqrt_sq_le (topA W x j)
  have hi := lt_succ_isqrt_sq (topA W x j)
  have e : (isqrt (topA W x j) + 1) * (isqrt (topA W x j) + 1) =
      isqrt (topA W x j) * isqrt (topA W x j) + 2 * isqrt (topA W x j) + 1 := by ring
  simp only [rJ, sJ]; omega_using [lo, hi, e]

/-- The roots are normalized: `2^(32 j - 1) ≤ s_j < 2^(32 j)`. -/
theorem sJ_bounds {W x j : Nat} (hx1 : 2 ^ (32 * W - 2) ≤ x) (hx2 : x < 2 ^ (32 * W)) (hj : 1 ≤ j)
    (hjW : 2 * j ≤ W) : 2 ^ (32 * j - 1) ≤ sJ W x j ∧ sJ W x j < 2 ^ (32 * j) := by
  have p := Nat.two_pow_pos (32 * (W - 2 * j))
  have A1 : 2 ^ (64 * j - 2) ≤ topA W x j := by
    rw [Nat.le_div_iff_mul_le p, ← Nat.pow_add, show 64 * j - 2 + 32 * (W - 2 * j) = 32 * W - 2 by omega_using [hj, hjW]]
    exact hx1
  have A2 : topA W x j < 2 ^ (64 * j) := by
    rw [Nat.div_lt_iff_lt_mul p, ← Nat.pow_add, show 64 * j + 32 * (W - 2 * j) = 32 * W by omega_using [hjW]]
    exact hx2
  refine ⟨le_isqrt ?_, ?_⟩
  · rw [← Nat.pow_add, show 32 * j - 1 + (32 * j - 1) = 64 * j - 2 by omega_using []]; exact A1
  · refine Nat.lt_of_not_le fun c => ?_
    have := Nat.mul_le_mul c c
    rw [← Nat.pow_add, show 32 * j + 32 * j = 64 * j by omega_using []] at this
    have := isqrt_sq_le (topA W x j)
    simp only [sJ] at *
    omega_arith

/-- The next pair of words. -/
abbrev pairP (W x j : Nat) : Nat := x / 2 ^ (32 * (W - 2 * j - 2)) % 2 ^ 64

theorem topA_succ {W x j : Nat} (hjW : 2 * j + 2 ≤ W) :
    topA W x (j + 1) = topA W x j * 2 ^ 64 + pairP W x j := by
  simp only [topA, pairP]
  rw [show W - 2 * (j + 1) = W - 2 * j - 2 by omega_using [],
    show 32 * (W - 2 * j) = 32 * (W - 2 * j - 2) + 64 by omega_using [hjW], Nat.pow_add, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (x / 2 ^ (32 * (W - 2 * j - 2))) (2 ^ 64)
  rw [Nat.mul_comm] at this; omega_using []

/-- The digit `q_j = s_{j+1} - s_j β`, of `R = r_j β² + P_j`. -/
theorem digit_rel {W x j : Nat} (hjW : 2 * j + 2 ≤ W) :
    let s := sJ W x j
    let R := rJ W x j * 2 ^ 64 + pairP W x j
    s * 2 ^ 32 ≤ sJ W x (j + 1) ∧ sJ W x (j + 1) - s * 2 ^ 32 < 2 ^ 32 ∧
      IsDigit (2 ^ 32) s R (sJ W x (j + 1) - s * 2 ^ 32) ∧
      rJ W x (j + 1) = R - (2 * s * 2 ^ 32 + (sJ W x (j + 1) - s * 2 ^ 32)) * (sJ W x (j + 1) - s * 2 ^ 32) := by
  intro s R
  have hA := topA_succ (x := x) hjW
  have Pl : pairP W x j < 2 ^ 64 := Nat.mod_lt _ (by decide)
  simp only [R, s, rJ, sJ] at *
  rw [hA]
  generalize topA W x j = A
  generalize pairP W x j = P at Pl ⊢
  have a1 := isqrt_sq_le A
  have a2 := lt_succ_isqrt_sq A
  have b1 := isqrt_sq_le (A * 2 ^ 64 + P)
  have b2 := lt_succ_isqrt_sq (A * 2 ^ 64 + P)
  generalize isqrt A = s0 at *
  generalize isqrt (A * 2 ^ 64 + P) = s1 at *
  have e2 : (s0 + 1) * (s0 + 1) = s0 * s0 + 2 * s0 + 1 := by ring
  have f0 : s0 * 2 ^ 32 * (s0 * 2 ^ 32) = s0 * s0 * 2 ^ 64 := by ring
  have g1 : s0 * 2 ^ 32 ≤ s1 := by
    refine Nat.le_of_not_lt fun c => ?_
    have : (s1 + 1) * (s1 + 1) ≤ s0 * 2 ^ 32 * (s0 * 2 ^ 32) := Nat.mul_le_mul c c
    omega_using [a1, b2, f0, this]
  have g2 : s1 < (s0 + 1) * 2 ^ 32 := by
    refine Nat.lt_of_not_le fun c => ?_
    have : (s0 + 1) * 2 ^ 32 * ((s0 + 1) * 2 ^ 32) ≤ s1 * s1 := Nat.mul_le_mul c c
    have : (s0 + 1) * 2 ^ 32 * ((s0 + 1) * 2 ^ 32) = (s0 * s0 + 2 * s0 + 1) * 2 ^ 64 := by ring
    omega_arith
  obtain ⟨q, rfl⟩ : ∃ q, s1 = s0 * 2 ^ 32 + q := ⟨s1 - s0 * 2 ^ 32, by omega_using [g1]⟩
  have hq : q < 2 ^ 32 := by
    have : (s0 + 1) * 2 ^ 32 = s0 * 2 ^ 32 + 2 ^ 32 := by ring
    omega_using [g2]
  rw [Nat.add_sub_cancel_left]
  have e3 : (s0 * 2 ^ 32 + q) * (s0 * 2 ^ 32 + q) = s0 * s0 * 2 ^ 64 + (2 * s0 * 2 ^ 32 + q) * q := by ring
  have e4 : (s0 * 2 ^ 32 + q + 1) * (s0 * 2 ^ 32 + q + 1) =
      s0 * s0 * 2 ^ 64 + (2 * s0 * 2 ^ 32 + (q + 1)) * (q + 1) := by ring
  refine ⟨by omega_using [], hq, ⟨by omega_using [a1, b1, e3], by omega_using [a1, b2, e4]⟩, by omega_using [a1, e3, b1]⟩

/-- The top word of the roots does not change. -/
theorem top_word {s q j : Nat} (hq : q < 2 ^ 32) (hj : 1 ≤ j) :
    (s * 2 ^ 32 + q) / 2 ^ (32 * j) = s / 2 ^ (32 * (j - 1)) := by
  rw [show 32 * j = 32 + 32 * (j - 1) by omega_using [hj], Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hq, Nat.zero_add]

end

/-! ## The corrections' math -/

section
open VG.Proof.Bignum.WordStep32 (twos_eq twos_neg addIfNeg twos_of_add)

theorem eq_twos {W t : Nat} {v : Int} (_ht : t < W) (h : (t : Int) % W = v % W) : t = VG.Proof.Bignum.WordStep32.twos W v := by
  unfold VG.Proof.Bignum.WordStep32.twos; rw [← h, Int.emod_eq_of_lt (by omega_using []) (by omega_using [_ht])]; simp

theorem sub32_negadd {n t g : Nat} (_ht : t < 2 ^ (32 * n)) (hg : g < 2 ^ (32 * n)) :
    sub32 n t (sub32 n 0 g) = (t + g) % 2 ^ (32 * n) := by
  unfold sub32
  rcases Nat.eq_zero_or_pos g with rfl | hg0
  · simp
  · rw [Nat.zero_add, Nat.mod_eq_of_lt (show 2 ^ (32 * n) - g < 2 ^ (32 * n) by omega_using [_ht, hg0]),
      show t + 2 ^ (32 * n) - (2 ^ (32 * n) - g) = t + g by omega_using [hg]]

/-- A correction: from `t = R - (c + x) x` (modulo `M`), its sign `b` and `R - (c + (x - b)) (x - b)`. -/
theorem fix_step {n R c q x : Nat} (hn : 2 ≤ n) (hx32 : x < 2 ^ 32)
    (hqR : (c + q) * q ≤ R) (hRq : R < (c + (q + 1)) * (q + 1)) (hxq : q ≤ x) (hx : x ≤ q + 2)
    (hRW : 2 * (R + 1) ≤ 2 ^ (32 * n)) (hcW : 2 * ((c + (q + 2)) * (q + 2)) < 2 ^ (32 * n))
    (hcx : c + 2 * x < 2 ^ (32 * n)) :
    VG.Proof.Bignum.WordStep32.twos (2 ^ (32 * n)) ((R : Int) - ((c + x) * x : Nat)) / 2 ^ (32 * n - 1) = (if q < x then 1 else 0) ∧
    fixR n (VG.Proof.Bignum.WordStep32.twos (2 ^ (32 * n)) ((R : Int) - ((c + x) * x : Nat))) c x =
      VG.Proof.Bignum.WordStep32.twos (2 ^ (32 * n)) ((R : Int) - ((c + (x - if q < x then 1 else 0)) * (x - if q < x then 1 else 0) : Nat)) := by
  obtain ⟨l1, l2, neg, add⟩ := VG.Proof.Rsa.Arm.RecoverDet.sq_fix hqR hRq hxq hx hRW hcW
  have hM2 : (2 : Nat) ^ (32 * n) = 2 * 2 ^ (32 * n - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, 32 * n = m + 1 := ⟨32 * n - 1, by omega_using [hn]⟩
    rw [hm, Nat.add_sub_cancel, Nat.pow_succ]; omega_using []
  have hM : (2 : Nat) ^ (32 * n) / 2 = 2 ^ (32 * n - 1) := by omega_using [hM2]
  have tl : VG.Proof.Bignum.WordStep32.twos (2 ^ (32 * n)) ((R : Int) - ((c + x) * x : Nat)) < 2 ^ (32 * n) := by
    unfold VG.Proof.Bignum.WordStep32.twos
    have := Int.emod_lt_of_pos ((R : Int) - ((c + x) * x : Nat)) (show (0 : Int) < ((2 ^ (32 * n) : Nat) : Int) by
      exact_mod_cast Nat.two_pow_pos _)
    have := Int.emod_nonneg ((R : Int) - ((c + x) * x : Nat)) (show ((2 ^ (32 * n) : Nat) : Int) ≠ 0 by
      exact_mod_cast (Nat.two_pow_pos _).ne')
    omega_using []
  generalize et : VG.Proof.Bignum.WordStep32.twos (2 ^ (32 * n)) ((R : Int) - ((c + x) * x : Nat)) = t at tl
  have hb : t / 2 ^ (32 * n - 1) = if 2 ^ (32 * n) / 2 ≤ t then 1 else 0 := by
    rw [hM]; split
    · rename_i h0
      have := Nat.div_add_mod t (2 ^ (32 * n - 1))
      have := Nat.mod_lt t (Nat.two_pow_pos (32 * n - 1))
      have : t / 2 ^ (32 * n - 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [hM2, tl]
      have : 1 ≤ t / 2 ^ (32 * n - 1) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega_using [h0])
      omega_arith
    · exact Nat.div_eq_of_lt (by omega_arith)
  have sg := twos_neg l1 l2
  rw [et] at sg
  have bq : (if 2 ^ (32 * n) / 2 ≤ t then 1 else 0) = (if q < x then 1 else 0) := by
    by_cases c1 : q < x
    · simp only [c1, ↓reduceIte, sg.mpr (neg.mpr c1)]
    · simp only [c1, ↓reduceIte, show ¬ (2 ^ (32 * n) / 2 ≤ t) from fun h => c1 (neg.mp (sg.mp h))]
  refine ⟨hb.trans bq, ?_⟩
  have hM0 : (2 ^ (32 * n) : Nat) / 2 = 2 ^ (32 * n) / 2 := rfl
  have h64 : (2 : Nat) ^ 64 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega_using [hn])
  have h32 : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by rw [← Nat.pow_add]
  have hx2 : 2 * x < 2 ^ 64 := by omega_using [hx32]
  rw [← add]
  refine twos_of_add (W := 2 ^ (32 * n)) (c := (t + if 2 ^ (32 * n) / 2 ≤ t then c + 2 * x - 1 else 0) / 2 ^ (32 * n))
    (by exact_mod_cast l1) (by exact_mod_cast l2) ?_ ?_ et.symm (sub32_lt _ _ _) ?_ ?_
  · rw [add]; push_cast at l1 ⊢
    have := VG.Proof.Rsa.Arm.RecoverDet.sq_fix (W := 2 ^ (32 * n)) hqR hRq (show q ≤ x - (if q < x then 1 else 0) by split <;> omega_arith)
      (by split <;> omega_arith) hRW hcW
    exact_mod_cast this.1
  · rw [add]
    have := VG.Proof.Rsa.Arm.RecoverDet.sq_fix (W := 2 ^ (32 * n)) hqR hRq (show q ≤ x - (if q < x then 1 else 0) by split <;> omega_arith)
      (by split <;> omega_arith) hRW hcW
    exact_mod_cast this.2.1
  · have : (if 2 ^ (32 * n) / 2 ≤ t then c + 2 * x - 1 else 0) < 2 ^ (32 * n) := by split <;> omega_arith
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [tl, this]
  · unfold fixR fixG
    rw [hb]
    split
    · rename_i hle
      have x1 : 1 ≤ x := by
        have := bq; simp only [hle, ↓reduceIte] at this; split at this <;> omega_arith
      have eE : fixE x = 2 * x - 1 := by
        unfold fixE; rw [show 2 * x + 2 ^ 64 - 1 = (2 * x - 1) + 2 ^ 64 by omega_using [x1], Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega_using [hx32])]
      have eG : sub32 n c (sub32 n 0 (2 * x - 1)) = c + 2 * x - 1 := by
        rw [sub32_negadd (by omega_using [hqR, hRq, hRW, hcW, hcx, l1, l2, neg, hM2, hM, tl, sg, hM0, h64, hle]) (by omega_using [hx32, hxq, hx, hRW, hcW, hcx, l1, l2, neg, hM2, hM, tl, sg, hM0, h64, hx2, hle, x1]), Nat.mod_eq_of_lt (by omega_using [hx32, hqR, hRq, hxq, hx, hRW, hcW, hcx, l1, l2, neg, hM2, hM, tl, sg, hM0, h64, hx2, hle, x1])]; omega_using [hx32, hqR, hRq, hxq, hx, hcW, hcx, l1, l2, neg, sg, hx2, x1]
      simp only [show ¬ (1 = 0) from by decide, ↓reduceIte, eE, eG]
      rw [sub32_negadd tl (by omega_using [hx32, hqR, hRq, hxq, hx, hRW, hcW, hcx, l1, l2, neg, hM2, hM, tl, sg, hM0, h64, hx2, hle, x1])]
      have := Nat.div_add_mod (t + (c + 2 * x - 1)) (2 ^ (32 * n))
      omega_using [hx32, hqR, hRq, hxq, hx, hRW, hcW, hcx, l1, l2, neg, hM2, hM, tl, hb, sg, hM0, h64, hx2, hle, x1, this]
    · simp only [↓reduceIte]
      rw [show sub32 n t (sub32 n 0 0) = t by unfold sub32; simp [Nat.add_mod_right, Nat.mod_eq_of_lt tl]]
      rw [Nat.div_eq_of_lt (by omega_arith)]; omega_using []

end

end VG.Proof.Rsa.Arm.RecoverDet
