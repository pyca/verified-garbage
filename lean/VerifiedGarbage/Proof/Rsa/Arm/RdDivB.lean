module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdDiv

import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.KdNorm
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.Arm.RdTaint
import VerifiedGarbage.Proof.Rsa.Arm.KeyWs

/-! # `vg_rsa_recover_primes_det` on ARMv7: `b - 1` by words

`divB_vp`: `m + 1` and `n - r` shifted left by `s' = W / 2 - wl(m + 1)` words, `wl` the number of
words of `m + 1` (`wlen_vp`), by masked stages of `2^k` words (`stages_vp`), so that the divisor's top
word is word `W / 2 - 1`; then the division by words with the quotient (`divMid_vp`), whether the
remainder is zero, and `b - 1` the quotient.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Rsa (sub32 b2n)

/-! ## Bits and words -/

/-- `nzR1`'s value: `(x ||| -x) >>> 31` is whether `x` is not zero. -/
theorem nz_bit (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx; decide
  · simp only [hx, ite_false]
    apply BitVec.eq_of_toNat_eq
    have a0 : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    have al := x.isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
      show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Nat.mod_eq_of_lt (by omega),
      show (1 : BitVec 32).toNat = 1 from rfl]
    have l1 : x.toNat ≤ x.toNat ||| (2 ^ 32 - x.toNat) := Nat.left_le_or
    have l2 : 2 ^ 32 - x.toNat ≤ x.toNat ||| (2 ^ 32 - x.toNat) := by rw [Nat.or_comm]; exact Nat.left_le_or
    have l3 : x.toNat ||| (2 ^ 32 - x.toNat) < 2 ^ 32 := Nat.or_lt_two_pow al (by omega)
    omega

/-- A word of a number in memory. -/
theorem w32_digit (m : Mem) (b : Addr) (d : Nat) {k n : Nat} (hk : k < n) :
    w32 m b (d + 4 * k) = val32 m b d n / 2 ^ (32 * k) % 2 ^ 32 := by
  have h1 := val32_append m b d k (n - k)
  have h2 : val32 m b (d + 4 * k) (n - k) = w32 m b (d + 4 * k) + 2 ^ 32 * val32 m b (d + 4 * k + 4) (n - k - 1) := by
    have e : n - k = n - k - 1 + 1 := by omega
    conv_lhs => rw [e]
    rw [val32]
  rw [Nat.add_sub_cancel' (Nat.le_of_lt hk)] at h1
  rw [h1, h2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- The number of words of `x`'s low `k`: one more than the index of its top word not zero. -/
def wlOf (x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if x / 2 ^ (32 * k) % 2 ^ 32 = 0 then wlOf x k else k + 1

theorem wlOf_le (x : Nat) : ∀ k, wlOf x k ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    simp only [wlOf]
    split
    · have := wlOf_le x k; omega
    · exact Nat.le_refl _

theorem wlOf_spec (x : Nat) : ∀ k, x % 2 ^ (32 * k) < 2 ^ (32 * wlOf x k) ∧
    (wlOf x k ≠ 0 → 2 ^ (32 * (wlOf x k - 1)) ≤ x % 2 ^ (32 * k))
  | 0 => by simp only [wlOf, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; exact ⟨Nat.one_pos, fun h => absurd rfl h⟩
  | k + 1 => by
    have e : x % 2 ^ (32 * (k + 1)) = x % 2 ^ (32 * k) + 2 ^ (32 * k) * (x / 2 ^ (32 * k) % 2 ^ 32) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
    obtain ⟨ih1, ih2⟩ := wlOf_spec x k
    simp only [wlOf]
    split
    · rename_i h0; rw [e, h0, Nat.mul_zero, Nat.add_zero]; exact ⟨ih1, ih2⟩
    · rename_i h0
      refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), fun _ => ?_⟩
      rw [e, Nat.add_sub_cancel]
      have : 2 ^ (32 * k) ≤ 2 ^ (32 * k) * (x / 2 ^ (32 * k) % 2 ^ 32) := Nat.le_mul_of_pos_right _ (by omega)
      omega

section
variable {P : RP}

/-- Before word `k` of the word length of the narrow `[j]`: `k` at `sCd`, the length of its low `k`
words at `sCa`, the word's address in `r0` and the words left in `lr`. -/
abbrev WI (P : RP) (j : Nat) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat) (LW : List Nat)
    (V : State → Nat → Nat) (LS : List Nat) (k : Nat) (σ s : State) : Prop :=
  (KS P σ (A σ) L (AW σ) LW (upd (upd (V σ) sCd k) sCa (wlOf (A σ j) k)) (sCa :: sCd :: LS) s ∧
    Ws s P.B P.Z P.w nArr) ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.w j + 4 * k) ∧
    s.gpr .lr = BitVec.ofNat 32 (P.w - k)

theorem mask_sel (a b : BitVec 32) (p : Prop) [Decidable p] :
    a &&& ~~~(0 - (if p then 0 else 1)) ||| b &&& (0 - (if p then 0 else 1)) = if p then a else b := by
  have e : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by decide
  by_cases c : p <;> simp [c] <;> rw [e, BitVec.and_allOnes]

theorem wlStep_ok {j k : Nat} {L LW LS : List Nat} {A AW V : State → Nat → Nat} {σ s : State} (hj : j ∈ L)
    (hk : k < P.w) (h : WI P j A L AW LW V LS k σ s) :
    WP isa (.block wlStep) s fun t => WI P j A L AW LW V LS (k + 1) σ t ∧ t.z = decide (P.w - (k + 1) = 0) := by
  obtain ⟨⟨h, hv⟩, p0, plr⟩ := h
  have sz := h.sizes
  have wl := sz.wle
  have fj := fit_w sz (h.live_lt j hj)
  have fjZ := fitZ_w sz (h.live_lt j hj)
  simp only [S] at fj fjZ
  have dig : (s.mem.readW (off (State.addr P.B) (arr P.w j + 4 * k)) 32).toNat = A σ j / 2 ^ (32 * k) % 2 ^ 32 := by
    show w32 s.mem (State.addr P.B) (arr P.w j + 4 * k) = _
    have := h.arrs j hj
    simp only [num] at this
    rw [w32_digit _ _ _ hk, this]
  unfold wlStep nzR1
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (by decide) (by rw [p0, BitVec.add_zero]; exact hv.addr (by omega)) (hv.read (by omega)) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r2]) (by simp)) u3.mem
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r2]) (by simp)) u4.mem
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r1]) (by simp)) u6.mem
  have nz : s6.gpr .r1 = if s1.gpr .r1 = 0 then 0 else 1 := by
    rw [u6.gpr, u5.gpr, dpVal, u4.gpr, dpVal, u3.gpr, u4.other .r1 (by decide), u3.other .r1 (by decide),
      u2.other .r1 (by decide), ← nz_bit]
  refine h6.ldrSlot hv6 (d := sCd) (by simp) (r := .r2) (by decide) fun s7 h7 hv7 u7 => ?_
  refine wp_dp (op2_imm (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r2]) (by simp)) u8.mem
  refine h8.strSlot hv8 (d := sCd) (r := .r2) (by decide) fun s9 h9 hv9 g9 _ => ?_
  refine wp_mov (op2_imm (by decide)) fun s10 u10 => ?_
  obtain ⟨h10, hv10⟩ := h9.reg hv9 (u10.rest (ws := [.r3]) (by simp)) u10.mem
  refine wp_dp (op2_reg _ _) fun s11 u11 => ?_
  obtain ⟨h11, hv11⟩ := h10.reg hv10 (u11.rest (ws := [.r1]) (by simp)) u11.mem
  refine h11.ldrSlot hv11 (d := sCa) (by simp) (r := .r3) (by decide) fun s12 h12 hv12 u12 => ?_
  refine wp_dp (op2_reg _ _) fun s13 u13 => ?_
  obtain ⟨h13, hv13⟩ := h12.reg hv12 (u13.rest (ws := [.r3]) (by simp)) u13.mem
  refine wp_dp (op2_reg _ _) fun s14 u14 => ?_
  obtain ⟨h14, hv14⟩ := h13.reg hv13 (u14.rest (ws := [.r2]) (by simp)) u14.mem
  refine wp_dp (op2_reg _ _) fun s15 u15 => ?_
  obtain ⟨h15, hv15⟩ := h14.reg hv14 (u15.rest (ws := [.r3]) (by simp)) u15.mem
  refine h15.strSlot hv15 (d := sCa) (r := .r3) (by decide) fun s16 h16 hv16 g16 _ => ?_
  refine wp_subs (op2_imm (by decide)) fun s17 u17 z17 => WP.block_nil ?_
  obtain ⟨h17, hv17⟩ := h16.reg hv16 (u17.rest (ws := [.lr]) (by simp)) u17.mem
  have k1 : k + 1 < 2 ^ 32 := by omega
  have r2v : s8.gpr .r2 = BitVec.ofNat 32 (k + 1) := by
    rw [u8.gpr, dpVal, u7.gpr]
    simp only [upd_self, upd_ne _ _ (show sCd ≠ sCa by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]; omega
  have r3v : s15.gpr .r3 = if s1.gpr .r1 = 0 then BitVec.ofNat 32 (wlOf (A σ j) k) else BitVec.ofNat 32 (k + 1) := by
    rw [u15.gpr, dpVal, u14.gpr, dpVal, u14.other .r3 (by decide), u13.gpr, dpVal, u13.other .r2 (by decide),
      u13.other .r1 (by decide), u12.gpr, u12.other .r2 (by decide), u12.other .r1 (by decide), u11.gpr, dpVal,
      u11.other .r2 (by decide), u10.gpr, u10.other .r1 (by decide), u10.other .r2 (by decide), g9, r2v,
      u8.other .r1 (by decide), u7.other .r1 (by decide), nz]
    simp only [upd_self, upd_ne _ _ (show sCa ≠ sCd by decide)]
    rw [show (0 : BitVec 32) - (if s1.gpr .r1 = 0 then 0 else 1) = 0 - (if s1.gpr .r1 = 0 then 0 else 1) from rfl,
      mask_sel]
  have w0 : (s1.gpr .r1 = 0) ↔ A σ j / 2 ^ (32 * k) % 2 ^ 32 = 0 := by
    rw [u1.gpr, ← dig]
    constructor
    · intro e; rw [e]; rfl
    · intro e; exact BitVec.eq_of_toNat_eq (by rw [e]; rfl)
  have wlv : (s15.gpr .r3).toNat = wlOf (A σ j) (k + 1) := by
    rw [r3v]; simp only [wlOf]
    by_cases c : s1.gpr .r1 = 0
    · simp only [c, w0.mp c, ↓reduceIte, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by have := wlOf_le (A σ j) k; omega)
    · have c' : ¬ A σ j / 2 ^ (32 * k) % 2 ^ 32 = 0 := fun e => c (w0.mpr e)
      simp only [c, c', ↓reduceIte, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt k1
  have lrv : s16.gpr .lr = BitVec.ofNat 32 (P.w - k) := by
    rw [g16, u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide),
      u11.other _ (by decide), u10.other _ (by decide), g9, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), plr]
  refine ⟨⟨⟨h17.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨?_, ?_⟩), hv17⟩, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_cons] at hd ⊢; grind
  · simp only [upd]
    split
    · rename_i e; subst e; rw [wlv]
    · split
      · rename_i e1 e2; subst e2; rw [r2v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k1]
      · rfl
  · rw [u17.other _ (by decide), g16, u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide),
      u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide), g9, u8.other _ (by decide),
      u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, dpVal, u1.other _ (by decide), p0,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
    congr 2
  · rw [u17.gpr, lrv, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]; congr 1
  · rw [z17, lrv, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    by_cases e : P.w - (k + 1) = 0
    · rw [show P.w - k - 1 = 0 by omega]; simp [e]
    · have : BitVec.ofNat 32 (P.w - k - 1) ≠ 0 := fun h0 => by
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        have : (0 : BitVec 32).toNat = 0 := rfl
        omega
      rw [show (BitVec.ofNat 32 (P.w - k - 1) == 0) = false from beq_eq_false_iff_ne.mpr this]
      exact (decide_eq_false e).symm


theorem wlInit_ok {L LW LS : List Nat} {A AW V : State → Nat → Nat} {σ s : State}
    (h : KS P σ (A σ) L (AW σ) LW (V σ) LS s) (hv : Ws s P.B P.Z P.w nArr) :
    WP isa (.block (wlInit aM1)) s fun t => WI P aM1 A L AW LW V LS 0 σ t := by
  unfold wlInit
  refine ptr_ok hv (r := .r0) (by decide) (j := aM1) (by decide) fun s1 p1 r1 m1 hv1 => ?_
  have h1 := h.of_rest r1 m1 (by decide)
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.lr]) (by simp)) u2.mem
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine h3.strSlot hv3 (d := sCa) (r := .r1) (by decide) fun s4 h4 hv4 g4 _ => ?_
  refine h4.strSlot hv4 (d := sCd) (r := .r1) (by decide) fun s5 h5 hv5 g5 _ => WP.block_nil ⟨⟨?_, hv5⟩, ?_, ?_⟩
  · have r1v : (s3.gpr .r1).toNat = 0 := by rw [u3.gpr]; rfl
    have r1v' : (s4.gpr .r1).toNat = 0 := by rw [g4, r1v]
    rw [r1v'] at h5
    rw [r1v] at h5
    refine h5.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ?_)
    simp only [List.mem_cons] at hd ⊢
    refine ⟨by grind, ?_⟩
    simp only [wlOf]
    by_cases c1 : d = sCa
    · subst c1; simp only [upd_self, upd_ne _ _ (show sCa ≠ sCd by decide)]
    · by_cases c2 : d = sCd
      · subst c2; simp only [upd_self, upd_ne _ _ (show sCd ≠ sCa by decide)]
      · simp only [upd_ne _ _ c1, upd_ne _ _ c2]
  · rw [g5, g4, u3.other _ (by decide), u2.other _ (by decide), p1, Nat.mul_zero, Nat.add_zero]
  · rw [g5, g4, u3.other _ (by decide), u2.gpr, hv1.r9, Nat.sub_zero]

/-- The words left of `wlen`: `sCa` and `sCd` dropped, `s'` at `sTk` and a word (`4`) at `sWs`. -/
def sPr (x : Nat) : Nat := P.w + 1 - wlOf x P.w

theorem wlen_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} (hj : aM1 ∈ L)
    (hLS : ∀ d ∈ LS, d ≠ sCa ∧ d ≠ sCd ∧ d ≠ sTk ∧ d ≠ sWs) :
    VP (Dk P E A L AW LW V LS P.w nArr) wlen
      (Dk P E A L AW LW (fun σ => upd (upd (V σ) sTk (sPr (P := P) (A σ aM1))) sWs 4) (sWs :: sTk :: LS)
        P.w nArr) := by
  simp only [wlen, seqs]
  refine VP.seq (G := fun σ s => E σ ∧ WI P aM1 A L AW LW V LS 0 σ s)
    (VP.dctx wlInit_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => WP.mono (wlInit_ok h hv) fun t ht => ⟨e, ht⟩) ?_
  refine VP.of_imp (p := 0 < P.w) (fun σ s ⟨_, h, _⟩ => by show 0 < 2 * P.w6 + 2; omega) fun pos => ?_
  refine VP.seq (VP.count (E := E) (I := fun k σ s => WI P aM1 A L AW LW V LS k σ s) pos fun k hk =>
    VP.taint _ wlStep_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
      fun σ s ⟨e, h⟩ => WP.mono (wlStep_ok hj hk h) fun t ⟨ht, z⟩ => ⟨⟨e, ht⟩, z⟩) ?_
  · obtain ⟨_, ⟨_, w₁⟩, a₁, b₁⟩ := h₁
    obtain ⟨_, ⟨_, w₂⟩, a₂, b₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [b₁, b₂]
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]
  refine VP.dctx shAmtW_taint (fun _ _ h => h.2.1.2) fun σ s ⟨e, ⟨h, hv⟩, _, _⟩ => ?_
  have sz := h.sizes
  have wl := sz.wle
  have hw := wlOf_le (A σ aM1) P.w
  unfold shAmtW
  refine h.ldrSlot hv (d := sCa) (by simp) (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r2]) (by simp)) u2.mem
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r2]) (by simp)) u3.mem
  refine h3.strSlot hv3 (d := sTk) (r := .r2) (by decide) fun s4 h4 hv4 g4 _ => ?_
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine h5.strSlot hv5 (d := sWs) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
  have r2v : (s3.gpr .r2).toNat = sPr (P := P) (A σ aM1) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, u2.other .r1 (by decide), u1.gpr,
      u1.other .r9 (by decide), hv.r9]
    simp only [upd_self]
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (1 : BitVec 32).toNat = 1 from rfl]
    unfold sPr
    rw [Nat.mod_eq_of_lt (a := P.w) (by omega), Nat.mod_eq_of_lt (a := P.w + 1) (by omega),
      Nat.mod_eq_of_lt (a := wlOf _ _) (by omega)]
    omega
  refine ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ?_)
  rw [u5.gpr, r2v] at *
  simp only [List.mem_cons] at hd
  rcases hd with rfl | rfl | hd
  · exact ⟨by simp, by simp only [upd_self]; rfl⟩
  · exact ⟨by simp, by simp only [upd_self, upd_ne _ _ (show sTk ≠ sWs by decide)]⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hLS d hd
    exact ⟨by simp [hd], by simp only [upd_ne _ _ a1, upd_ne _ _ a2, upd_ne _ _ a3, upd_ne _ _ a4]⟩


/-- The narrow arrays the division by words reads. -/
abbrev LBd : List Nat := [aD, aM1, aN, aZN, aOneN]

/-- The wide `m + 1` and `n - r` at `5` and `6`. -/
def AWBw (A : Nat → Nat) : Nat → Nat := upd (upd (AWB P) 5 (A aM1)) 6 (A aD)
abbrev LWBw : List Nat := [6, 5, 2, wN, wOne, wZ, 0]

theorem toN_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} :
    VP (Dk P E A L AW LW V LS P.W 22) (.block toN) (Dk P E A L AW LW V LS P.w nArr) :=
  VP.dctx toN_taint (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ => by
    rw [← List.append_nil toN]; exact h.toN hv fun t ht hvt _ => WP.block_nil ⟨e, ht, hvt⟩

theorem widenB_vp {E : State → Prop} {A V : State → Nat → Nat} {LS : List Nat} :
    VP (Dk P E A LBd (fun _ => AWB P) LWB0 V LS P.w nArr) widenB
      (Dk P E A LBd (fun σ => AWBw (P := P) (A σ)) LWBw V LS P.W 22) := by
  simp only [widenB, seqs]
  refine toW_vp.seq ((copyW_vp (o := 5) (a := wZ) (by decide) (by decide) (by decide) (by decide)
    copy5_taint).seq ((copyW_vp (o := 6) (a := wZ) (by decide) (by decide) (by decide) (by decide)
    copy6_taint).seq ((copyW_vp (o := 2) (a := wZ) (by decide) (by decide) (by decide) (by decide)
    copy2_taint).seq (toN_vp.seq ?_))))
  refine VP.seq (G := Dk P E A LBd (fun σ => upd (AWB P) 5 (A σ aM1)) (5 :: 6 :: 2 :: LWB0) V LS P.w nArr)
    (VP.dctx copy10_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) (VP.seq ?_ toW_vp)
  · have z : num s.mem P.B P.W 5 = 0 := by rw [h.arrsW 5 (by decide)]; simp only [AWB]; rd_up
    have h' := h.mono (A' := A σ) (live' := LBd) (AW' := AWB P) (liveW' := 6 :: 2 :: LWB0) (V' := V σ) (ls' := LS)
      (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => by
        simp only [LWB0, List.mem_cons, List.not_mem_nil, or_false] at hj
        refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [AWB] <;> rd_up) (fun d hd => ⟨hd, rfl⟩)
    exact WP.mono (h'.widen hv (j := 5) (a := aM1) (by decide) z (by decide) (by decide) (by decide) (by decide))
      fun t ⟨ht, hvt⟩ => ⟨e, ht, hvt⟩
  · refine VP.dctx copy12d_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
    have z : num s.mem P.B P.W 6 = 0 := by rw [h.arrsW 6 (by decide)]; simp only [AWB]; rd_up
    have h' := h.mono (A' := A σ) (live' := LBd) (AW' := upd (AWB P) 5 (A σ aM1)) (liveW' := 5 :: 2 :: LWB0)
      (V' := V σ) (ls' := LS) (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => by
        simp only [LWB0, List.mem_cons, List.not_mem_nil, or_false] at hj
        exact ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    exact WP.mono (h'.widen hv (j := 6) (a := aD) (by decide) z (by decide) (by decide) (by decide) (by decide))
      fun t ⟨ht, hvt⟩ => ⟨e, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => by
        simp only [LWBw, List.mem_cons, List.not_mem_nil, or_false] at hj
        refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [AWBw] <;> rd_up)
        (fun d hd => ⟨hd, rfl⟩), hvt⟩


/-- A stage of the shift by `sp` words: its bit `k` set, a shift by `2^k` words, which does not overflow. -/
theorem stage_math {v len sp k W : Nat} (hv : v < 2 ^ (32 * len)) (hl : len + sp ≤ W) :
    (if sp / 2 ^ k % 2 = 0 then v * 2 ^ (32 * (sp % 2 ^ k))
      else v * 2 ^ (32 * (sp % 2 ^ k)) % 2 ^ (32 * (W - 2 ^ k)) * 2 ^ (32 * 2 ^ k)) =
    v * 2 ^ (32 * (sp % 2 ^ (k + 1))) := by
  have e : sp % 2 ^ (k + 1) = sp % 2 ^ k + 2 ^ k * (sp / 2 ^ k % 2) := Nat.mod_pow_succ
  split
  · rename_i b; rw [e, b, Nat.mul_zero, Nat.add_zero]
  · rename_i b
    have b1 : sp / 2 ^ k % 2 = 1 := by omega
    have d := Nat.div_add_mod sp (2 ^ k)
    have q1 : 2 ^ k ≤ 2 ^ k * (sp / 2 ^ k) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero fun h => by rw [h] at b1; exact absurd b1 (by decide))
    have le : sp % 2 ^ k + 2 ^ k ≤ sp := by
      generalize 2 ^ k * (sp / 2 ^ k) = a at d q1
      omega
    have lt : v * 2 ^ (32 * (sp % 2 ^ k)) < 2 ^ (32 * (W - 2 ^ k)) := by
      refine Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _)) ?_
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.mod_eq_of_lt lt, Nat.mul_assoc, ← Nat.pow_add, e, b1, Nat.mul_one]
    congr 2; omega


/-- `x - y >>> 31`: whether `x < y`. -/
theorem sign_bit {x y : Nat} (hx : x < 2 ^ 31) (hy : y < 2 ^ 31) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y) >>> 31 = if x < y then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  by_cases c : x < y
  · simp only [c, ↓reduceIte]; rw [show (1 : BitVec 32).toNat = 1 from rfl]; omega
  · simp only [c, ↓reduceIte]; rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega

/-- Half a stage: `[a]` shifted by `2^k` words where bit `k` of `sp` is set, through `[18]` and `[3]`. -/
theorem halfStage_vp {a k : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    {H : State → State → Prop} {rest : Prog isa} {v len sp : State → Nat}
    (hsh : 2 ^ k < P.W) (ha : a ∈ LW) (ha22 : a < 22) (ha3 : a ≠ 3) (ha18 : a ≠ 18) (hz : wZ ∈ LW)
    (hLW : ∀ j ∈ LW, j ≠ 3 ∧ j ≠ 18) (hL : ∀ j ∈ L, j / 2 ≠ 18 ∧ j / 2 ≠ 3 ∧ j / 2 ≠ a)
    (hS : sWs ∈ LS) (hB : sBit ∈ LS)
    (z0 : ∀ σ, E σ → AW σ wZ = 0) (vS : ∀ σ, E σ → V σ sWs = 4 * 2 ^ k)
    (vB : ∀ σ, E σ → V σ sBit = sp σ / 2 ^ k % 2)
    (vA : ∀ σ, E σ → AW σ a = v σ * 2 ^ (32 * (sp σ % 2 ^ k)))
    (hfit : ∀ σ, E σ → v σ < 2 ^ (32 * len σ) ∧ len σ + sp σ ≤ P.W)
    (certA : DCert (.block (ptr .r0 18 ++ ([.ldr .r1 .r8 sWs] : List Instr)))) (certB : ShiftCert .r0 (shiftUpB a))
    (certS : DCert (sel 3 a 18 sBit)) (certC : DCert (copy a 3))
    (hrest : VP (Dk P E A L (fun σ => upd (AW σ) a (v σ * 2 ^ (32 * (sp σ % 2 ^ (k + 1))))) LW V LS P.W 22)
      rest H) :
    VP (Dk P E A L AW LW V LS P.W 22)
      (.seq (shiftUpBy sWs 18 a) (.seq (sel 3 a 18 sBit) (.seq (copy a 3) rest))) H := by
  refine (shiftUpBy_vp (d := sWs) (sh := 2 ^ k) (o := 18) (a := a) hsh (by decide) ha (Ne.symm ha18) hz
    (by decide) (fun j hj => (hL j hj).1) hS z0 vS copy18_taint certA certB).seq ?_
  refine VP.seq (G := Dk P E A L (fun σ => upd (upd (AW σ) 18 (AW σ a % 2 ^ (32 * (P.W - 2 ^ k)) * 2 ^ (32 * 2 ^ k)))
      3 (if V σ sBit = 0 then upd (AW σ) 18 (AW σ a % 2 ^ (32 * (P.W - 2 ^ k)) * 2 ^ (32 * 2 ^ k)) a
        else upd (AW σ) 18 (AW σ a % 2 ^ (32 * (P.W - 2 ^ k)) * 2 ^ (32 * 2 ^ k)) 18)) (3 :: 18 :: LW) V LS P.W 22)
    (VP.dctx certS (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
    WP.mono (h.sel_W hv (o := 3) (a := a) (b := 18) (sl := sBit) (by decide) (List.mem_cons_of_mem _ ha)
      (List.mem_cons_self ..) (Ne.symm ha3) (by decide) hB (by rw [vB σ e]; omega) (fun j hj => (hL j hj).2.1))
      fun t ⟨ht, hvt, _⟩ => ⟨e, ht, hvt⟩) ?_
  refine VP.seq (G := Dk P E A L (fun σ => upd (AW σ) a (v σ * 2 ^ (32 * (sp σ % 2 ^ (k + 1))))) LW V LS P.W 22)
    ((copyW_vp (o := a) (a := 3) ha22 (List.mem_cons_self ..) ha3 (fun j hj => (hL j hj).2.2)
    certC).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_)
      (fun d hd => ⟨hd, rfl⟩), hv⟩) hrest
  refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)), ?_⟩
  obtain ⟨j3, j18⟩ := hLW j hj
  by_cases c : j = a
  · subst c
    simp only [upd_self, upd_ne _ _ ha18]
    rw [vB σ e, vA σ e]
    exact stage_math (hfit σ e).1 (hfit σ e).2
  · simp only [upd_ne _ _ c, upd_ne _ _ j3, upd_ne _ _ j18]

/-- The stages' count: `2^K > w`. -/
abbrev KSt (P : RP) : Nat := Nat.log2 P.w + 1

/-- After `k` stages: `m + 1` and `n - r` shifted by `sp mod 2^k` words, `⌊sp / 2^k⌋` at `sTk`
and `4 · 2^k` at `sWs`. -/
def SK (A : Nat → Nat) (k : Nat) : Nat → Nat :=
  upd (upd (AWB P) 5 (A aM1 * 2 ^ (32 * (sPr (P := P) (A aM1) % 2 ^ k))))
    6 (A aD * 2 ^ (32 * (sPr (P := P) (A aM1) % 2 ^ k)))
def VK (V A : Nat → Nat) (k : Nat) : Nat → Nat :=
  upd (upd V sTk (sPr (P := P) (A aM1) / 2 ^ k)) sWs (4 * 2 ^ k)

theorem stEnd_ok {k : Nat} {LS : List Nat} {σ s : State} {A V AW : Nat → Nat}
    (hk : 2 ^ k ≤ P.w) (hLS : ∀ d ∈ LS, d ≠ sTk ∧ d ≠ sWs ∧ d ≠ sBit)
    (h : KS P σ A LBd AW LWBw (upd (VK (P := P) V A k) sBit (sPr (P := P) (A aM1) / 2 ^ k % 2))
      (sBit :: sWs :: sTk :: LS) s) (hv : Ws s P.B P.Z P.W 22) :
    WP isa (.block [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
      .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
      .dp .sub .r1 .r1 (.shifted .r9 .lsl 1), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]) s fun t =>
      (KS P σ A LBd AW LWBw (VK (P := P) V A (k + 1)) (sWs :: sTk :: LS) t ∧ Ws t P.B P.Z P.W 22) ∧
        t.z = decide (KSt P - (k + 1) = 0) := by
  have sz := h.sizes
  have wl := sz.wle
  have w0 : P.w ≠ 0 := by have := sz.w6a; simp only [RP.w]; omega
  have p1 : 2 ^ (k + 1) ≤ 2 * P.w := by rw [Nat.pow_succ]; omega
  refine h.ldrSlot hv (d := sTk) (by simp) (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := sTk) (r := .r1) (by decide) fun s3 h3 hv3 g3 _ => ?_
  refine h3.ldrSlot hv3 (d := sWs) (by simp) (r := .r1) (by decide) fun s4 h4 hv4 u4 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine h5.strSlot hv5 (d := sWs) (r := .r1) (by decide) fun s6 h6 hv6 g6 _ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s7 u7 => ?_
  obtain ⟨h7, hv7⟩ := h6.reg hv6 (u7.rest (ws := [.r1]) (by simp)) u7.mem
  refine wp_mov (op2_lsr (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r1]) (by simp)) u8.mem
  refine wp_cmp (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  obtain ⟨ht, hvt⟩ := h8.reg hv8 (ut.rest []) ut.mem
  have tk : (s2.gpr .r1).toNat = sPr (P := P) (A aM1) / 2 ^ (k + 1) := by
    rw [u2.gpr, u1.gpr]
    simp only [VK, upd_ne _ _ (show sTk ≠ sBit by decide), upd_ne _ _ (show sTk ≠ sWs by decide), upd_self]
    have : sPr (P := P) (A aM1) ≤ P.w + 1 := by unfold sPr; omega
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)), Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
  have ws : (s5.gpr .r1).toNat = 4 * 2 ^ (k + 1) := by
    rw [u5.gpr, u4.gpr]
    simp only [upd_ne _ _ (show sWs ≠ sTk by decide), VK, upd_ne _ _ (show sWs ≠ sBit by decide), upd_self]
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_succ, Nat.pow_succ 2 k]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have r8v : s8.gpr .r1 = if 4 * 2 ^ (k + 1) < 2 * P.W then 1 else 0 := by
    rw [u8.gpr, u7.gpr, dpVal, hv6.r9, g6]
    rw [show s5.gpr .r1 = BitVec.ofNat 32 (4 * 2 ^ (k + 1)) from BitVec.eq_of_toNat_eq (by
      rw [ws, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])]
    rw [show BitVec.ofNat 32 P.W <<< 1 = BitVec.ofNat 32 (2 * P.W) from BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (a := P.W) (by simp only [RP.W]; omega)]; simp only [RP.W]; omega)]
    exact sign_bit (by omega) (by simp only [RP.W]; omega)
  refine ⟨⟨ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ?_), hvt⟩, ?_⟩
  · rw [ws, g3, tk] at *
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact ⟨by simp, by simp only [VK, upd_self]⟩
    · exact ⟨by simp, by simp only [VK, upd_self, upd_ne _ _ (show sTk ≠ sWs by decide)]⟩
    · obtain ⟨a1, a2, a3⟩ := hLS d hd
      exact ⟨by simp [hd], by simp only [VK, upd_ne _ _ a1, upd_ne _ _ a2, upd_ne _ _ a3]⟩
  · rw [zt, r8v]
    have e : 4 * 2 ^ (k + 1) < 2 * P.W ↔ k + 1 ≤ Nat.log2 P.w := by
      rw [Nat.le_log2 w0]; simp only [RP.W]; omega
    by_cases c : k + 1 ≤ Nat.log2 P.w
    · simp only [e.mpr c, ↓reduceIte]
      have : ¬ KSt P - (k + 1) = 0 := by simp only [KSt]; omega
      simp only [this, decide_false]; rfl
    · simp only [show ¬ 4 * 2 ^ (k + 1) < 2 * P.W from fun h => c (e.mp h), ↓reduceIte]
      have : KSt P - (k + 1) = 0 := by simp only [KSt]; omega
      simp only [this, decide_true]; rfl


theorem stage_pow_le {k : Nat} (hk : k < KSt P) : 2 ^ k ≤ P.w :=
  Nat.le_trans (Nat.pow_le_pow_right (by decide) (by simp only [KSt] at hk; omega))
    (Nat.log2_self_le (by simp only [RP.w]; omega))

theorem stage_vp {k : Nat} {E : State → Prop} {A V : State → Nat → Nat} {LS : List Nat} (hk : k < KSt P)
    (hLS : ∀ d ∈ LS, d ≠ sTk ∧ d ≠ sWs ∧ d ≠ sBit)
    (hx : ∀ σ, E σ → A σ aM1 < 2 ^ (32 * P.w) ∧ A σ aD < 2 ^ (32 * P.w)) :
    VP (fun σ s => E σ ∧ (KS P σ (A σ) LBd (SK (P := P) (A σ) k) LWBw (VK (P := P) (V σ) (A σ) k)
        (sWs :: sTk :: LS) s ∧ Ws s P.B P.Z P.W 22))
      (wStage 5 6 18 3)
      (fun σ s => (E σ ∧ (KS P σ (A σ) LBd (SK (P := P) (A σ) (k + 1)) LWBw (VK (P := P) (V σ) (A σ) (k + 1))
        (sWs :: sTk :: LS) s ∧ Ws s P.B P.Z P.W 22)) ∧ s.z = decide (KSt P - (k + 1) = 0)) := by
  have p := stage_pow_le hk
  have hsh : 2 ^ k < P.W := by simp only [RP.W]; omega
  have hfx : ∀ σ, E σ → A σ aM1 < 2 ^ (32 * wlOf (A σ aM1) P.w) ∧
      wlOf (A σ aM1) P.w + sPr (P := P) (A σ aM1) ≤ P.W := fun σ e => by
    have h1 := (wlOf_spec (A σ aM1) P.w).1
    rw [Nat.mod_eq_of_lt (hx σ e).1] at h1
    have := wlOf_le (A σ aM1) P.w
    exact ⟨h1, by unfold sPr; simp only [RP.W]; omega⟩
  simp only [wStage, seqs]
  refine VP.seq (G := Dk P E A LBd (fun σ => SK (P := P) (A σ) k) LWBw
      (fun σ => upd (VK (P := P) (V σ) (A σ) k) sBit (sPr (P := P) (A σ aM1) / 2 ^ k % 2))
      (sBit :: sWs :: sTk :: LS) P.W 22)
    (VP.dctx stBit_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · refine h.ldrSlot hv (d := sTk) (by simp) (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
    refine h2.strSlot hv2 (d := sBit) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
    have bv : (s2.gpr .r1).toNat = sPr (P := P) (A σ aM1) / 2 ^ k % 2 := by
      rw [u2.gpr, dpVal, u1.gpr]
      simp only [VK, upd_ne _ _ (show sTk ≠ sWs by decide), upd_self]
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
        Nat.mod_mod_of_dvd _ (by decide)]
    rw [bv] at ht; exact ht
  refine halfStage_vp (a := 5) (k := k) (v := fun σ => A σ aM1) (len := fun σ => wlOf (A σ aM1) P.w)
    (sp := fun σ => sPr (P := P) (A σ aM1)) hsh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp) (fun σ _ => by simp only [SK, AWB]; rd_ev)
    (fun σ _ => by simp only [VK]; rd_up) (fun σ _ => by rd_up) (fun σ _ => by simp only [SK]; rd_up) hfx
    upA18_taint upB5_taint sel5_taint copy53_taint ?_
  refine halfStage_vp (a := 6) (k := k) (v := fun σ => A σ aD) (len := fun _ => P.w)
    (sp := fun σ => sPr (P := P) (A σ aM1)) hsh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp) (fun σ _ => by simp only [SK, AWB]; rd_ev)
    (fun σ _ => by simp only [VK]; rd_up) (fun σ _ => by rd_up) (fun σ _ => by simp only [SK]; rd_up)
    (fun σ e => ⟨(hx σ e).2, by have := wlOf_le (A σ aM1) P.w; unfold sPr; simp only [RP.W]; omega⟩)
    upA18_taint upB6_taint sel6_taint copy63_taint ?_
  refine VP.dctx stEnd_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
    WP.mono (stEnd_ok p hLS h hv) fun t ⟨⟨ht, hvt⟩, z⟩ => ⟨⟨e, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_)
      (fun d hd => ⟨hd, rfl⟩), hvt⟩, z⟩
  refine ⟨hj, ?_⟩
  simp only [LWBw, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [SK] <;> rd_up


/-- The divisor shifted by `sp` words: its top word is word `w`. -/
theorem shifted_bounds {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ (32 * P.w)) :
    2 ^ (32 * P.w) ≤ x * 2 ^ (32 * sPr (P := P) x) ∧ x * 2 ^ (32 * sPr (P := P) x) < 2 ^ (32 * (P.w + 1)) := by
  obtain ⟨h1, h2⟩ := wlOf_spec x P.w
  rw [Nat.mod_eq_of_lt hx] at h1 h2
  have hle := wlOf_le x P.w
  have hne : wlOf x P.w ≠ 0 := fun e => by rw [e, Nat.mul_zero, Nat.pow_zero] at h1; omega
  have lo := h2 hne
  unfold sPr
  constructor
  · calc 2 ^ (32 * P.w) = 2 ^ (32 * (wlOf x P.w - 1)) * 2 ^ (32 * (P.w + 1 - wlOf x P.w)) := by
          rw [← Nat.pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ lo
  · calc x * 2 ^ (32 * (P.w + 1 - wlOf x P.w)) < 2 ^ (32 * wlOf x P.w) * 2 ^ (32 * (P.w + 1 - wlOf x P.w)) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = _ := by rw [← Nat.pow_add]; congr 1; omega

theorem sp_lt {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ (32 * P.w)) :
    sPr (P := P) x % 2 ^ KSt P = sPr (P := P) x := by
  have h1 := (wlOf_spec x P.w).1
  rw [Nat.mod_eq_of_lt hx] at h1
  have hne : wlOf x P.w ≠ 0 := fun e => by rw [e, Nat.mul_zero, Nat.pow_zero] at h1; omega
  have := Nat.lt_log2_self (n := P.w)
  unfold sPr KSt
  exact Nat.mod_eq_of_lt (by omega)

theorem m1V_facts {f g : Nat × Nat × Nat → Nat × Nat × Nat} (σ : State) :
    1 ≤ m1V P f g σ ∧ m1V P f g σ < 2 ^ (32 * P.w) ∧ dV P f g σ < 2 ^ (32 * P.w) := by
  have p : 1 < 2 ^ (32 * P.w) := Nat.one_lt_two_pow (by simp only [RP.w]; omega)
  have l1 : m1R P f g σ < 2 ^ (32 * P.w) := by unfold m1R sub32; exact Nat.mod_lt _ (by omega)
  refine ⟨?_, ?_, by unfold dV sub32; exact Nat.mod_lt _ (by omega)⟩ <;> unfold m1V <;>
    by_cases c : m1R P f g σ = 0 <;> simp only [c, ↓reduceIte] <;> omega

theorem divB_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (fun _ => AB P) LB (AWA2 P f g) LWA (VA P f g) [sLt, sOkDE] P.w nArr) divB
      (Dk P E (fun σ => upd (AB P) aD (qV P f g σ)) [aD, aN, aZN, aOneN] (fun _ => AWB P) LWB (VB P f g)
        [sExact, sLt, sOkDE] P.w nArr) := by
  have pos : 0 < KSt P := by simp only [KSt]; omega
  have hx : ∀ σ, E σ → ABd P f g σ aM1 < 2 ^ (32 * P.w) ∧ ABd P f g σ aD < 2 ^ (32 * P.w) := fun σ _ => by
    simp only [ABd]; rd_ev; exact ⟨(m1V_facts σ).2.1, (m1V_facts σ).2.2⟩
  simp only [divB, divBW, seqs]
  refine divBPre_vp.seq ((wlen_vp (by decide) (by decide)).seq (VP.seq
    (G := fun σ s => E σ ∧ (KS P σ (ABd P f g σ) LBd (SK (P := P) (ABd P f g σ) 0) LWBw
      (VK (P := P) (VA P f g σ) (ABd P f g σ) 0) [sWs, sTk, sLt, sOkDE] s ∧ Ws s P.B P.Z P.W 22)) ?_
    (VP.seq (VP.count (E := E) (I := fun k σ s => KS P σ (ABd P f g σ) LBd (SK (P := P) (ABd P f g σ) k) LWBw
      (VK (P := P) (VA P f g σ) (ABd P f g σ) k) [sWs, sTk, sLt, sOkDE] s ∧ Ws s P.B P.Z P.W 22) pos
      fun k hk => stage_vp hk (by decide) hx) ?_)))
  · refine widenB_vp.mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ =>
      ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_) (fun d hd => ?_), hv⟩
    · refine ⟨hj, ?_⟩
      simp only [LWBw, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [SK, AWBw] <;> rd_up <;>
        simp only [Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.mul_one]
    · refine ⟨hd, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> simp only [VK] <;> rd_up <;> simp only [Nat.pow_zero, Nat.div_one]
  refine VP.seq (divMid_vp (a := 6) (r := 7) (m := 5) (t := 8) (nm := 15) (u := 21) (q := 2) (L := LBd)
    (LW := LWBw) (LS := [sWs, sTk, sLt, sOkDE]) divBW_taint
    (by simp only [VG.Proof.Rsa.Arm.KeyDiv.QArr]; decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ _ => by simp only [SK, AWB]; rd_ev)
    (fun σ _ => by simp only [SK, AWB]; rd_ev) (fun σ e => ?_)) ?_
  · have := m1V_facts (P := P) (f := f) (g := g) σ
    simp only [SK]; rd_up
    rw [sp_lt (by simp only [ABd]; rd_ev; exact this.1) (hx σ e).1]
    have b := shifted_bounds (P := P) (x := ABd P f g σ aM1) (by simp only [ABd]; rd_ev; exact this.1)
      (hx σ e).1
    rw [show P.W / 2 - 1 = P.w by simp only [RP.W]; omega, show P.W / 2 = P.w + 1 by simp only [RP.W]; omega]
    exact b
  simp only [divBEnd, seqs]
  refine toW_vp.seq ((eqSW_vp (d := sExact) (a := 7) (b := wZ) (t := 18) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) eqExactW_taint).seq (toN_vp.seq ?_))
  refine VP.dctx copyDB_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have h' := h.narrow (j := 2) (by decide) (by decide)
  refine WP.mono (h'.copy_w hv (o := aD) (a := aB) (by decide) (by simp [aB]) (by decide) (by decide))
    fun t ⟨ht, hvt, _⟩ => ⟨e, ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_), hvt⟩
  · have mf := m1V_facts (P := P) (f := f) (g := g) σ
    have P0 := Nat.two_pow_pos (32 * sPr (P := P) (ABd P f g σ aM1))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl | rfl
    · simp only [upd_self]; rw [show (2 * 2 : Nat) = aB from rfl]; simp only [upd_self]
      rd_up; simp only [SK]; rd_up
      rw [sp_lt (by simp only [ABd]; rd_ev; exact mf.1) (by simp only [ABd]; rd_ev; exact mf.2.1),
        Nat.mul_div_mul_right _ _ P0]
      simp only [ABd]; rd_ev
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) mf.2.2)
    all_goals (simp only [ABd, AB]; rd_ev)
  · simp only [LWB, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl <;> simp only [SK, AWB] <;> rd_ev
  · have P0 := Nat.two_pow_pos (32 * sPr (P := P) (ABd P f g σ aM1))
    have mf := m1V_facts (P := P) (f := f) (g := g) σ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl | rfl
    · simp only [upd_self, VB]; rd_up; simp only [SK, AWB]; rd_ev
      rw [sp_lt (by simp only [ABd]; rd_ev; exact mf.1) (by simp only [ABd]; rd_ev; exact mf.2.1),
        Nat.mul_mod_mul_right]
      simp only [ABd]; rd_ev
    all_goals (simp only [VB, VK]; rd_up)

end

end VG.Proof.Rsa.Arm.RecoverDet
