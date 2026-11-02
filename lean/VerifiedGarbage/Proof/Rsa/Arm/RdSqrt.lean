module
public import VerifiedGarbage.Proof.Rsa.Arm.RdDiv

import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: `b² - 4 n`, its square root and the factors

`square_vp`: `b = q + 1` and `b²` (`product_vp`); `minus4n_vp`: `4 n`,
`b² - 4 n` and whether it is positive; `sqrt_vp`: its square root two bits
at a time, whose step is any `h` with the formula of Appendix C.2's model
(`sqrtStep`); `factors_vp`: the factors and the mask of every check.
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

/-! ## `b` and `b²` -/

/-- `b = q + 1` modulo `2^(32 w)`. -/
abbrev bV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.w (qV P f g σ) (sub32 P.w 0 1)

def ASQ (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AB P) aB (bV P f g σ)) aBy (bV P f g σ)
def AWSQ (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (AWB P) wB (bV P f g σ)
abbrev LSQ : List Nat := [aBy, aB, aN, aZN, aOneN]
abbrev LWSQ : List Nat := [wB, wN, wOne, wZ]
abbrev LSB : List Nat := [sExact, sLt, sOkDE]

theorem squarePre_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (fun σ => upd (AB P) aD (qV P f g σ)) [aD, aN, aZN, aOneN] (fun _ => AWB P) LWB (VB P f g) LSB
      P.w nArr) squarePre (Dk P E (ASQ P f g) LSQ (AWSQ P f g) LWSQ (VB P f g) LSB P.w nArr) := by
  refine VP.dctx squarePre_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  simp only [squarePre, seqs]
  refine WP.seq (WP.mono (h.sub_w hv (o := aT1) (a := aZN) (b := aOneN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s1 ⟨h1, hv1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.sub_w hv1 (o := aB) (a := aD) (b := aT1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s2 ⟨h2, hv2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.copy_w hv2 (o := aBy) (a := aB) (by decide) (by decide) (by decide) (by decide))
    fun s3 ⟨h3, hv3, _, _⟩ => ?_)
  refine WP.seq (h3.toW hv3 fun s4 h4 hv4 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h4.copy_W hv4 (o := wB) (a := wZ) (by decide) (by decide) (by decide) (by decide))
    fun s5 ⟨h5, hv5, _⟩ => ?_)
  refine WP.seq (h5.toN hv5 fun s6 h6 hv6 _ => WP.block_nil ?_)
  have z6 : num s6.mem P.B P.W wB = 0 := by rw [h6.arrsW wB (by decide)]; rd_up; simp only [AWB]; rd_up
  have h6' := h6.mono (A' := ASQ P f g σ) (live' := LSQ) (AW' := AWB P) (liveW' := LWB) (V' := VB P f g σ)
    (ls' := LSB)
    (fun j hj => by
      simp only [LSQ, List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [ASQ, AB, bV] <;> rd_ev)
    (fun j hj => by
      simp only [LWB, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> exact ⟨by decide, by rd_up⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (h6'.widen hv6 (j := wB) (a := aB) (by decide) z6 (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨ht, hvt⟩ => ⟨e, ?_, hvt⟩
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_) (fun d hd => ⟨hd, rfl⟩)
  simp only [LWSQ, List.mem_cons, List.not_mem_nil, or_false] at hj
  refine ⟨by rcases hj with rfl | rfl | rfl | rfl <;> decide, ?_⟩
  rcases hj with rfl | rfl | rfl | rfl <;> simp only [AWSQ, ASQ] <;> rd_up

theorem pcfgB : PCfg aBy wB wA wT1 wT2 wZ LSQ LWSQ LSB := by
  constructor <;> decide

/-- `b²`. -/
abbrev sqV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  (pr g (bV P f g σ) (bV P f g σ) (32 * P.w)).2.2

theorem square_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} (hg : ProdF P g) {E : State → Prop} :
    VP (Dk P E (fun σ => upd (AB P) aD (qV P f g σ)) [aD, aN, aZN, aOneN] (fun _ => AWB P) LWB (VB P f g) LSB
      P.w nArr) square (fun σ s => E σ ∧ PI P g aBy wB wA (ASQ P f g) LSQ (AWSQ P f g) LWSQ (VB P f g) LSB
        (32 * P.w) σ s) :=
  squarePre_vp.seq (product_vp pcfgB hg (fun σ _ => by simp only [AWSQ, AWB]; rd_up) productPreA_taint
    productStepB_taint)

/-! ## `b² - 4 n` -/

abbrev fourV (P : RP) : Nat := 2 * (2 * P.n % 2 ^ (32 * P.W)) % 2 ^ (32 * P.W)
abbrev xRV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.W (sqV P f g σ) (fourV P)
abbrev ok4v (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Bool :=
  !(decide (sqV P f g σ < fourV P) || decide (xRV P f g σ < 1))

def AM4 (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat := upd (AB P) aB (bV P f g σ)
def AWM (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wR (xRV P f g σ)
def VM4 (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (VB P f g σ) sOk4 (b2n (ok4v P f g σ))
abbrev LM4 : List Nat := [aB, aN, aZN, aOneN]
abbrev LWM : List Nat := [wR, wOne, wZ]
abbrev LSM : List Nat := [sOk4, sExact, sLt, sOkDE]

theorem minus4n_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (fun σ s => E σ ∧ PI P g aBy wB wA (ASQ P f g) LSQ (AWSQ P f g) LWSQ (VB P f g) LSB (32 * P.w) σ s)
      minus4n (Dk P E (AM4 P f g) LM4 (AWM P f g) LWM (VM4 P f g) LSM P.w nArr) := by
  refine VP.dctx minus4n_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  simp only [minus4n, seqs]
  refine WP.seq (h.toW hv fun s1 h1 hv1 _ => h1.clr11 hv1 fun s2 h2 hv2 z2 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h2.shl_W hv2 (j := wN) (by decide) (by omega) (by decide))
    fun s3 ⟨h3, hv3, _, _⟩ => ?_)
  rw [z2] at h3
  refine WP.seq (h3.clr11 hv3 fun s4 h4 hv4 z4 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h4.shl_W hv4 (j := wN) (by decide) (by omega) (by decide))
    fun s5 ⟨h5, hv5, _, _⟩ => ?_)
  rw [z4] at h5
  refine WP.seq (WP.mono (h5.sub_W hv5 (o := wR) (a := wA) (b := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s6 ⟨h6, hv6, _, c6⟩ => ?_)
  refine WP.seq (h6.brw hv6 (d := sC1) (by decide) fun s7 h7 hv7 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h7.sub_W hv7 (o := wT1) (a := wR) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s8 ⟨h8, hv8, _, c8⟩ => ?_)
  refine h8.brw hv8 (d := sC2) (by decide) fun s9 h9 hv9 _ => ?_
  refine h9.norS hv9 (d := sOk4) (a := sC1) (b := sC2) (by decide) (by decide)
    (by rd_up; rw [c6]; exact b2n_lt_one _) (by rd_up; rw [c8]; exact b2n_lt_one _) (by decide)
    fun s10 h10 hv10 => ?_
  refine h10.toN hv10 fun t ht hvt _ => WP.block_nil ⟨e, ?_, hvt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [LM4, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl | rfl <;> simp only [AM4, ASQ, AB] <;> rd_ev
  · simp only [LWM, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl <;> simp only [AWM, AWSQ, AWB, ASQ, AB, xRV, fourV, sqV] <;> rd_ev
  · simp only [LSM, List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl | rfl | rfl
    · rd_up; rw [c6, c8, b2n_nor]; simp only [VM4, ok4v, xRV, fourV, sqV, AWSQ, AWB, ASQ, AB]; rd_ev
    all_goals simp only [VM4]; rd_up

/-! ## The square root -/

/-- A bit shifted in at the bottom of an even number. -/
theorem shl_mod {v c k : Nat} (hc : c ≤ 1) (hk : 1 ≤ k) : (2 * v + c) % 2 ^ k = 2 * v % 2 ^ k + c := by
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ k = 2 * M := ⟨2 ^ (k - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
  have hM0 : 0 < M := by have := Nat.two_pow_pos k; omega
  have hv := Nat.div_add_mod v M
  have hr := Nat.mod_lt v hM0
  have e1 : 2 * v + c = (2 * (v % M) + c) + 2 * M * (v / M) := by rw [Nat.mul_assoc]; omega
  rw [hM, e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.mul_mod_mul_left]

theorem sub32_le {w a b : Nat} (ha : a < 2 ^ (32 * w)) (hb : b ≤ a) : sub32 w a b = a - b := by
  unfold sub32
  rw [show a + 2 ^ (32 * w) - b = (a - b) + 2 ^ (32 * w) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The step of the square root. -/
abbrev SqrtF (P : RP) (h : Nat × Nat × Nat → Nat × Nat × Nat) : Prop :=
  ∀ x r y, h (x, r, y) =
    if 2 * (2 * r % 2 ^ (32 * P.w) + 2 * x / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w) +
        2 * (2 * x % 2 ^ (32 * P.W)) / 2 ^ (32 * P.W) < 2 * (2 * y % 2 ^ (32 * P.w)) % 2 ^ (32 * P.w) + 1
    then (2 * (2 * x % 2 ^ (32 * P.W)) % 2 ^ (32 * P.W),
      2 * (2 * r % 2 ^ (32 * P.w) + 2 * x / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w) +
        2 * (2 * x % 2 ^ (32 * P.W)) / 2 ^ (32 * P.W), 2 * y % 2 ^ (32 * P.w))
    else (2 * (2 * x % 2 ^ (32 * P.W)) % 2 ^ (32 * P.W),
      2 * (2 * r % 2 ^ (32 * P.w) + 2 * x / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w) +
        2 * (2 * x % 2 ^ (32 * P.W)) / 2 ^ (32 * P.W) - (2 * (2 * y % 2 ^ (32 * P.w)) % 2 ^ (32 * P.w) + 1),
      2 * y % 2 ^ (32 * P.w) + 1)

/-- `(x, r, y)` after `k` steps of the square root. -/
abbrev rs (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat × Nat × Nat :=
  h^[k] (xRV P f g σ, 0, 0)

def AS (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (AM4 P f g σ) aRm (rs P f g h σ k).2.1) aY (rs P f g h σ k).2.2
def AWS (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (AWM P f g σ) wR (rs P f g h σ k).1
def VS (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (VM4 P f g σ) sK (16 * P.W - k)
abbrev LS5 : List Nat := [aRm, aY, aB, aN, aZN, aOneN]
abbrev LSS5 : List Nat := [sK, sOk4, sExact, sLt, sOkDE]

/-- After `k` steps of the square root. -/
def SI (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (k : Nat) (σ s : State) : Prop :=
  KS P σ (AS P f g h σ k) LS5 (AWS P f g h σ k) LWM (VS P f g σ k) LSS5 s ∧ Ws s P.B P.Z P.w nArr

theorem sqrtPre_vp {f g h : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (AM4 P f g) LM4 (AWM P f g) LWM (VM4 P f g) LSM P.w nArr) sqrtPre
      (fun σ s => E σ ∧ SI P f g h 0 σ s) := by
  refine VP.dctx sqrtPre_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h0, hv⟩ => ?_
  have sz := h0.sizes
  simp only [sqrtPre, seqs]
  refine WP.seq (WP.mono (h0.copy_w hv (o := aRm) (a := aZN) (by decide) (by decide) (by decide) (by decide))
    fun s1 ⟨h1, hv1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy_w hv1 (o := aY) (a := aZN) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, hv2, _, _⟩ => ?_)
  rw [List.append_assoc]
  refine h2.toW hv2 fun s3 h3 hv3 _ => ?_
  refine h3.cntInit hv3 (e := 4) (by decide) (by have := sz.Wle; omega) fun s4 h4 hv4 => ?_
  refine h4.toN hv4 fun t ht hvt _ => WP.block_nil ⟨e, ?_, hvt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [LS5, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [AS, AM4, AB, rs, Function.iterate_zero, id] <;>
      rd_ev
  · simp only [LWM, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl <;> simp only [AWS, AWM, rs, Function.iterate_zero, id] <;> rd_ev
  · simp only [LSS5, List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp only [VS] <;> rd_up <;> simp

theorem carry_le {x N : Nat} (hx : x < N) : (2 * x + 0) / N ≤ 1 := by
  have := Nat.div_lt_of_lt_mul (show 2 * x + 0 < N * 2 by omega); omega

theorem rs_succ (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) :
    rs P f g h σ (k + 1) = h (rs P f g h σ k) := by
  simp only [rs]; rw [Function.iterate_succ_apply']

theorem sqrtBody_ok {f g h : Nat × Nat × Nat → Nat × Nat × Nat} (hh : SqrtF P h) {σ s : State} {k : Nat}
    (hS : SI P f g h k σ s) (hk : k < 16 * P.W) :
    WP isa sqrtBody s fun t => SI P f g h (k + 1) σ t ∧ t.z = decide (16 * P.W - (k + 1) = 0) := by
  obtain ⟨h0, hv⟩ := hS
  have sz := h0.sizes
  have Wl := sz.Wle
  have wpos : 1 ≤ 32 * P.w := by show 1 ≤ 32 * (2 * P.w6 + 2); omega
  have xl := h0.lt_W (j := wR) (by decide)
  have rl := h0.lt_w (j := aRm) (by decide)
  have yl := h0.lt_w (j := aY) (by decide)
  generalize ex : (rs P f g h σ k).1 = x at *
  generalize er : (rs P f g h σ k).2.1 = r at *
  generalize ey : (rs P f g h σ k).2.2 = y at *
  have wR' : AWS P f g h σ k wR = x := by simp only [AWS]; rd_up; exact ex
  have aR' : AS P f g h σ k aRm = r := by simp only [AS]; rd_up; exact er
  have aY' : AS P f g h σ k aY = y := by simp only [AS]; rd_up; exact ey
  rw [wR'] at xl; rw [aR'] at rl; rw [aY'] at yl
  simp only [sqrtBody, seqs]
  -- The top two bits into the remainder.
  refine WP.seq (h0.toW hv fun s1 h1 hv1 _ => h1.clr11 hv1 fun s2 h2 hv2 z2 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h2.shl_W hv2 (j := wR) (by decide) (by omega) (by decide))
    fun s3 ⟨h3, hv3, c3, _⟩ => ?_)
  rw [z2, wR'] at h3 c3
  refine WP.seq (h3.toN hv3 fun s4 h4 hv4 r4 => WP.block_nil ?_)
  have c4 : (s4.gpr .r11).toNat = (2 * x + 0) / 2 ^ (32 * P.W) := by rw [r4.gpr _ (by decide)]; exact c3
  refine WP.seq (WP.mono (h4.shl_w hv4 (j := aRm) (by decide) (by rw [c4]; exact carry_le xl) (by decide))
    fun s5 ⟨h5, hv5, _, _⟩ => ?_)
  rw [c4, aR'] at h5
  refine WP.seq (h5.toW hv5 fun s6 h6 hv6 _ => h6.clr11 hv6 fun s7 h7 hv7 z7 => WP.block_nil ?_)
  have x1l : (2 * x + 0) % 2 ^ (32 * P.W) < 2 ^ (32 * P.W) := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine WP.seq (WP.mono (h7.shl_W hv7 (j := wR) (by decide) (by omega) (by decide))
    fun s8 ⟨h8, hv8, c8, _⟩ => ?_)
  rw [z7] at h8 c8
  rw [upd_self] at h8 c8
  refine WP.seq (h8.toN hv8 fun s9 h9 hv9 r9 => WP.block_nil ?_)
  have c9 : (s9.gpr .r11).toNat = (2 * ((2 * x + 0) % 2 ^ (32 * P.W)) + 0) / 2 ^ (32 * P.W) := by
    rw [r9.gpr _ (by decide)]; exact c8
  refine WP.seq (WP.mono (h9.shl_w hv9 (j := aRm) (by decide) (by rw [c9]; exact carry_le x1l) (by decide))
    fun s10 ⟨h10, hv10, _, _⟩ => ?_)
  rw [c9, upd_self] at h10
  -- `4 y + 1`.
  refine WP.seq (WP.mono (h10.copy_w hv10 (o := aTy) (a := aY) (by decide) (by decide) (by decide)
    (by decide)) fun s11 ⟨h11, hv11, _, _⟩ => ?_)
  refine WP.seq (h11.clr11 hv11 fun s12 h12 hv12 z12 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h12.shl_w hv12 (j := aTy) (by decide) (by omega) (by decide))
    fun s13 ⟨h13, hv13, _, _⟩ => ?_)
  rw [z12] at h13
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s14 u14 => WP.block_nil ?_)
  obtain ⟨h14, hv14⟩ := h13.reg hv13 (u14.rest (ws := [.r11]) (by simp)) u14.mem
  have z14 : (s14.gpr .r11).toNat = 1 := by rw [u14.gpr]; rfl
  refine WP.seq (WP.mono (h14.shl_w hv14 (j := aTy) (by decide) (by omega) (by decide))
    fun s15 ⟨h15, hv15, _, _⟩ => ?_)
  rw [z14, upd_self] at h15
  -- The comparison and the selection.
  have h15' := h15.mono (A' := upd (upd (AS P f g h σ k) aRm
      ((2 * ((2 * r + (2 * x + 0) / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w)) +
        (2 * ((2 * x + 0) % 2 ^ (32 * P.W)) + 0) / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w)))
      aTy ((2 * ((2 * y + 0) % 2 ^ (32 * P.w)) + 1) % 2 ^ (32 * P.w))) (live' := aTy :: LS5)
    (AW' := upd (AWS P f g h σ k) wR ((2 * ((2 * x + 0) % 2 ^ (32 * P.W)) + 0) % 2 ^ (32 * P.W)))
    (liveW' := LWM) (V' := VS P f g σ k) (ls' := LSS5)
    (fun j hj => by
      simp only [LS5, List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rd_up <;> simp only [aY'])
    (fun j hj => by
      simp only [LWM, List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl <;> rd_up)
    (fun d hd => ⟨hd, rfl⟩)
  generalize eR2 : (2 * ((2 * r + (2 * x + 0) / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w)) +
    (2 * ((2 * x + 0) % 2 ^ (32 * P.W)) + 0) / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w) = R2 at h15'
  generalize eT2 : (2 * ((2 * y + 0) % 2 ^ (32 * P.w)) + 1) % 2 ^ (32 * P.w) = T2 at h15'
  generalize eX2 : (2 * ((2 * x + 0) % 2 ^ (32 * P.W)) + 0) % 2 ^ (32 * P.W) = X2 at h15'
  refine WP.seq (WP.mono (h15'.sub_w hv15 (o := aDf) (a := aRm) (b := aTy) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s16 ⟨h16, hv16, _, c16⟩ => ?_)
  refine WP.seq (h16.brw hv16 (d := sBb) (by decide) fun s17 h17 hv17 _ => WP.block_nil ?_)
  rw [c16] at h17
  refine WP.seq (WP.mono (h17.copy_w hv17 (o := aT1) (a := aRm) (by decide) (by decide) (by decide)
    (by decide)) fun s18 ⟨h18, hv18, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h18.sel_w hv18 (o := aRm) (a := aDf) (b := aT1) (sl := sBb) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [upd_self]; exact b2n_lt_one _) (by decide))
    fun s19 ⟨h19, hv19, _⟩ => ?_)
  have vR : upd (upd (AS P f g h σ k) aRm R2) aTy T2 aRm = R2 := by rd_up
  have vT : upd (upd (AS P f g h σ k) aRm R2) aTy T2 aTy = T2 := by rd_up
  rw [vR, vT] at h19
  generalize eB : b2n (decide (R2 < T2)) = Bb at h19
  have bl : Bb ≤ 1 := eB ▸ b2n_lt_one _
  -- The root's bit.
  refine WP.seq (h19.ldrSlot hv19 (d := sBb) (r := .r11) (by decide) (by decide) fun s20 h20 hv20 u20 => ?_)
  refine wp_dp (op2_imm (by decide)) fun s21 u21 => WP.block_nil ?_
  obtain ⟨h21, hv21⟩ := h20.reg hv20 (u21.rest (ws := [.r11]) (by simp)) u21.mem
  have z21 : (s21.gpr .r11).toNat = 1 - Bb := by
    rw [u21.gpr, dpVal, u20.gpr, upd_self,
      VG.Proof.Rsa.KeyBits32.bv_xor_bits (by rw [BitVec.toNat_ofNat]; omega) (by decide), BitVec.toNat_ofNat]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine WP.seq (WP.mono (h21.shl_w hv21 (j := aY) (by decide) (by rw [z21]; omega) (by decide))
    fun s22 ⟨h22, hv22, _, _⟩ => ?_)
  rw [z21] at h22
  have vK : VS P f g σ k sK = 16 * P.W - k := by simp only [VS]; rd_up
  refine WP.mono (h22.cntNext hv22 (by decide) (by rd_up; rw [vK]; omega) (by rd_up; rw [vK]; omega))
    fun t ⟨ht, hvt, zt⟩ => ⟨⟨?_, hvt⟩, by rw [zt]; rd_up; rw [vK, Nat.sub_sub]⟩
  -- The step.
  have hs := rs_succ P f g h σ k
  rw [show rs P f g h σ k = (x, r, y) from Prod.ext ex (Prod.ext er ey), hh] at hs
  have hi := carry_le xl
  have lo := carry_le x1l
  have eR1 : (2 * r + (2 * x + 0) / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w) =
      2 * r % 2 ^ (32 * P.w) + 2 * x / 2 ^ (32 * P.W) := by rw [shl_mod (by simpa using hi) wpos]; simp
  have eR2' : R2 = 2 * (2 * r % 2 ^ (32 * P.w) + 2 * x / 2 ^ (32 * P.W)) % 2 ^ (32 * P.w) +
      2 * (2 * x % 2 ^ (32 * P.W)) / 2 ^ (32 * P.W) := by
    rw [← eR2, eR1, shl_mod (by simpa using lo) wpos]; simp
  have eT2' : T2 = 2 * (2 * y % 2 ^ (32 * P.w)) % 2 ^ (32 * P.w) + 1 := by
    rw [← eT2, shl_mod (by omega) wpos]; simp
  have eX2' : X2 = 2 * (2 * x % 2 ^ (32 * P.W)) % 2 ^ (32 * P.W) := by rw [← eX2]; simp
  have R2l : R2 < 2 ^ (32 * P.w) := eR2 ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [← eR2', ← eT2', ← eX2'] at hs
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [LS5, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> rd_up <;> simp only [AS, hs, ey] <;> rd_up
    · by_cases c : R2 < T2
      · have : Bb = 1 := by rw [← eB]; simp [c, b2n]
        simp [c, this]
      · have : Bb = 0 := by rw [← eB]; simp [c, b2n]
        simp [c, this, sub32_le R2l (Nat.le_of_not_lt c)]
    · by_cases c : R2 < T2
      · have : Bb = 1 := by rw [← eB]; simp [c, b2n]
        simp [c, this]
      · have : Bb = 0 := by rw [← eB]; simp [c, b2n]
        simp [c, this, shl_mod (v := y) (c := 1) (by omega) wpos]
  · simp only [LWM, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl <;> rd_up <;> simp only [AWS, hs] <;> rd_up <;> split <;> rfl
  · simp only [LSS5, List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> rd_up <;> simp only [VS] <;> rd_up <;> omega

/-- The root and the remainder. -/
abbrev yV (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := (rs P f g h σ (16 * P.W)).2.2
abbrev rmV (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := (rs P f g h σ (16 * P.W)).2.1

def AR (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AB P) aB (bV P f g σ)) aY (yV P f g h σ)
def VR (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (VM4 P f g σ) sOk5 (if rmV P f g h σ = 0 then 1 else 0)
abbrev LR : List Nat := [aY, aB, aN, aZN, aOneN]
abbrev LSR : List Nat := [sOk5, sOk4, sExact, sLt, sOkDE]

theorem sqrt_vp {f g h : Nat × Nat × Nat → Nat × Nat × Nat} (hh : SqrtF P h) {E : State → Prop} :
    VP (Dk P E (AM4 P f g) LM4 (AWM P f g) LWM (VM4 P f g) LSM P.w nArr) sqrt
      (Dk P E (AR P f g h) LR (fun _ => upd (upd (fun _ => 0) wZ 0) wOne 1) [wOne, wZ] (VR P f g h) LSR
        P.w nArr) := by
  simp only [sqrt, seqs]
  refine (sqrtPre_vp (h := h)).seq (VP.seq (G := fun σ s => E σ ∧ SI P f g h (16 * P.W) σ s) ?_ ?_)
  · refine VP.of_imp (p := 0 < 16 * P.W) (fun σ s ⟨_, h, _⟩ => by show 0 < 16 * (2 * (2 * P.w6 + 2) + 2); omega)
      fun pos => ?_
    exact VP.count (E := E) (I := SI P f g h) pos fun k hk => VP.dctx sqrtBody_taint (fun _ _ h => h.2.2)
      fun σ s ⟨e, h0⟩ => WP.mono (sqrtBody_ok hh h0 hk) fun t ⟨ht, z⟩ => ⟨⟨e, ht⟩, z⟩
  · refine VP.dctx eqOk5_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h0, hv⟩ => ?_
    refine WP.mono (h0.eqS_w hv (d := sOk5) (a := aRm) (b := aZN) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht, hvt, _⟩ => ⟨e, ?_, hvt⟩
    refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
    · simp only [LR, List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [AS, AR, AM4, AB] <;> rd_ev
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl <;> simp only [AWS, AWM] <;> rd_ev
    · simp only [LSR, List.mem_cons, List.not_mem_nil, or_false] at hd
      refine ⟨by rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp only [VR, VS, AS, AM4, AB] <;> rd_ev

/-! ## The factors -/

theorem b2n_and' (p q : Bool) : b2n (decide (b2n p = 1 ∧ b2n q = 1)) = b2n (p && q) := by
  cases p <;> cases q <;> rfl

theorem ite10_le (p : Prop) [Decidable p] : (if p then 1 else 0 : Nat) ≤ 1 := by split <;> omega

theorem ite_b2n (p : Prop) [Decidable p] : (if p then 1 else 0) = b2n (decide p) := by
  by_cases h : p <;> simp [h, b2n]

/-- The factors and the mask. -/
abbrev pV (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  (bV P f g σ + yV P f g h σ) % 2 ^ (32 * P.w) / 2
abbrev qV' (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.w (bV P f g σ) (yV P f g h σ) / 2
abbrev okV (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Bool :=
  okDEv P σ && decide (aV P f g σ / P.n < P.n) && decide (remV P f g σ = 0) && ok4v P f g σ &&
    decide (rmV P f g h σ = 0)

def AFac (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (fun _ => 0) aP (pV P f g h σ)) aQ (qV' P f g h σ)
def VFac (P : RP) (f g h : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (fun _ => 0) sMask (b2n (okV P f g h σ))

theorem factors_vp {f g h : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (AR P f g h) LR (fun _ => upd (upd (fun _ => 0) wZ 0) wOne 1) [wOne, wZ] (VR P f g h) LSR
      P.w nArr) factors
      (Dk P E (AFac P f g h) [aQ, aP] (fun _ _ => 0) [] (VFac P f g h) [sMask] P.w nArr) := by
  refine VP.dctx factors_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h0, hv⟩ => ?_
  simp only [factors, seqs]
  refine WP.seq (WP.mono (h0.add_w hv (o := aP) (a := aB) (b := aY) (t := aT1) (z := aZN) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp only [AR, AB]; rd_ev) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s1 ⟨h1, hv1⟩ => ?_)
  refine WP.seq (h1.clr11 hv1 fun s2 h2 hv2 z2 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h2.half_w hv2 (j := aP) (by decide) z2 (by decide)) fun s3 ⟨h3, hv3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.sub_w hv3 (o := aQ) (a := aB) (b := aY) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s4 ⟨h4, hv4, _, _⟩ => ?_)
  refine WP.seq (h4.clr11 hv4 fun s5 h5 hv5 z5 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h5.half_w hv5 (j := aQ) (by decide) z5 (by decide)) fun s6 ⟨h6, hv6, _⟩ => ?_)
  simp only [List.append_assoc]
  have bit : ∀ d ∈ LSR, VR P f g h σ d ≤ 1 := by
    intro d hd
    simp only [LSR, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp only [VR, VM4, VB, VA, VG'] <;> rd_up <;>
      first | (split <;> omega) | exact b2n_lt_one _ | (unfold b2n; split <;> omega)
  refine h6.andS hv6 (d := sMask) (a := sOkDE) (b := sLt) (by decide) (by decide) (bit _ (by decide))
    (bit _ (by decide)) (by decide) fun s7 h7 hv7 => ?_
  refine h7.andS hv7 (d := sMask) (a := sMask) (b := sExact) (by decide) (by decide)
    (by rd_up; exact ite10_le _) (by rd_up; exact bit _ (by decide)) (by decide) fun s8 h8 hv8 => ?_
  refine h8.andS hv8 (d := sMask) (a := sMask) (b := sOk4) (by decide) (by decide)
    (by rd_up; exact ite10_le _) (by rd_up; exact bit _ (by decide)) (by decide) fun s9 h9 hv9 => ?_
  refine h9.andS hv9 (d := sMask) (a := sMask) (b := sOk5) (by decide) (by decide)
    (by rd_up; exact ite10_le _) (by rd_up; exact bit _ (by decide)) (by decide) fun t ht hvt =>
      WP.block_nil ⟨e, ?_, hvt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => by simp at hj) (fun d hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl <;> simp only [AFac, AR, AB] <;> rd_ev
  · simp only [List.mem_singleton] at hd; subst hd
    refine ⟨by decide, ?_⟩
    simp only [upd_self, VFac]
    rd_up
    simp only [VR, VM4, VB, VA, VG', ite_b2n]
    rd_up
    simp only [b2n_and']

end

end VG.Proof.Rsa.Arm.RecoverDet
