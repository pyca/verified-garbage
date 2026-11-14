module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdSqrtL

import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: `b² - 4 n`, its square root and the factors

`square_vp`: `b = q + 1` and `b²` (`product_vp`); `minus4n_vp`: `4 n`,
`b² - 4 n` and whether it is positive; `sqrt_vp`: its integer square root
(`isqrt`) by words, and whether it is exact (`RdSqrtW.lean` to
`RdSqrtL.lean`); `factors_vp`: the factors and the mask of every check.
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

/-- `b²`. -/
abbrev sqV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  (pr g (bV P f g σ) (bV P f g σ) (32 * P.w)).2.2

theorem square_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (fun σ => upd (AB P) aD (qV P f g σ)) [aD, aN, aZN, aOneN] (fun _ => AWB P) LWB (VB P f g) LSB
      P.w nArr) square (fun σ s => E σ ∧ RI P aB wB wA (ASQ P f g) LSQ (AWSQ P f g) LWSQ (VB P f g) LSB σ s) :=
  squarePre_vp.seq (rowProd_vp (Y := 2) (by constructor <;> decide) (by decide) (by decide)
    (fun σ _ => by simp only [AWSQ, AWB]; rd_up) copyA_taint pRowA_taint pRowBB_taint)

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

theorem minus4n_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} (hg : ProdF P g) {E : State → Prop} :
    VP (fun σ s => E σ ∧ RI P aB wB wA (ASQ P f g) LSQ (AWSQ P f g) LWSQ (VB P f g) LSB σ s)
      minus4n (Dk P E (AM4 P f g) LM4 (AWM P f g) LWM (VM4 P f g) LSM P.w nArr) := by
  refine VP.dctx minus4n_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  have sq : sqV P f g σ = bV P f g σ % 2 ^ (32 * P.w) * bV P f g σ % 2 ^ (32 * P.W) := by
    have := h.lt_W (j := wB) (by decide)
    rw [upd_ne _ _ (by decide)] at this
    simp only [AWSQ] at this; rw [upd_self] at this
    exact pr_rows hg this _
  simp only [minus4n, seqs]
  refine WP.seq (h.toW hv fun s1 h1 hv1 _ => h1.clr11 hv1 fun s2 h2 hv2 z2 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h2.shl_W hv2 (j := wN) (by decide) (by omega_using [z2]) (by decide))
    fun s3 ⟨h3, hv3, _, _⟩ => ?_)
  rw [z2] at h3
  refine WP.seq (h3.clr11 hv3 fun s4 h4 hv4 z4 => WP.block_nil ?_)
  refine WP.seq (WP.mono (h4.shl_W hv4 (j := wN) (by decide) (by omega_using [z4]) (by decide))
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
    rcases hj with rfl | rfl | rfl <;> simp only [AWM, AWSQ, AWB, ASQ, AB, xRV, fourV, sq] <;> rd_ev
  · simp only [LSM, List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl | rfl | rfl
    · rd_up; rw [c6, c8, b2n_nor]; simp only [VM4, ok4v, xRV, fourV, sq, AWSQ, AWB, ASQ, AB]; rd_ev
    all_goals simp only [VM4]; rd_up

/-! ## The square root -/

section
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa.RecoverDet (isqrt_sq_le)
open VG.Impl.Rsa.Arm.KeyDiv (sD sD1 sV)

theorem sub32_le {w a b : Nat} (ha : a < 2 ^ (32 * w)) (hb : b ≤ a) : sub32 w a b = a - b := by
  unfold sub32
  rw [show a + 2 ^ (32 * w) - b = (a - b) + 2 ^ (32 * w) by omega_using [ha, hb], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [ha])]

/-- The root, to `w` words, and the remainder. -/
abbrev yV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  isqrt (xRV P f g σ) % 2 ^ (32 * P.w)
abbrev rmV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  xRV P f g σ - isqrt (xRV P f g σ) * isqrt (xRV P f g σ)

def AR (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AB P) aB (bV P f g σ)) aY (yV P f g σ)
def VR (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (VM4 P f g σ) sOk5 (if rmV P f g σ = 0 then 1 else 0)
abbrev LR : List Nat := [aY, aB, aN, aZN, aOneN]
abbrev LSR : List Nat := [sOk5, sOk4, sExact, sLt, sOkDE]

/-- The normalized root, shifted down, is `X`'s (0 where `X` was 0, and 1 replaced it). -/
theorem root_norm (P : RP) (X : Nat) :
    (if (if X = 0 then 1 else 0) = 0 then isqrt (nX P X) / 2 ^ (lzX P X / 2) else 0) = isqrt X := by
  by_cases h : X = 0
  · subst h; simp only [↓reduceIte, Nat.one_ne_zero]; exact isqrt_zero.symm
  · simp only [h, ↓reduceIte, nX, xz]
    rw [Nat.mul_comm]; exact VG.Proof.Bignum.SqrtRem.norm_sqrt _ _

theorem isqrt_one : isqrt 1 = 1 := by
  have h1 := VG.Proof.Rsa.Arm.RecoverDet.le_isqrt (s := 1) (x := 1) (by decide)
  have h2 := isqrt_sq_le 1
  have : isqrt 1 ≤ 1 := by
    refine Nat.le_of_not_lt fun c => ?_
    have := Nat.mul_le_mul (show 2 ≤ isqrt 1 by omega_using [c]) (show 2 ≤ isqrt 1 by omega_using [c])
    omega_using [h2, this]
  omega_using [h1, this]

/-- The normalized `X` is a square exactly where `X` is. -/
theorem square_norm (P : RP) (X : Nat) :
    nX P X - isqrt (nX P X) * isqrt (nX P X) = 0 ↔ X - isqrt X * isqrt X = 0 := by
  have e : ∀ x, x - isqrt x * isqrt x = 0 ↔ isqrt x * isqrt x = x := fun x => by
    have := isqrt_sq_le x; omega_using [this]
  rw [e, e]
  simp only [nX]
  rw [Nat.mul_comm (xz X), VG.Proof.Bignum.SqrtRem.norm_square]
  by_cases h : X = 0
  · subst h; simp only [xz, ↓reduceIte, isqrt_one, isqrt_zero]
  · simp only [xz, h, ↓reduceIte]

theorem topA_last (P : RP) (x : Nat) : topA P.W x (P.w + 1) = x := by
  simp only [topA, show P.W - 2 * (P.w + 1) = 0 by simp only [RP.W]; omega_using [], Nat.mul_zero, Nat.pow_zero,
    Nat.div_one]

/-- The wide arrays of the digits. -/
abbrev LWQ : List Nat := [wE, wD, wR, wOne, wZ]
/-- The slots of the digits. -/
abbrev LSQ' : List Nat := [sCm, sD1, sLn, sK, sMo, sPo, sV, sD, sLz, sZ, sOk4, sExact, sLt, sOkDE]

/-- The square root of `b² - 4 n`, by words: `X` normalized, its top two words' root, a digit per two
words, the root shifted back and its low `w` words into `[aY]`, and whether the remainder is 0. -/
theorem sqrt_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (AM4 P f g) LM4 (AWM P f g) LWM (VM4 P f g) LSM P.w nArr) sqrt
      (Dk P E (AR P f g) LR (fun _ => upd (upd (fun _ => 0) wZ 0) wOne 1) [wOne, wZ] (VR P f g) LSR
        P.w nArr) := by
  refine VP.of_imp (p := 1 ≤ P.w ∧ P.W ≤ 518) (fun σ s h => ⟨by have := h.2.1.sizes.w6a; simp only [RP.w]; omega_using [],
    h.2.1.sizes.Wle⟩) fun ⟨w1, Wl⟩ => ?_
  have hW : P.W = 2 * P.w + 2 := rfl
  have xl : ∀ σ, AWM P f g σ wR < 2 ^ (32 * P.W) := fun σ => by simp only [AWM]; rd_up; exact sub32_lt _ _ _
  simp only [sqrt, seqs]
  refine toW_vp.seq ?_
  refine (normX_vp (by decide) (by decide) (fun σ _ => by simp only [AWM]; rd_up) (by decide) (by decide)
    (by decide)).seq ?_
  refine (firstDigit_vp (by decide) (by decide) (by decide) (by decide) (fun σ _ => by simp only [AWM]; rd_up)
    (fun σ _ => by simp only [AWM]; rd_up)
    (fun σ _ => by rd_up; exact (nX_bounds (xl σ)).1) (fun σ _ => by rd_up; exact (nX_bounds (xl σ)).2.1)
    (by omega_arith)).seq ?_
  refine sqInit_vp.seq ?_
  -- the digits
  let AWb : State → Nat → Nat := fun σ => upd (AWM P f g σ) wR (nX P (AWM P f g σ wR))
  let Vb : State → Nat → Nat := fun σ => upd (upd (VN (VM4 P f g σ) (AWM P f g σ wR)
    (lzX P (AWM P f g σ wR))) sD (sJ P.W (nX P (AWM P f g σ wR)) 1)) sV
    ((2 ^ 64 - 1) / sJ P.W (nX P (AWM P f g σ wR)) 1 - 2 ^ 32)
  refine VP.seq (G := fun σ s => E σ ∧ Dk P E (AM4 P f g) LM4 (fun σ => DAW P.W (P.w + 1) (AWb σ)) LWQ
      (fun σ => DV P.W P.w (P.w + 1) (sJ P.W (AWb σ wR) (P.w + 1)) (Vb σ)) LSQ' P.W 22 σ s)
    (VP.mono (sqLoop_vp (K := P.w) (AW := AWb) (V := Vb) hW.symm w1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
      (fun σ _ => by simp only [AWb]; rd_up; exact (nX_bounds (xl σ)).1)
      (fun σ _ => by simp only [AWb]; rd_up; exact (nX_bounds (xl σ)).2.1)
      (fun σ _ => by simp only [Vb, AWb]; rd_up) (fun σ _ => by simp only [Vb]; rd_up))
      (fun σ s ⟨e, h, hv⟩ => ⟨e, e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, ?_⟩), hv⟩)
      (fun _ _ h => h)) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Vb, DV, VN, AWb] <;> rd_up
    · omega_arith
    · simp only [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_mod_left]
    · omega_using [hW]
    · omega_arith
  -- the root `D / 2`
  refine VP.seq (VP.mono (sqEnd_vp (by decide) (by decide)) (fun σ s h => h.2) fun _ _ h => h) ?_
  -- the finish
  have hK0 : P.W / 2 - (P.w + 1) = 0 := by omega_using [hW]
  refine VP.mono (sqFinish_vp (L := LM4) (LW := [wR, wS, wOne, wZ]) (LS := [sLz, sZ, sOk4, sExact, sLt, sOkDE])
    (v := fun σ => isqrt (nX P (AWM P f g σ wR))) (lz := fun σ => lzX P (AWM P f g σ wR))
    (z := fun σ => if AWM P f g σ wR = 0 then 1 else 0) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun σ _ => by simp only [DAW, AWb, AWM]; rd_up)
    (fun σ _ => by
      simp only [DAW, Dv, AWb, sJ]; rd_up
      rw [topA_last, hK0, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_div_cancel_left _ (by decide)])
    (fun σ _ => by simp only [DV, Vb, VN]; rd_up) (fun σ _ => by simp only [DV, Vb, VN]; rd_up)
    (fun σ _ => by split <;> omega_using []) (fun σ _ => (nX_bounds (xl σ)).2.2)
    (fun σ _ => by
      have b := (nX_bounds (xl σ)).2.1
      have sq := isqrt_sq_le (nX P (AWM P f g σ wR))
      have we : 32 * P.W = 32 * (P.W / 2) + 32 * (P.W / 2) := by omega_using [hW]
      rw [we, Nat.pow_add] at b
      exact Nat.lt_of_not_le fun h => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul h h) sq) b)))
    (fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => ⟨(show [wR, wS, wOne, wZ] ⊆ wS :: LWQ by decide) hj, rfl⟩)
      (fun d hd => ⟨(show [sLz, sZ, sOk4, sExact, sLt, sOkDE] ⊆ LSQ' by decide) hd, rfl⟩), hv⟩)
    (fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨?_, ?_⟩), hv⟩)
  · simp only [LR, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [LR, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [AR, AM4, AB] <;> rd_up
    rw [root_norm]; simp only [AWM]; rd_up
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp only [DAW, AWb, AWM] <;> rd_up
  · simp only [LSR, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [LSR, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp only [VR, DV, Vb, VN] <;> rd_up
    simp only [Rv, AWb, rJ, sJ, rmV]; rd_up
    rw [topA_last, show P.W - 2 * (P.w + 1) = 0 by omega_using [hW], Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add,
      Nat.one_mul]
    by_cases c : xRV P f g σ - isqrt (xRV P f g σ) * isqrt (xRV P f g σ) = 0
    · simp only [AWM] at *; rd_up; simp only [(square_norm P _).mpr c, c, ↓reduceIte]
    · simp only [AWM] at *; rd_up
      simp only [show ¬ (_ = 0) from fun h' => c ((square_norm P _).mp h'), c, ↓reduceIte]

end

/-! ## The factors -/

theorem b2n_and' (p q : Bool) : b2n (decide (b2n p = 1 ∧ b2n q = 1)) = b2n (p && q) := by
  cases p <;> cases q <;> rfl

theorem ite10_le (p : Prop) [Decidable p] : (if p then 1 else 0 : Nat) ≤ 1 := by split <;> omega_using []

theorem ite_b2n (p : Prop) [Decidable p] : (if p then 1 else 0) = b2n (decide p) := by
  by_cases h : p <;> simp [h, b2n]

/-- The factors and the mask. -/
abbrev pV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  (bV P f g σ + yV P f g σ) % 2 ^ (32 * P.w) / 2
abbrev qV' (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.w (bV P f g σ) (yV P f g σ) / 2
abbrev okV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Bool :=
  okDEv P σ && decide (aV P f g σ / P.n < P.n) && decide (remV P f g σ = 0) && ok4v P f g σ &&
    decide (rmV P f g σ = 0)

def AFac (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (fun _ => 0) aP (pV P f g σ)) aQ (qV' P f g σ)
def VFac (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (fun _ => 0) sMask (b2n (okV P f g σ))

theorem factors_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (AR P f g) LR (fun _ => upd (upd (fun _ => 0) wZ 0) wOne 1) [wOne, wZ] (VR P f g) LSR
      P.w nArr) factors
      (Dk P E (AFac P f g) [aQ, aP] (fun _ _ => 0) [] (VFac P f g) [sMask] P.w nArr) := by
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
  have bit : ∀ d ∈ LSR, VR P f g σ d ≤ 1 := by
    intro d hd
    simp only [LSR, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp only [VR, VM4, VB, VA, VG'] <;> rd_up <;>
      first | (split <;> omega_using []) | exact b2n_lt_one _ | (unfold b2n; split <;> omega_using [])
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
    rcases hj with rfl | rfl <;> simp only [AFac, AR, AB] <;> rd_ev <;> simp only [pV, yV, Nat.add_mod_mod]
  · simp only [List.mem_singleton] at hd; subst hd
    refine ⟨by decide, ?_⟩
    simp only [upd_self, VFac]
    rd_up
    simp only [VR, VM4, VB, VA, VG', ite_b2n]
    rd_up
    simp only [b2n_and']

end

end VG.Proof.Rsa.Arm.RecoverDet
