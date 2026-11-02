module
-- separate module: its proofs build in parallel with the constant-time ones, `CTBase`, `CTParts` and `CTLoops`

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root and the factors

The square root's stage (`sqrtS_ok`): `rootOf`'s root, and the mask and'ed
with whether its remainder is zero; the factors `(b + ϒ) / 2` and
`(b - ϒ) / 2`, written under the mask, and the exit (`factors_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet

/-- What the square root's stage changes: arrays 4 to 7, wide array 7, the
mask and the header slots 25 and 30. -/
def SqP (w y : Nat) : Prop :=
  (slot w 4 ≤ y ∧ y < slot w 8) ∨ (slot w 14 ≤ y ∧ y < slot w 14 + 8 * (2 * w + 2)) ∨ (200 ≤ y ∧ y < 208) ∨
    (240 ≤ y ∧ y < 248) ∨ (176 ≤ y ∧ y < 184)

macro "sqs_omega" : tactic =>
  `(tactic| (simp only [SqP, SqrtP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, sFn, sCt, sC]; omega_arith))

/-- The square root's stage (narrow): `64 (w + 1)` steps of `sqrtStep` from `X`
(wide array 7), the root into array 5, and the mask and'ed with whether
the remainder is zero. -/
theorem sqrtS_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {X : Nat} {c : Bool}
    (hX : wv s.mem B (slot w 14) (2 * w + 2) = X) (hz : wv s.mem B (slot w 3) w = 0) (hm : mw s.mem B = mask c) :
    WP isa (seqs RecoverDet.sqrt) s fun t =>
      wv t.mem B (slot w 5) w = ((sqrtStep (64 * w) (64 * (2 * w + 2)))^[64 * (w + 1)] (X, 0, 0)).2.2 ∧
      mw t.mem B = mask (c && decide (((sqrtStep (64 * w) (64 * (2 * w + 2)))^[64 * (w + 1)] (X, 0, 0)).2.1 = 0)) ∧
      FrmP B (SqP w) s.mem t.mem ∧ Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .rbp, .rsi, .r10, .rdx] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  simp only [RecoverDet.sqrt, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (zeroA_ok h (j := 4) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by sqs_omega) k1 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := 5) (by decide)) fun t₂ ⟨z2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by sqs_omega) k2 (by simp)
  refine WP.seq (WP.mono (countW_ok h₂) fun t₃ ⟨m3, k3⟩ => ?_)
  have h₃ := h₂.congrW m3 (by sqs_omega) (by decide) k3 (by simp)
  have o3 : Outside B (8 * sCt) 8 t₂.mem t₃.mem := by rw [m3]; exact writeW_outside _ _ _ (by sqs_omega)
  have X₃ : wv t₃.mem B (slot w 14) (2 * w + 2) = X := by
    rw [o3.wv (by sqs_omega) (by sqs_omega), o2.wv (by sqs_omega) (by sqs_omega), o1.wv (by sqs_omega) (by sqs_omega), hX]
  have R₃ : wv t₃.mem B (slot w 4) w = 0 := by
    rw [o3.wv (by sqs_omega) (by sqs_omega), o2.wv (by sqs_omega) (by sqs_omega),
      wv_low_of_lt (v := w) (w := w + 2) (by omega_arith) (by rw [z1]; exact Nat.two_pow_pos _), z1]
  have Y₃ : wv t₃.mem B (slot w 5) w = 0 := by
    rw [o3.wv (by sqs_omega) (by sqs_omega),
      wv_low_of_lt (v := w) (w := w + 2) (by omega_arith) (by rw [z2]; exact Nat.two_pow_pos _), z2]
  have hct : word t₃.mem B (8 * sCt) = BitVec.ofNat 64 (64 * (w + 1)) := by rw [m3, word_writeW_self]
  -- The loop.
  refine wp_seqs_append (a := [.loop sqrtBody .ne]) (by simp) (by simp)
    (WP.mono (sqrtLoop_ok h₃ hct) fun t₄ hI => ?_)
  rw [X₃, R₃, Y₃] at hI
  have h₄ := hI.ws
  have hv := hI.val
  -- Whether the remainder is zero.
  have hz₄ : wv t₄.mem B (slot w 3) w = 0 := by
    rw [hI.frm.wv_eq (fun y => by sqs_omega) (by sqs_omega), o3.wv (by sqs_omega) (by sqs_omega),
      o2.wv (by sqs_omega) (by sqs_omega), o1.wv (by sqs_omega) (by sqs_omega), hz]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₄ (a := 4) (b := 3) (by decide) (by decide))
    fun t₅ ⟨hz5, m5, k5⟩ => ?_)
  rw [hz₄] at hz5
  have h₅ := h₄.congrP (FrmP.of_eq (P := fun _ => False) m5) (fun y hy => hy.elim) k5 (by simp)
  have hm₅ : mw t₅.mem B = mask c := by
    unfold mw at hm ⊢
    rw [m5, hI.frm.word_eq (fun y => by sqs_omega) (by sqs_omega), o3.word (by sqs_omega) (by sqs_omega),
      o2.word (by sqs_omega) (by sqs_omega), o1.word (by sqs_omega) (by sqs_omega), hm]
  simp only [seqs]
  refine WP.mono (andZero_ok h₅ hm₅ hz5) fun t ⟨m6, k6⟩ => ?_
  have o6 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₅.mem t.mem := by
    rw [m6]; exact writeW_outside _ _ _ (by sqs_omega)
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → SqP w y) →
      FrmP B (SqP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o6.wv (by sqs_omega) (by sqs_omega), m5]
    exact congrArg (fun p => p.2.2) hv
  · unfold mw
    rw [m6, word_writeW_self, ← congrArg (fun p => p.2.1) hv]
  · exact ((((((fr o1 fun y => by sqs_omega).trans (fr o2 fun y => by sqs_omega)).trans
      (fr o3 fun y => by sqs_omega)).trans (hI.frm.mono fun y => by sqs_omega)).trans (FrmP.of_eq m5)).trans
      (fr o6 fun y => by sqs_omega))
  · exact (((((k1.trans k2).trans k3).trans hI.keep).trans k5).trans k6).mono (by simp)

/-! ## The factors -/

/-- What the factors change before the stores: arrays 10 and 11. -/
def FcP (w y : Nat) : Prop := slot w 10 ≤ y ∧ y < slot w 12

macro "fc_omega" : tactic =>
  `(tactic| (simp only [FcP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith))

/-- The factors (narrow): `p = (b + y) mod 2^(64 w) / 2` and
`q = (b - y) mod 2^(64 w) / 2` for `b` (array 8) and the root `y` (array 5),
written to `pP` and `pQ` (`k` bytes each) under the mask, its low bit
returned and the saved registers restored. -/
theorem factors_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {k : Nat} {pP pQ : Addr}
    {sv : Nat → BitVec 64} {b y : Nat} {c : Bool}
    (hp : word s.mem B (8 * Recover.sP) = pP) (hq : word s.mem B (8 * Recover.sQ) = pQ)
    (hk : word s.mem B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k)
    (hsv : ∀ i < 6, word s.mem B (8 * i) = sv i) (hm : mw s.mem B = mask c) (hk1 : 1 ≤ k) (hk2 : k ≤ 8 * w)
    (hb : wv s.mem B (slot w 8) w = b) (hy : wv s.mem B (slot w 5) w = y)
    (hP : c = true → (b + y) % 2 ^ (64 * w) / 2 < 2 ^ (64 * ((k + 7) / 8)))
    (hQ : c = true → wsub (64 * w) b y / 2 < 2 ^ (64 * ((k + 7) / 8)))
    (oP : OutOk s B Z pP k) (oQ : OutOk s B Z pQ k) (a : Apart pP k pQ k) :
    WP isa (seqs factors) s fun t =>
      (List.range k).map (fun i => t.mem (pP + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then (b + y) % 2 ^ (64 * w) / 2 else 0) k ∧
      (List.range k).map (fun i => t.mem (pQ + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wsub (64 * w) b y / 2 else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = sv i) ∧
      (∀ x, (∀ i < k, x ≠ pP + BitVec.ofNat 64 i) → (∀ i < k, x ≠ pQ + BitVec.ofNat 64 i) →
        Z ≤ ofs B x → t.mem x = s.mem x) ∧
      Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  simp only [factors, List.cons_append, List.nil_append, List.append_assoc, seqs]
  -- `p`.
  refine WP.seq (WP.mono (zeroA_ok h (j := 10) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by fc_omega) k1 (by simp)
  refine WP.seq (WP.mono (addA_ok h₁ (o := 10) (a := 8) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  rw [o1.wv (by fc_omega) (by fc_omega), o1.wv (by fc_omega) (by fc_omega), hb, hy] at v2
  have h₂ := h₁.congrO o2 (by fc_omega) k2 (by simp)
  have z₂ : word t₂.mem B (slot w 10 + 8 * w) = 0 := by
    rw [o2.word (by fc_omega) (by fc_omega)]
    have := wv_zero_sub (a := w) (k := 1) z1 (by omega_arith)
    exact BitVec.eq_of_toNat_eq (by simpa [wv] using this)
  refine WP.seq (WP.mono (shrA_ok h₂ (j := 10) (by decide) z₂) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  rw [v2] at v3
  have h₃ := h₂.congrO o3 (by fc_omega) k3 (by simp)
  -- `q`.
  refine WP.seq (WP.mono (zeroA_ok h₃ (j := 11) (by decide)) fun t₄ ⟨z4, o4, k4⟩ => ?_)
  have h₄ := h₃.congrO o4 (by fc_omega) k4 (by simp)
  refine WP.seq (WP.mono (subA_ok h₄ (t := 11) (a := 8) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₅ ⟨_, e5, o5, k5⟩ => ?_)
  have b₄ : wv t₄.mem B (slot w 8) w = b := by
    rw [o4.wv (by fc_omega) (by fc_omega), o3.wv (by fc_omega) (by fc_omega), o2.wv (by fc_omega) (by fc_omega),
      o1.wv (by fc_omega) (by fc_omega), hb]
  have y₄ : wv t₄.mem B (slot w 5) w = y := by
    rw [o4.wv (by fc_omega) (by fc_omega), o3.wv (by fc_omega) (by fc_omega), o2.wv (by fc_omega) (by fc_omega),
      o1.wv (by fc_omega) (by fc_omega), hy]
  rw [b₄, y₄] at e5
  have q₅ := wsub_of_eq e5 (wv_lt _ _ _ _) (hb ▸ wv_lt _ _ _ _) (hy ▸ wv_lt _ _ _ _)
  have h₅ := h₄.congrO o5 (by fc_omega) k5 (by simp)
  have z₅ : word t₅.mem B (slot w 11 + 8 * w) = 0 := by
    rw [o5.word (by fc_omega) (by fc_omega)]
    have := wv_zero_sub (a := w) (k := 1) z4 (by omega_arith)
    exact BitVec.eq_of_toNat_eq (by simpa [wv] using this)
  refine WP.seq (WP.mono (shrA_ok h₅ (j := 11) (by decide) z₅) fun t₆ ⟨v6, o6, k6⟩ => ?_)
  rw [q₅] at v6
  have h₆ := h₅.congrO o6 (by fc_omega) k6 (by simp)
  have f6 : FrmP B (FcP w) s.mem t₆.mem :=
    (((((FrmP.of_out o1 fun y => by fc_omega).trans (FrmP.of_out o2 fun y => by fc_omega)).trans
      (FrmP.of_out o3 fun y => by fc_omega)).trans (FrmP.of_out o4 fun y => by fc_omega)).trans
      (FrmP.of_out o5 fun y => by fc_omega)).trans (FrmP.of_out o6 fun y => by fc_omega)
  have P₆ : wv t₆.mem B (slot w 10) w = (b + y) % 2 ^ (64 * w) / 2 := by
    rw [o6.wv (by fc_omega) (by fc_omega), o5.wv (by fc_omega) (by fc_omega), o4.wv (by fc_omega) (by fc_omega), v3]
  have hh : ∀ i < 32, word t₆.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    f6.word_eq (fun y => by fc_omega) (by omega_arith)
  have k16 := (((((k1.trans k2).trans k3).trans k4).trans k5).trans k6)
  -- The stores and the exit.
  have hm₆ : word t₆.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c := (hh _ (by decide)).trans hm
  refine wp_seqs_append (by simp [storeA]) (by simp [storeA]) (WP.mono (storeA_ws h₆ (j := 10) (by decide)
    (by decide) (by decide) ((hh _ (by decide)).trans hp) ((hh _ (by decide)).trans hk) hm₆ hk1 hk2
    (fun i hi => by rw [k16.2.2]; exact oP.wr i hi) oP.sep) fun t₇ ⟨b₇, x₇, h₇, f₇, k₇⟩ => ?_)
  have fw : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ i < 32, word m' B (8 * i) = word m B (8 * i) :=
    fun hf i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith))
      (by omega_arith)
  have fv : ∀ {m m' : Mem}, Frm B [(Z, 2 ^ 64)] m m' → ∀ j < 16, ∀ n ≤ w + 2,
      wv m' B (slot w j) n = wv m B (slot w j) n := fun hf j hj n hn' =>
    hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.sl hj; exact Or.inl (by omega_arith))
      (by have := h.sl hj; omega_arith)
  have hm₇ : word t₇.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c := by rw [fw f₇ _ (by decide)]; exact hm₆
  refine wp_seqs_append (by simp [storeA]) (by simp) (WP.mono (storeA_ws h₇ (j := 11) (by decide)
    (by decide) (by decide) (by rw [fw f₇ _ (by decide), hh _ (by decide)]; exact hq)
    (by rw [fw f₇ _ (by decide), hh _ (by decide)]; exact hk) hm₇ hk1 hk2
    (fun i hi => by rw [k₇.2.2, k16.2.2]; exact oQ.wr i hi) oQ.sep) fun t₈ ⟨b₈, x₈, h₈, f₈, k₈⟩ => ?_)
  have hm₈ : word t₈.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c := by rw [fw f₈ _ (by decide)]; exact hm₇
  simp only [seqs]
  refine WP.mono (cvExit_ok h₈ hm₈) fun t ⟨hax, hsv', hmt, k₉⟩ => ?_
  rw [hmt]
  have wk : (k + 7) / 8 ≤ w := by omega_arith
  refine ⟨?_, ?_, hax, fun i hi => ?_, fun x n1 n2 hx => ?_, (((k16.trans k₇).trans k₈).trans k₉).mono (by decide)⟩
  · have eP : (if c = true then wv t₆.mem B (slot w 10) ((k + 7) / 8) else 0) =
        (if c = true then (b + y) % 2 ^ (64 * w) / 2 else 0) := by
      cases c
      · rfl
      · simp only [↓reduceIte]
        rw [wv_low_of_lt (v := (k + 7) / 8) (w := w) wk (by rw [P₆]; exact hP rfl), P₆]
    rw [← eP, ← b₇]
    exact List.map_congr_left fun i hi => by
      have hi' := List.mem_range.mp hi
      rw [x₈ _ (fun j hj => a i hi' j hj)]
  · have eQ : (if c = true then wv t₇.mem B (slot w 11) ((k + 7) / 8) else 0) =
        (if c = true then wsub (64 * w) b y / 2 else 0) := by
      cases c
      · rfl
      · simp only [↓reduceIte]
        rw [fv f₇ _ (by decide) _ (by omega_arith),
          wv_low_of_lt (v := (k + 7) / 8) (w := w) wk (by rw [v6]; exact hQ rfl), v6]
    rw [← eQ]
    exact b₈
  · rw [hsv' i hi, fw f₈ _ (by omega_arith), fw f₇ _ (by omega_arith), hh _ (by omega_arith)]
    exact hsv i hi
  · rw [x₈ x n2, x₇ x n1]
    exact f6 x (by simp only [FcP, Bignum.slot, hdrBytes] at hx ⊢; omega_arith)

end VG.Proof.Rsa.X86_64.Rd
