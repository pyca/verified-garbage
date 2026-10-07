import VerifiedGarbage.Proof.Rsa.AArch64.RpCT3

/-!
# `vg_rsa_recover_primes` on AArch64: constant time, the squarings

Pieces of a candidate leak the same in runs whose working spaces agree:
`copyA`, `eqA` and blocks checked from `x0` (`copyA_gct`, `eqA_gct`,
`blk_gct`), a Montgomery multiplication (`mm_gct`). The squarings count a
public `64 Bw` (`sqLoop_ct`): their counter in `sC1` is pinned by
correctness.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

namespace Rp

/-! ## Pieces, from correctness -/

theorem copyA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {o a : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (copyA o a) s (Ψ x)) : RelCT isa (Two Φ) (copyA o a) (Two Ψ) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .x16 ++ base o .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct B Z w hws ht fun x s h => by rw [← e]; exact hw x s h

theorem eqA_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {a b : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block [movi .x9 0, mov .x14 .x12])
      (.seq (.block (base a .x16 ++ base b .x17)) (countLoop .x14 xorBody))) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (seqs (eqA a b)) s (Ψ x)) : RelCT isa (Two Φ) (seqs (eqA a b)) (Two Ψ) :=
  ws_ct B Z w hws ht hw

theorem blk_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {l : List Instr} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block l) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (.block l) s (Ψ x)) : RelCT isa (Two Φ) (.block l) (Two Ψ) :=
  two_piece [.x0] (pins_ws B Z w hws) ht hw

theorem mm_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) (M : Mont) {o a b : Nat} (hu : MmUse o a b)
    (hw : ∀ x s, Φ x s → WP isa (M.mm o a b) s (Ψ x)) : RelCT isa (Two Φ) (M.mm o a b) (Two Ψ) :=
  two_post (two_map (fun x => (⟨B x, Z x, w x⟩ : VG.Proof.Bignum.AArch64.Ws)) (fun x s h => ⟨_, (hws x s h).good⟩)
    (M.ct hu)) hw

/-! ## The squarings -/

/-- In a squaring: the constants, the counter `k` and the masks `done` and
`ok`, and `Y < n` if `hy`. -/
def SQ (hy : Bool) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t k : Nat) (done ok : Bool), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    k < 64 * (wk p.k + (p.el + 7) / 8) ∧ word s.mem p.B (8 * sC1) = BitVec.ofNat 64 k ∧
    word s.mem p.B (8 * sC2) = mask done ∧ word s.mem p.B (8 * sC3) = mask ok ∧
    (hy = true → wv s.mem p.B (slot (wk p.k) aY) (wk p.k) < N)

/-- After the mask of `x = 1`. -/
def SQM (p : RpP) (s : State) : Prop := SQ false p s ∧ ∃ e1, word s.mem p.B (8 * sMask) = mask e1

theorem SQ.ws {hy : Bool} {p : RpP} {s : State} (h : SQ hy p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, _, _, _, hc, -⟩ := h
  exact hc.ws

/-- `SQ` after a piece that keeps the constants, `sC1`–`sC3`, and `Y` if
`hy`. -/
theorem SQ.step {hy : Bool} {p : RpP} {s u : State} (h : SQ hy p s) {js hs : List Nat}
    (hf : Frm p.B (rg (wk p.k) js hs) s.mem u.mem) (hjs : ∀ j ∈ cArr, j ∉ js)
    (hhs : ∀ i ∈ hs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT)
    (hc : ∀ i ∈ hs, i ≠ sC1 ∧ i ≠ sC2 ∧ i ≠ sC3) (hY : hy = true → aY ∉ js)
    {regs : List Reg} (k : Keep regs s u) (hr : .x0 ∉ regs) : SQ hy p u := by
  obtain ⟨minv, N, r, t, kk, done, ok, hcs, hk, h1, h2, h3, hyl⟩ := h
  have hZ16 := hcs.hZ16
  have h32 : ∀ i ∈ hs, i < 32 := fun i hi => by
    have := (hhs i hi).1; simp only [rSlot, Bool.or_eq_true, beq_iff_eq] at this; omega
  have hw : ∀ i, i < 32 → i ∉ hs → word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi hn =>
    hf.rg_word hi hn
  refine ⟨minv, N, r, t, kk, done, ok, hcs.congr hf hjs hhs k hr, hk, ?_, ?_, ?_, fun e => ?_⟩
  · rw [hw _ (by decide) fun hm => (hc _ hm).1 rfl]; exact h1
  · rw [hw _ (by decide) fun hm => (hc _ hm).2.1 rfl]; exact h2
  · rw [hw _ (by decide) fun hm => (hc _ hm).2.2 rfl]; exact h3
  · rw [hf.rg_wv hZ16 h32 (by decide) (hY e) (by omega)]; exact hyl e

/-- `selLoop`'s and `sqNext`'s registers after `sqLogic`. -/
def sqVal (p : RpP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wk p.k) aX)
  | .x17 => off p.B (slot (wk p.k) aY)
  | .x14 => BitVec.ofNat 64 (wk p.k)
  | _ => 0

/-- The masks, `y := x` if the squarings continue, and `k += 1`. -/
theorem sqTail_ct : RelCT isa (Two SQM)
    (seqs [.block sqLogic, VG.Impl.Rsa.AArch64.Crt.selLoop, .block sqNext]) fun _ _ => True := by
  simp only [seqs]
  refine (pin_ct (Ψ := fun _ _ => True) [.x0] [.x0, .x16, .x17, .x14] sqVal
    (pins_ws RpP.B RpP.Z (fun p => wk p.k) fun _ _ h => h.1.ws)
    (by taint_decide) (fun p s h => ?_) (by taint_decide) fun p s h => ?_).mono (fun _ _ h => h)
      fun _ _ _ => trivial
  · obtain ⟨⟨minv, N, r, t, k, done, ok, hc, hk, h1, h2, h3, -⟩, e1, hm⟩ := h
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    rw [sqLogic_eq]
    refine WP.block_append_iff.mpr (WP.mono (sqMasks_ok hc.ws (k := k) (t := t) (done := done) (ok := ok)
      (by omega) (by have := hc.t2; omega) h1 hc.ht h2 h3 hm rfl) fun u₆ ⟨⟨_, m₆⟩, k₆⟩ => ?_)
    have h256 := hc.ws.h256
    have hf₆ : Frm p.B (rg (wk p.k) [] [sC2, sC3]) s.mem u₆.mem := by
      rw [m₆]
      exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
        (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
          (by decide))
    have hw₆ := hc.ws.congrG hf₆ (by decide) k₆ (by decide)
    refine WP.mono (bases2w_ok hw₆ aX aY) fun u₇ ⟨⟨h16, h17, h14, _⟩, k₇⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (k₇.gpr .x0 (by decide)).trans hw₆.x0
    · exact h16
    · exact h17
    · exact h14
  · obtain ⟨⟨minv, N, r, t, k, done, ok, hc, hk, h1, h2, h3, -⟩, e1, hm⟩ := h
    have he2 := hc.e2
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have h256 := hc.ws.h256
    have hZ16 := hc.hZ16
    rw [sqLogic_eq]
    refine WP.seq (WP.block_append_iff.mpr (WP.mono (sqMasks_ok hc.ws (k := k) (t := t) (done := done) (ok := ok)
      (by omega) (by have := hc.t2; omega) h1 hc.ht h2 h3 hm rfl) fun u₆ ⟨⟨h15₆, m₆⟩, k₆⟩ => ?_))
    have hf₆ : Frm p.B (rg (wk p.k) [] [sC2, sC3]) s.mem u₆.mem := by
      rw [m₆]
      exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
        (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
          (by decide))
    have hc₆ := hc.congr hf₆ (by decide) (by decide) k₆ (by decide)
    refine WP.mono (bases2w_ok hc₆.ws aX aY) fun u₇ ⟨⟨h16, h17, h14, m₇⟩, k₇⟩ => ?_
    have hc₇ := hc₆.congr (js := []) (hs := []) (by rw [m₇]; exact Frm.refl _ _ _) (by simp) (by simp) k₇
      (by decide)
    have h15₇ : u₇.gpr .x15 = _ := (k₇.gpr .x15 (by decide)).trans h15₆
    have sY := hc₇.ws.sl (j := aY) (by decide)
    have sX := hc₇.ws.sl (j := aX) (by decide)
    refine WP.seq (WP.mono (selLoop_ok hc₇.ws.scr h16 h17 h14 h15₇ (by omega) (by omega) (by omega) (by omega)
      (by have := slot_sep (w := wk p.k) (show aY ≠ aX by decide); omega)) fun u₈ ⟨_, o₈, k₈⟩ => ?_)
    have hf₈ : Frm p.B (rg (wk p.k) [aY] []) u₇.mem u₈.mem := Frm.rg_of_out o₈ (by omega) _ _ (by decide)
    have hc₈ := hc₇.congr hf₈ (by decide) (by simp) k₈ (by decide)
    have hc1₈ : word u₈.mem p.B (8 * sC1) = BitVec.ofNat 64 k := by
      rw [hf₈.rg_word (by decide) (by simp), m₇, hf₆.rg_word (by decide) (by decide)]; exact h1
    exact WP.mono (sqNext_ok hc₈.ws hc₈.hel (by omega) hc1₈ hk) fun _ _ => trivial

/-- A squaring leaks the same in runs that agree on the public data. -/
theorem sqBody_ct (M : Mont) : RelCT isa (Two (SQ true)) (sqBody M.mm) fun _ _ => True := by
  have hB : ∀ (hy : Bool) p s, SQ hy p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  rw [show sqBody M.mm = seqs ([copyA aX aY, M.mm aX aX aY] ++ (eqA aX aO ++
    ([.block (zeroMask ++ [sth .x15 sMask])] ++ (eqA aX aNg ++
      [.block sqLogic, VG.Impl.Rsa.AArch64.Crt.selLoop, .block sqNext])))) by
      simp only [sqBody, List.append_assoc]]
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two (SQ false)) ?_ ?_)
  · simp only [seqs]
    refine RelCT.seq (R := Two (SQ true)) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB true) (by taint_decide)
      fun p s h => ?_) (mm_gct RpP.B RpP.Z (fun p => wk p.k) (hB true) M (by unfold MmUse; decide) fun p s h => ?_)
    · have hw := h.ws
      exact WP.mono (copyA_ok hw (o := aX) (a := aY) (by decide) (by decide) (by decide)) fun u ⟨_, o, _, _, k⟩ =>
        h.step (Frm.rg_of_out o (by omega) [aX] [] (by decide)) (by decide) (by simp) (by simp) (by decide) k
          (by decide)
    · obtain ⟨minv, N, r, t, kk, done, ok, hc, hk, h1, h2, h3, hyl⟩ := h
      have hg := hc.good
      have hw2 := hc.ws.w2
      exact WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aX) (a := aX) (b := aY) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
        (by rw [hc.hn]; exact hyl rfl)) fun u ⟨_, _, _, ha, k⟩ =>
        (show SQ false p s from ⟨minv, N, r, t, kk, done, ok, hc, hk, h1, h2, h3, fun e => by cases e⟩).step
          (Frm.rg_of_arrays ha [aX, aAcc, aTmp] [] (by decide)) (by decide) (by simp) (by simp) (by simp) k
          (by decide)
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two (SQ false))
    (eqA_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) (by taint_decide) fun p s h => ?_) ?_)
  · exact WP.mono (eqA_ok h.ws (a := aX) (b := aO) (by decide) (by decide)) fun u ⟨_, m, _, _, k⟩ =>
      h.step (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) (by simp) (by simp) k
        (by decide)
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two SQM) ?_ ?_)
  · simp only [seqs]
    refine blk_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) (by taint_decide) fun p s h => ?_
    have h256 := h.ws.h256
    have hn := h.ws.scr.nowrap
    refine WP.mono (zstore_ok h.ws (i := sMask) (by decide) (by decide)) fun u ⟨⟨_, m⟩, k⟩ =>
      ⟨?_, decide (s.gpr .x9 = 0), ?_⟩
    · exact h.step (js := []) (Frm.rg_of_hdr (m ▸ writeW_outside _ _ _ (by simp only [sMask, sFn]; omega))
        [] [sMask] (List.mem_singleton_self _)) (by decide) (by decide) (by decide) (by simp) k (by decide)
    · rw [m, word_writeW_self]
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two SQM)
    (eqA_gct RpP.B RpP.Z (fun p => wk p.k) (fun p s h => h.1.ws) (by taint_decide) fun p s h => ?_) sqTail_ct)
  obtain ⟨h, e1, hm⟩ := h
  exact WP.mono (eqA_ok h.ws (a := aX) (b := aNg) (by decide) (by decide)) fun u ⟨_, m, _, _, k⟩ =>
    ⟨h.step (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) (by simp) (by simp) k
      (by decide), e1, by rw [m]; exact hm⟩

/-- The squarings' invariant: `k` squarings from `t₀`. -/
def SQI (p : RpP) (k : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t : Nat) (st₀ : Nat × Bool × Bool),
    Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧ SqI t₀ p.B (wk p.k) N t st₀ k u

/-- The squarings: `64 Bw` of them. -/
theorem sqLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < 64 * (wk p.k + (p.el + 7) / 8) ∧ SQI p 0 s)
    (.loop (sqBody M.mm) (.nonzero .x .x3)) (Two fun p s => SQI p (64 * (wk p.k + (p.el + 7) / 8)) s) :=
  two_loop (fun p => 64 * (wk p.k + (p.el + 7) / 8))
    (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨hk, t₀, minv, N, r, t, st₀, hc, hI⟩ := hq
      have hcu := hc.congr hI.frm (by decide) sq_hs hI.keep (by decide)
      have hN : 0 < N := by have := hc.n1; omega
      exact ⟨minv, N, r, t, q.2, _, _, hcu, hk, hI.c1, hI.c2, hI.c3, fun _ => by
        rw [hI.y]; exact Nat.mod_lt _ hN⟩) (sqBody_ct M))
    fun p k s hk ⟨t₀, minv, N, r, t, st₀, hc, hI⟩ =>
      WP.mono (sqBody_ok M hc hk hI) fun s' ⟨hI', hz⟩ =>
        ⟨by rw [eval_nonzero, ne_zero_iff]; exact congrArg some (decide_eq_decide.mpr (by rw [hz]; omega)),
          fun _ => ⟨t₀, minv, N, r, t, st₀, hc, hI'⟩, fun e => e ▸ ⟨t₀, minv, N, r, t, st₀, hc, hI'⟩⟩

end Rp

end VG.Proof.Rsa.AArch64
