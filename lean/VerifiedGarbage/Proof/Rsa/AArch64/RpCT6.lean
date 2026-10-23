module

public import VerifiedGarbage.Proof.Rsa.AArch64.RpCT5
public import VerifiedGarbage.Proof.Rsa.AArch64.RpCands
public import VerifiedGarbage.Proof.Rsa.AArch64.RpCT3
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Rsa.AArch64.RpCT4
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpCT5
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpCands
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpCT3
meta import VerifiedGarbage.Proof.Rsa.RecoverTries
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes` on AArch64: constant time, the candidates

A candidate leaks the same in runs whose working spaces agree
(`candBody_ct`); the candidates tried are the public number of tries
(`candLoop_ct`): the loop stops after candidate `j` iff `j + 1` is that
number (`cand_cond`, `RecoverTries.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)
open VG.Proof.Rsa (pqOf go_le cand_cond)

namespace Rp

/-! ## A candidate -/

/-- At a candidate's start: the constants, and the candidate `c < 100`. -/
def CA (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t c : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    word s.mem p.B (8 * sCand) = BitVec.ofNat 64 c ∧ c < 100

/-- The constants. -/
def CK (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t

theorem CK.ws {p : RpP} {s : State} (h : CK p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, hc⟩ := h
  exact hc.ws

/-- After `gBlk`. -/
def CG (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    s.gpr .x12 = BitVec.ofNat 64 (wk p.k) ∧ s.gpr .x13 = BitVec.ofNat 64 0

/-- After `g R mod n` in `Xm` (`hg`), then copied to `G`. -/
def CX (j : Nat) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t g : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (slot (wk p.k) j) (wk p.k) < N ∧
    wv s.mem p.B (slot (wk p.k) j) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N

/-- `setWord`'s registers after its load. -/
def swXVal (p : RpP) : Reg → BitVec 64
  | .x8 => off p.B (slot (wk p.k) aX)
  | .x12 => BitVec.ofNat 64 (wk p.k)
  | .x13 => BitVec.ofNat 64 0
  | _ => 0

theorem setX_ct : RelCT isa (Two CG) (setWord aX) (Two CK) := by
  unfold setWord
  refine pin_ct [.x0, .x12, .x13] [.x8, .x12, .x13] swXVal (fun _ _ _ h₁ h₂ r hr => ?_) (by taint_decide)
    (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · obtain ⟨_, _, _, _, hc₁, a₁, b₁⟩ := h₁
    obtain ⟨_, _, _, _, hc₂, a₂, b₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hc₁.ws.x0, hc₂.ws.x0]
    · rw [a₁, a₂]
    · rw [b₁, b₂]
  · obtain ⟨_, _, _, _, hc, h12, h13⟩ := h
    have hw := hc.ws
    have := hw.h256
    have hl : InRegions (s.rd ++ s.wr) (off p.B (8 * sArr aX)) 8 :=
      hw.scr.ld (by have := hw.hZ; have := hdr_lt_slot (wk p.k) 16 (show sArr aX < 32 by decide); omega)
    refine WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off p.B (slot (wk p.k) aX)) (by
      brun [hw.x0, hdr_enc (show sArr aX < 32 by decide), hl, hw.harr aX (by decide)])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨h8, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h8
    · exact (k.gpr .x12 (by decide)).trans h12
    · exact (k.gpr .x13 (by decide)).trans h13
  · obtain ⟨minv, N, r, t, hc, h12, h13⟩ := h
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have hg := hc.good
    refine WP.mono (setWord_ok hc.ws.scr hc.ws.x0 hg.1.hdr hg.2 h12 (by omega) (o := aX) (by decide)
      (i := 0) (by omega) h13) fun u ⟨_, o, k⟩ => ?_
    exact ⟨minv, N, r, t, hc.congr (Frm.rg_of_out o (Nat.le_refl _) [aX] [] (by decide)) (by decide) (by simp) k
      (by decide)⟩

/-- `g`, `g R mod n`, its copy and `Y = R mod n`. -/
theorem candPre_ct (M : Mont) : RelCT isa (Two CA)
    (seqs [.block gBlk, setWord aX, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO])
    fun _ _ => True := by
  have hK : ∀ p s, CK p s → Ws s p.B p.Z (wk p.k) := fun _ _ h => h.ws
  have hX : ∀ j p s, CX j p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws
  simp only [seqs]
  refine RelCT.seq (R := Two CG) (blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨minv, N, r, t, c, hc, hcand, -⟩ := h
    exact WP.mono (gBlk_ok hc.ws hcand) fun u ⟨⟨_, h13, h12, m⟩, k⟩ =>
      ⟨minv, N, r, t, hc.congr (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k
        (by decide), h12, h13⟩
  refine RelCT.seq setX_ct (RelCT.seq (R := Two (CX aXm)) (mm_gct RpP.B RpP.Z (fun p => wk p.k) hK M
    (o := aXm) (a := aX) (b := aR2) (by unfold MmUse; decide) fun p s h => ?_) ?_)
  · obtain ⟨minv, N, r, t, hc⟩ := h
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aXm) (a := aX) (b := aR2) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hc.hr2lt)) fun u ⟨_, hlt, hm, ha, k⟩ => ?_
    rw [hc.hn] at hlt hm
    exact ⟨minv, N, r, t, _, hc.congr (Frm.rg_of_arrays ha [aXm, aAcc, aTmp] [] (by decide)) (by decide) (by simp)
      k (by decide), hlt, VG.Proof.Rsa.g_mont hc.coprime hc.hr2 hm⟩
  refine RelCT.seq (R := Two (CX aG)) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hX aXm) (by taint_decide)
    fun p s h => ?_) ((copyA_gct (Ψ := EX fun _ => True) RpP.B RpP.Z (fun p => wk p.k) (hX aG) (by taint_decide)
      fun p s h => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial)
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aG) (a := aXm) (by decide) (by decide) (by decide))
      fun u ⟨hv, o, _, _, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aG] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hv]; exact hlt,
      by rw [hv]; exact hm⟩
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aY) (a := aO) (by decide) (by decide) (by decide))
      fun u ⟨hv, o, _, _, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aY] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    have hG : wv u.mem p.B (slot (wk p.k) aG) (wk p.k) = wv s.mem p.B (slot (wk p.k) aG) (wk p.k) :=
      hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hG]; exact hlt,
      by rw [hG]; exact hm, by rw [hv, hc.ho], trivial⟩

/-- Before `expSel`: `G ≡ g R` for the candidate `g = q.2 + 2`, whose number
`q.2` is in `sCand`, and `Y = R mod n`. -/
def EXq (q : RpP × Nat) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s q.1.B q.1.Z (wk q.1.k) minv N q.1.el r t ∧
    wv s.mem q.1.B (slot (wk q.1.k) aG) (wk q.1.k) < N ∧
    wv s.mem q.1.B (slot (wk q.1.k) aG) (wk q.1.k) % N = (q.2 + 2) * 2 ^ (64 * wk q.1.k) % N ∧
    wv s.mem q.1.B (slot (wk q.1.k) aY) (wk q.1.k) = 2 ^ (64 * wk q.1.k) % N ∧
    word s.mem q.1.B (8 * sCand) = BitVec.ofNat 64 q.2 ∧ q.2 < 100

theorem EXq.ws {q : RpP × Nat} {s : State} (h : EXq q s) : Ws s q.1.B q.1.Z (wk q.1.k) := by
  obtain ⟨_, _, _, _, hc, -⟩ := h
  exact hc.ws

theorem EXq.cand {q : RpP × Nat} {s : State} (h : EXq q s) : word s.mem q.1.B (8 * sCand) = BitVec.ofNat 64 q.2 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcand, _⟩ := h
  exact hcand

theorem EXq.lt {q : RpP × Nat} {s : State} (h : EXq q s) : q.2 < 100 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h100⟩ := h
  exact h100

theorem EXq.ex {q : RpP × Nat} {s : State} (h : EXq q s) {G : Nat → Prop} (hG : G (q.2 + 2)) : EX G q.1 s := by
  obtain ⟨minv, N, r, t, hc, hlt, hm, hY, -⟩ := h
  exact ⟨minv, N, r, t, q.2 + 2, hc, hlt, hm, hY, hG⟩

/-- `EXq` after a block that writes only `x3`. -/
theorem EXq.x3 {q : RpP × Nat} {s u : State} (h : EXq q s) (m : u.mem = s.mem) (k : Keep [.x3] s u) : EXq q u := by
  obtain ⟨minv, N, r, t, hc, hlt, hm, hY, hcand, h100⟩ := h
  exact ⟨minv, N, r, t, hc.congr (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k
    (by decide), by rw [m]; exact hlt, by rw [m]; exact hm, by rw [m]; exact hY, by rw [m]; exact hcand, h100⟩

/-- `expSel` leaks the same in runs that agree on the public data and on the
candidate's number. -/
theorem expSel_ct (M : Mont) : RelCT isa (Two EXq) (expSel M.mm) fun _ _ => True := by
  have hpin : ∀ (Φ : RpP × Nat → State → Prop), (∀ q s, Φ q s → EXq q s) → Pins Φ [.x0] := fun Φ hΦ =>
    pins_ws (fun q => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k) fun q s h => (hΦ q s h).ws
  unfold expSel
  refine RelCT.seq (R := Two fun q s => EXq q s ∧ s.gpr .x3 = BitVec.ofNat 64 q.2)
    (two_piece [.x0] (hpin EXq fun _ _ h => h) (by taint_decide) fun q s h => ?_) ?_
  · exact WP.mono (candNum_ok h.ws h.cand) fun u ⟨⟨h3, m⟩, k⟩ => ⟨h.x3 m k, h3⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · refine two_map (fun q => q.1) (fun q s hh => ?_) ((expLoopWith_ct (bitSmall_two_code M)).mono
      (fun _ _ h => h) fun _ _ _ => trivial)
    obtain ⟨⟨h, h3⟩, he⟩ := hh
    have h100 := h.lt
    rw [eval_zero, h3, ofNat_beq_zero (by omega)] at he
    have h0 : q.2 = 0 := by simpa using he
    exact h.ex (G := (· = 2)) (by omega)
  refine RelCT.seq (R := Two fun q s => (EXq q s ∧ q.2 ≠ 0) ∧ s.gpr .x3 = BitVec.ofNat 64 q.2 - 1#64)
    (two_piece [.x0] (hpin _ fun _ _ h => h.1.1) (by taint_decide) fun q s hh => ?_) ?_
  · obtain ⟨⟨h, h3⟩, he⟩ := hh
    have h100 := h.lt
    rw [eval_zero, h3, ofNat_beq_zero (by omega)] at he
    have h0 : q.2 ≠ 0 := by simpa using he
    exact WP.mono (candNum1_ok h.ws h.cand) fun u ⟨⟨h3', m⟩, k⟩ => ⟨⟨h.x3 m k, h0⟩, h3'⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · refine two_map (fun q => q.1) (fun q s hh => ?_) ((expLoopWith_ct (bitSmall_three_code M)).mono
      (fun _ _ h => h) fun _ _ _ => trivial)
    obtain ⟨⟨⟨h, _⟩, h3⟩, he⟩ := hh
    have h100 := h.lt
    rw [eval_zero, h3, ofNat_sub_one_beq_zero (by omega)] at he
    have h1 : q.2 = 1 := by simpa using he
    exact h.ex (G := (· = 3)) (by omega)
  · exact two_map (fun q => q.1) (fun q s hh => hh.1.1.1.ex (G := fun _ => True) trivial)
      ((expLoop_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)

/-- At a candidate's start, with its number `q.2`. -/
def CAq (q : RpP × Nat) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s q.1.B q.1.Z (wk q.1.k) minv N q.1.el r t ∧
    word s.mem q.1.B (8 * sCand) = BitVec.ofNat 64 q.2 ∧ q.2 < 100

/-- `g`, `g R mod n`, its copy and `Y = R mod n`, and the exponentiation. -/
theorem candA_ct (M : Mont) : RelCT isa (Two CAq)
    (seqs [.block gBlk, setWord aX, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO, expSel M.mm])
    fun _ _ => True := by
  rw [show [.block gBlk, setWord aX, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO, expSel M.mm] =
    [.block gBlk, setWord aX, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO] ++ [expSel M.mm] from rfl]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two EXq) (two_post (two_map (fun q => q.1)
    (fun q s ⟨minv, N, r, t, hc, hcand, h100⟩ => ⟨minv, N, r, t, q.2, hc, hcand, h100⟩) (candPre_ct M))
    fun q s ⟨minv, N, r, t, hc, hcand, h100⟩ => ?_) (expSel_ct M))
  have hZ16 := hc.hZ16
  refine WP.mono (candPre_ok M hc hcand h100) fun u ⟨hf, k, hlt, hm, hY⟩ =>
    ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, hm, hY, ?_, h100⟩
  rw [hf.rg_word (by decide) (by simp)]; exact hcand

/-- The checks of `y = ±1` and the start of the squarings. -/
theorem candB_ct : RelCT isa (Two CK) (seqs (eqA aY aO ++ (([.block (zeroMask ++ [sth .x15 sC2])] :
    List (Prog isa)) ++ (eqA aY aNg ++ ([.block chkBlk] : List (Prog isa)))))) fun _ _ => True := by
  have hK : ∀ p s, CK p s → Ws s p.B p.Z (wk p.k) := fun _ _ h => h.ws
  have same : ∀ p s u, CK p s → u.mem = s.mem → ∀ {regs : List Reg}, Keep regs s u → .x0 ∉ regs → CK p u :=
    fun p s u ⟨minv, N, r, t, hc⟩ m _ k hr => ⟨minv, N, r, t, hc.congr (js := []) (hs := [])
      (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k hr⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two CK) (eqA_gct RpP.B RpP.Z
    (fun p => wk p.k) hK (by taint_decide) fun p s h => WP.mono (eqA_ok h.ws (a := aY) (b := aO) (by decide)
      (by decide)) fun u ⟨_, m, _, _, k⟩ => same p s u h m k (by decide)) ?_)
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two CK) ?_ ?_)
  · simp only [seqs]
    refine blk_gct RpP.B RpP.Z (fun p => wk p.k) hK (by taint_decide) fun p s h => ?_
    obtain ⟨minv, N, r, t, hc⟩ := h
    have h256 := hc.ws.h256
    have hn := hc.ws.scr.nowrap
    exact WP.mono (zstore_ok hc.ws (i := sC2) (by decide) (by decide)) fun u ⟨⟨_, m⟩, k⟩ =>
      ⟨minv, N, r, t, hc.congr (js := []) (Frm.rg_of_hdr (m ▸ writeW_outside _ _ _ (by simp only [sC2, sFn]; omega))
        [] [sC2] (List.mem_singleton_self _)) (by decide) (by decide) k (by decide)⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two CK) (eqA_gct RpP.B RpP.Z
    (fun p => wk p.k) hK (by taint_decide) fun p s h => WP.mono (eqA_ok h.ws (a := aY) (b := aNg) (by decide)
      (by decide)) fun u ⟨_, m, _, _, k⟩ => same p s u h m k (by decide)) ?_)
  simp only [seqs]
  exact two_taint [.x0] (pins_ws RpP.B RpP.Z (fun p => wk p.k) hK) (by taint_decide)

/-- After a candidate's exponentiation: `Y ≡ y R` for some `y < n`. -/
def CY (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t y : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = y * 2 ^ (64 * wk p.k) % N ∧ y < N

/-- A candidate leaks the same in runs that agree on the public data and on
the candidate's number. -/
theorem candBody_ct (M : Mont) : RelCT isa (Two CAq) (candBody M.mm) fun _ _ => True := by
  rw [show candBody M.mm = seqs ([.block gBlk, setWord aX, M.mm aXm aX aR2, copyA aG aXm, copyA aY aO,
      expSel M.mm] ++ ((eqA aY aO ++ ([.block (zeroMask ++ [sth .x15 sC2])] ++ (eqA aY aNg ++
        [.block chkBlk]))) ++ [.loop (sqBody M.mm) (.nonzero .x .x3), .block candNext])) by
    simp only [candBody, List.append_assoc, List.cons_append, List.nil_append]]
  refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two fun (q : RpP × Nat) s => CY q.1 s)
    (two_post (candA_ct M) fun q s ⟨minv, N, r, t, hc, hcand, hc100⟩ => ?_)
    (two_map (Φ' := CY) (fun q => q.1) (fun _ _ h => h) ?_))
  · have hN : 0 < N := by have := hc.n1; omega
    exact WP.mono (candA_ok M hc hcand hc100) fun u ⟨hf, k, hY⟩ =>
      ⟨minv, N, r, t, _, hc.congr hf (by decide) (by decide) k (by decide), hY,
        by rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hN⟩
  refine RelCT.seqs_append (by simp [eqA]) (by simp) (RelCT.seq (R := Two fun p s =>
      0 < 64 * (wk p.k + (p.el + 7) / 8) ∧ SQI p 0 s)
    (two_post (two_map id (fun _ _ ⟨minv, N, r, t, _, hc, _⟩ => ⟨minv, N, r, t, hc⟩) candB_ct)
      fun p s h => ?_) ?_)
  · obtain ⟨minv, N, r, t, y, hc, hY, hy⟩ := h
    have hZ16 := hc.hZ16
    have hw1 := hc.ws.w1
    refine WP.mono (candB_ok hc hY hy) fun u ⟨hf, k, hc2, hc3, hc1⟩ => ⟨by omega, ?_⟩
    have hc₂ := hc.congr hf (by decide) (by decide) k (by decide)
    refine ⟨u, minv, N, r, t, VG.Proof.Rsa.sqStart N y, hc₂, Frm.refl _ _ _, Keep.refl _ _, ?_, hy, hc1, hc2, hc3⟩
    rw [hf.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hY
  show RelCT isa _ (.seq (.loop (sqBody M.mm) (.nonzero .x .x3)) (.block candNext)) _
  exact RelCT.seq (sqLoop_ct M) (two_taint [.x0] (fun _ _ _ ⟨_, _, _, _, _, _, hc₁, hI₁⟩
    ⟨_, _, _, _, _, _, hc₂, hI₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [(hc₁.congr hI₁.frm (by decide) sq_hs hI₁.keep (by decide)).ws.x0,
        (hc₂.congr hI₂.frm (by decide) sq_hs hI₂.keep (by decide)).ws.x0]) (by taint_decide))

/-! ## The candidates -/

/-- The candidates' invariant: `j` tried from `s₀`, and the public count. -/
def CL (p : RpP) (j : Nat) (u : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (N r t : Nat), Cst s₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    p.cnt = (recoverPrimes.go N t r recoverTries).2 ∧ CandI s₀ p.B (wk p.k) N t r j u

theorem candLoopL_ct (M : Mont) : RelCT isa (Two fun p s => 0 < p.cnt ∧ CL p 0 s)
    (.loop (candBody M.mm) (.nonzero .x .x15)) (Two fun (_ : RpP) (_ : State) => True) :=
  two_loop RpP.cnt ((candBody_ct M).mono (fun _ _ h => two_mono (fun q s hq => by
      obtain ⟨hj, s₀, minv, N, r, t, hc, hcnt, hI⟩ := hq
      have := go_le N t r recoverTries (Nat.le_refl _)
      exact ⟨minv, N, r, t, hc.congr hI.frm (by decide) cand_hs hI.keep (by decide), hI.cand,
        by have : recoverTries = 100 := rfl; omega⟩) h) fun _ _ h => h)
    fun p j s hj ⟨s₀, minv, N, r, t, hc, hcnt, hI⟩ => by
      have hle := go_le N t r recoverTries (Nat.le_refl _)
      have hj100 : j < 100 := by have : recoverTries = 100 := rfl; omega
      have hcu := hc.congr hI.frm (by decide) cand_hs hI.keep (by decide)
      refine WP.mono (candBody_ok M hcu hI.cand hj100) fun u' ⟨h15, hf, k, hcand, _, _⟩ => ⟨?_, fun hlt => ?_,
        fun _ => trivial⟩
      · rw [hcnt] at hj ⊢
        rw [eval_mask u' h15]
        have := cand_cond N t r hj hI.go
        simp only [Bool.not_not] at this
        rw [this]
      · refine ⟨s₀, minv, N, r, t, hc, hcnt, (hI.frm.rg_trans hf).rg_mono (by decide) (by decide),
          (hI.keep.trans k).mono (by decide), hcand, ?_⟩
        rw [hI.go, VG.Proof.Rsa.go_eq N t r hj100]
        rw [hcnt, hI.go, VG.Proof.Rsa.go_eq N t r hj100] at hlt
        cases hs : recoverStep N t r (j + 2) with
        | some y => rw [hs] at hlt; exact absurd hlt (by simp)
        | none => rfl

/-- The public count is `recoverPrimes.go`'s, once `d e` passes step 1. -/
theorem cnt_eq {I : RpIn} (hv : Spec.Rsa.modulusValid I.N I.k = true) (L : RpLens I) (hm0 : 0 < I.D * I.E - 1)
    (heven : (I.D * I.E - 1) % 2 = 0) :
    I.pub.cnt = (recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2
      recoverTries).2 := by
  have h1 : ¬(I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1) := by omega
  show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = _
  simp only [Spec.Rsa.primesKey, L.nbl, hv, ite_true]
  rw [← VG.Proof.Rsa.recoverPrimes_go h1]
  split <;> simp_all

/-- After the candidates: `recoverPrimes.go`'s result, and what the factors
need. -/
def GR3 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem) (minv : BitVec 64) (res : Option Nat) (cnt : Nat), I.pub = p ∧ RpS I m₀ s ∧
    RpLens I ∧ RpOuts I ∧ Spec.Rsa.modulusValid I.N I.k = true ∧
    Cst s I.B I.Z (wk I.k) minv I.N I.el (splitTwos (I.D * I.E - 1)).2 (splitTwos (I.D * I.E - 1)).1 ∧
    recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2 recoverTries =
      (res.map (pqOf I.N), cnt) ∧ word s.mem I.B (8 * sC3) = mask res.isSome ∧
    (∀ y, res = some y → wv s.mem I.B (slot (wk I.k) aY) (wk I.k) = y * 2 ^ (64 * wk I.k) % I.N ∧ y < I.N ∧
      y * y % I.N = 1)

theorem candLoop_ct (M : Mont) : RelCT isa (Two GR2) (candLoop M.mm) (Two GR3) := by
  refine two_post (RelCT.seq (blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, e, S, _⟩ => e ▸ S.ws) (by taint_decide) fun p s h => ?_)
      ((candLoopL_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun p s h => ?_
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    dsimp only [RpIn.pub]
    have h256 := hc.ws.h256
    have hn := hc.ws.scr.nowrap
    refine WP.mono (WP.keep [.x3] (Q := fun u => u.mem = s.mem.writeW (off I.B (8 * sCand))
        (BitVec.ofNat 64 0)) (by
      brun [hc.ws.x0, hdr_enc (show sCand < 32 by decide),
        hc.ws.scr.st (d := 8 * sCand) (by simp only [sCand, sFn]; omega)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun u ⟨m₁, k₁⟩ =>
        ⟨?_, s, _, I.N, _, _, hc, cnt_eq hv L hm0 heven, ?_, k₁.mono (by decide), by rw [m₁, word_writeW_self], rfl⟩
    · rw [show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = I.pub.cnt from rfl, cnt_eq hv L hm0 heven]
      exact VG.Proof.Rsa.go_pos _ _ _ _ (Nat.le_refl _)
    · rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sCand, sFn]; omega)) _ _ (by decide)
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    exact WP.mono (candLoop_ok M hc) fun u ⟨res, cnt, hgo, _, hc3, hy, hf, k⟩ =>
      ⟨I, m₀, _, res, cnt, rfl, S.step hf (by decide) (by decide) k (by decide), L, O, hv,
        hc.congr hf (by decide) cand_hs k (by decide), hgo, hc3, hy⟩

end Rp

end VG.Proof.Rsa.AArch64
