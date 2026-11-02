module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
public import VerifiedGarbage.Proof.Rsa.AArch64.RdProd
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrt
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdProd
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdSqrt
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, from `a` to `b² - 4 n`

`product_ct`: the products' loop, then `aProd`, `divA`, `divB`, `square`
and `minus4n`, each from and to `GC` with no facts.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- No facts about the public data's state. -/
abbrev XN : DP → State → Prop := fun _ _ => True

/-- The count and a mask in `x15`. -/
def XPm (a : Pub) (s : State) : Prop := XL NT XN a s ∧ MR .x15 s

/-- `setNar` and then the count's decrement. -/
theorem narDec_w : CTW (GC Wk (XL NT XN)) (GC vk (XL' NT XN)) (.block (setNar ++ ([.subImm .x .x6 .x6 1] : List Instr))) :=
  blk (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
    subst e
    rw [WP.block_append_iff]
    exact WP.mono (g.setNar_ok L.1) fun t₁ ⟨g₁, _, k₁⟩ => WP.mono (dec_ok t₁ .x6)
      fun t ⟨⟨h6, hm, _⟩, k₂⟩ => ⟨I, m₀, c, rfl, g₁.same hm k₂ (by decide), L,
        by rw [h6, k₁.gpr .x6 (by decide), x.1], trivial⟩

theorem prodBody_ct {y x a t : Nat} (P : PIdx y x a t) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block (base y .x16 ++ [ld .x3 .x16, movi .x7 0] ++
      oddMask)) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([mov .x14 .x12] ++ base y .x16 ++
      base y .x17)) (countLoop .x14 shrBody)) hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12,
      .adds .x .x3 .x7 .x7] ++ base x .x10 ++ base a .x8 ++ base t .x5)) (countLoop .x14 addMBody)) hc₃).isSome
      = true)
    {hc₄ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₄ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base t .x16 ++ base a .x17)) copyWords)
      hc₄).isSome = true)
    {hc₅ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₅ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12] ++
      base x .x16 ++ c0)) (.seq (countLoop .x14 shlBody) (.block []))) hc₅).isSome = true) :
    CTW (GC vk (XL NT XN)) (GC vk (XL' NT XN)) (prodBody y x a t) := by
  have hx : x < 16 := by have := P.hx; omega
  have ha : a < 16 := by have := P.ha; omega
  unfold prodBody
  refine CTW.cons (by simp) (wsblk (Y := XPm) (rest := base y .x16 ++ [ld .x3 .x16, movi .x7 0] ++ oddMask)
    (by simp only [List.append_assoc]) ht₁
    fun ⟨Q, i⟩ s h => h.elim fun I m₀ c e g L xx => by
      subst e
      exact WP.mono (prodBit_ok g.ws P.hy) fun t ⟨⟨h15, _, hm⟩, k⟩ =>
        ⟨I, m₀, c, rfl, g.same hm k (by decide), L, xx.keep k (by decide) (fun _ => trivial), ⟨_, h15⟩⟩) ?_
  refine CTW.cons (by simp) (halfA_w (Y := XPm) P.hy P.hy (fun _ _ _ h _ k =>
    ⟨h.x.1.keep k (by decide) (fun _ => trivial), h.x.2.keep k (by decide)⟩) ht₂) ?_
  refine CTW.cons (by simp) (setWid_w (Y := XPm) (fun _ _ _ h _ k =>
    ⟨h.x.1.keep k (by decide) (fun _ => trivial), h.x.2.keep k (by decide)⟩)) ?_
  refine CTW.cons (by simp) (addA_w (Y := XL NT XN) P.ht hx ha (Ne.symm P.xt) (Ne.symm P.at') (fun _ _ h => h.x.2)
    (fun _ _ _ h _ k => h.x.1.keep k (by decide) (fun _ => trivial)) ht₃) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XL NT XN) ha P.ht P.at' (fun _ _ _ h _ k =>
    h.x.keep k (by decide) (fun _ => trivial)) ht₄) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XL NT XN) hx (fun _ s _ => cin_c0 s) (fun _ _ _ h _ k _ =>
    h.x.keep k (by decide) (fun _ => trivial)) ht₅) ?_
  exact CTW.one narDec_w

theorem countN_w : CTW (GC vk XT) (GC vk fun a s => s.gpr .x6 = BitVec.ofNat 64 (NT a.1) ∧ XN a.1 s)
    (.block countN) :=
  wsblk (rws_drop (by simp [countN, ws])) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    exact WP.mono (countN_ok g.ws) fun t ⟨⟨h6, hm⟩, k⟩ => ⟨I, m₀, c, rfl, g.same hm k (by decide), L, h6, trivial⟩

theorem product_ct {y x a t : Nat} (P : PIdx y x a t) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block (base y .x16 ++ [ld .x3 .x16, movi .x7 0] ++
      oddMask)) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([mov .x14 .x12] ++ base y .x16 ++
      base y .x17)) (countLoop .x14 shrBody)) hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12,
      .adds .x .x3 .x7 .x7] ++ base x .x10 ++ base a .x8 ++ base t .x5)) (countLoop .x14 addMBody)) hc₃).isSome
      = true)
    {hc₄ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₄ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base t .x16 ++ base a .x17)) copyWords)
      hc₄).isSome = true)
    {hc₅ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₅ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x7 0, mov .x14 .x12] ++
      base x .x16 ++ c0)) (.seq (countLoop .x14 shlBody) (.block []))) hc₅).isSome = true) :
    CTW (GC vk XT) (GC vk XT) (product y x a t) :=
  (countN_w.seq (loop_w NT NT_ok (prodBody_ct P ht₁ ht₂ ht₃ ht₄ ht₅))).mono (fun _ _ h => h) fun _ _ h =>
    h.imp rfl fun _ => trivial

theorem aProd_ct : CTW (GC vk XT) (GC vk XT) aProd := by
  unfold aProd
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
  exact CTW.one (product_ct pidxA (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide))

/-- `m < n`, and'ed into the mask. -/
theorem cmpTail_w : CTW (GC Wk XT) (GC Wk XT) (seqs [.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++
    base wA .x16 ++ base wN .x17), cmpLoop, .block (borrowMask ++ andMask)]) :=
  wsop (rest := [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base wA .x16 ++ base wN .x17)
    (body := .seq cmpLoop (.block (borrowMask ++ andMask)))
    (by simp only [seqs, List.append_assoc]) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
    subst e
    have sA := g.ws.sl (j := wA) (by decide)
    have sN := g.ws.sl (j := wN) (by decide)
    have hw1 := g.ws.w1
    have hw2 := g.ws.w2
    simp only [seqs]
    refine WP.seq (WP.mono (cmpSet_ok' g.ws wA wN) fun s₇ ⟨⟨h16, h17, h14, _, _, h7, hc, m₇⟩, k₇⟩ => ?_)
    refine WP.seq (WP.mono (cmpLoop_ok (g.ws.scr.congr k₇.wr) h16 h17 h14 hc (by omega) (by omega) (by omega)
      (by omega)) fun s₈ ⟨_, m₈, k₈⟩ => ?_)
    have g₈ := (g.same m₇ k₇ (by decide)).same m₈ k₈ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (borrowMask_ok s₈ ((k₈.gpr .x7 (by decide)).trans h7)) fun s₉ ⟨⟨h15, m₉, _⟩, k₉⟩ => ?_
    exact WP.mono (andMask_ok (g₈.same m₉ k₉ (by decide)) h15) fun t ⟨gt, _, _⟩ => ⟨I, m₀, _, rfl, gt, L, trivial⟩

theorem divA_ct : CTW (GC vk XT) (GC Wk XT) divA := by
  unfold divA
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (divmod_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intros; trivial) (by taint_decide)
    (by taint_decide)) ?_
  exact cmpTail_w

theorem divB_ct : CTW (GC Wk XT) (GC vk XT) divB := by
  unfold divB
  simp only [List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (blk (w' := vk) (Y := fun _ s => MR .x15 s) (by taint_decide)
    fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
      subst e
      rw [WP.block_append_iff]
      exact WP.mono (g.setNar_ok L.1) fun t₁ ⟨g₁, _, _⟩ => WP.mono (ones_ok t₁) fun t ⟨⟨h15, _, hm⟩, k⟩ =>
        ⟨I, m₀, c, rfl, g₁.same hm k (by decide), L, _, h15⟩) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := fun _ s => MR .x15 s) (by decide)
    (fun _ _ _ h _ k _ => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (addA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => h.x) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (divmod_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intros; trivial) (by taint_decide)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.app (a := eqA nRem nZ) (by simp [eqA]) (by simp) (eqA_w (Y := XT) (by decide) (by decide)
    (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (andZero_w (Y := XT) (by intros; trivial))

theorem square_ct : CTW (GC vk XT) (GC vk XT) square := by
  unfold square
  refine CTW.cons (by simp) (regs_w (Y := fun _ s => MR .x15 s) (by taint_decide) (rs := [.x7, .x15]) (by decide)
    fun a s h => WP.mono (ones_ok s) fun t ⟨⟨h15, _, hm⟩, k⟩ => ⟨⟨hm, _, h15⟩, k⟩) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := fun _ s => MR .x15 s) (by decide)
    (fun _ _ _ h _ k _ => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (addA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => h.x) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial)
    (by taint_decide)) ?_
  exact CTW.one (product_ct pidxS (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide))

theorem minus4n_ct : CTW (GC vk XT) (GC Wk XT) minus4n := by
  unfold minus4n oneA
  simp only [List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XT) (by decide) (fun _ s _ => cin_c0 s) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XT) (by decide) (fun _ s _ => cin_c0 s) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  refine CTW.cons (by simp) (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  exact CTW.one (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial))

end VG.Proof.Rsa.AArch64.Rd
