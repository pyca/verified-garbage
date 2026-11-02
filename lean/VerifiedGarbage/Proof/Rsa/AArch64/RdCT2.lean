module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT1
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT1
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, the first pieces
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- No facts. -/
abbrev XT : Pub → State → Prop := fun _ _ => True

/-- `x15` a mask. -/
def XM (_ : Pub) (s : State) : Prop := ∃ c, s.gpr .x15 = mask c

theorem deMinus_ct : CTW (GC vk XT) (GC Wk XT) deMinus := by
  unfold deMinus oneA
  simp only [List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (setWid_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  refine CTW.cons (by simp) (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XM) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ hm _ => hm) (by taint_decide)) ?_
  exact CTW.one (andMask_w (Y := XT) (fun _ _ h => h.x) (by intros; trivial))

/-! ## The halvings -/

/-- Register `r` a mask. -/
def MR (r : Reg) (s : State) : Prop := ∃ c, s.gpr r = mask c

theorem MR.keep {r : Reg} {rs : List Reg} {s t : State} (h : MR r s) (k : Keep rs s t) (hr : r ∉ rs) : MR r t := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, (k.gpr r hr).trans hc⟩

/-- The top word of narrow `x` zero. -/
def zX (P : DP) (s : State) : Prop := word s.mem P.B (slot (vk P.k) nXn + 8 * vk P.k) = 0

theorem zX_out {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s t : State} (h : GC w X a s) {d n : Nat}
    (o : Outside a.1.B d n s.mem t.mem)
    (hd : slot (vk a.1.k) nXn + 8 * vk a.1.k + 8 ≤ d ∨ d + n ≤ slot (vk a.1.k) nXn + 8 * vk a.1.k)
    (z : zX a.1 s) : zX a.1 t := by
  rcases a with ⟨P, i⟩
  obtain ⟨I, m₀, c, e, g, L, -⟩ := h
  subst e
  have o' : Outside I.B d n s.mem t.mem := o
  have hd' : slot (vk I.k) nXn + 8 * vk I.k + 8 ≤ d ∨ d + n ≤ slot (vk I.k) nXn + 8 * vk I.k := hd
  have z' : word s.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0 := z
  have := g.bndv L.1 (j := nXn) (k := vk I.k + 1) (by decide) (by omega)
  show word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  rw [o'.word hd' (by omega)]; exact z'

theorem zX_frm {w : Nat → Nat} {X : Pub → State → Prop} {a : Pub} {s t : State} (h : GC w X a s)
    (f : Frm a.1.B hdrW s.mem t.mem) (z : zX a.1 s) : zX a.1 t := by
  rcases a with ⟨P, i⟩
  obtain ⟨I, m₀, c, e, g, L, -⟩ := h
  subst e
  have f' : Frm I.B hdrW s.mem t.mem := f
  have z' : word s.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0 := z
  have := g.bndv L.1 (j := nXn) (k := vk I.k + 1) (by decide) (by omega)
  show word t.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
  rw [Frm.hdrW_word f' (by have := slot_ge (vk I.k) nXn; omega) (by omega)]; exact z'

theorem zX_mem {P : DP} {s t : State} (hm : t.mem = s.mem) (z : zX P s) : zX P t := by
  unfold zX at z ⊢; rw [hm]; exact z

/-- The halvings' count. -/
abbrev NT (P : DP) : Nat := 64 * vk P.k

theorem NT_ok (I : RpIn) (L : RpLens I) : 0 < NT (dpub I) ∧ NT (dpub I) < 2 ^ 64 := by
  have := L.k2; simp only [NT, vk, dpub]; omega

/-- The count and `x`'s top word, and masks in `x1`, `x2`. -/
def XT2 (a : Pub) (s : State) : Prop := XL NT zX a s ∧ MR .x1 s ∧ MR .x2 s
def XT15 (a : Pub) (s : State) : Prop := XL NT zX a s ∧ MR .x15 s ∧ MR .x2 s
def XTx2 (a : Pub) (s : State) : Prop := XL NT zX a s ∧ MR .x2 s
def XTm (a : Pub) (s : State) : Prop := XL NT zX a s ∧ MR .x15 s

theorem XL.keep {X : DP → State → Prop} {N : DP → Nat} {a : Pub} {s t : State} {rs : List Reg}
    (h : XL N X a s) (k : Keep rs s t) (h6 : .x6 ∉ rs) (hx : X a.1 s → X a.1 t) : XL N X a t :=
  ⟨(k.gpr .x6 h6).trans h.1, hx h.2⟩

theorem twosBody_ct : CTW (GC vk (XL NT zX)) (GC vk (XL' NT zX)) twosBody := by
  unfold twosBody
  refine CTW.cons (by simp) (wsblk (Y := XT2) (rws_drop (by simp [twosFlags, ws])) (by taint_decide)
    fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
      subst e
      exact WP.mono (twosFlags_ok g.ws) fun t ⟨⟨h1, h2, hm⟩, k⟩ =>
        ⟨I, m₀, c, rfl, g.same hm k (by decide), L, x.keep k (by decide) (zX_mem hm), ⟨_, h1⟩, ⟨_, h2⟩⟩) ?_
  refine CTW.cons (by simp) (halfA_w (Y := XT2) (by decide) (by decide) (fun _ _ _ h o k =>
    ⟨h.x.1.keep k (by decide) (zX_out h o (wd_sep (by decide) (by omega) (by omega))),
      h.x.2.1.keep k (by decide), h.x.2.2.keep k (by decide)⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (regs_w (Y := XT15) (by taint_decide) (rs := [.x15]) (by decide) fun a s h =>
    WP.mono (mov15_ok s (.inl rfl)) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨⟨hm, h.x.1.keep k (by decide) (zX_mem hm),
      by obtain ⟨c, hc⟩ := h.x.2.1; exact ⟨c, h15.trans hc⟩, h.x.2.2.keep k (by decide)⟩, k⟩) ?_
  refine CTW.cons (by simp) (selA_w (Y := XTx2) (by decide) (by decide) (by decide) (fun _ _ h => h.x.2.1)
    (fun _ _ _ h o k => ⟨h.x.1.keep k (by decide) (zX_out h o (wd_sep (by decide) (by omega) (by omega))),
      h.x.2.2.keep k (by decide)⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (halfA_w (Y := XTx2) (by decide) (by decide) (fun _ _ _ h o k =>
    ⟨h.x.1.keep k (by decide) (zX_out h o (wd_sep (by decide) (by omega) (by omega))),
      h.x.2.keep k (by decide)⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (regs_w (Y := XT15) (by taint_decide) (rs := [.x15]) (by decide) fun a s h =>
    WP.mono (mov15_ok s (.inr rfl)) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨⟨hm, h.x.1.keep k (by decide) (zX_mem hm),
      by obtain ⟨c, hc⟩ := h.x.2; exact ⟨c, h15.trans hc⟩, h.x.2.keep k (by decide)⟩, k⟩) ?_
  refine CTW.cons (by simp) (selA_w (Y := XTx2) (by decide) (by decide) (by decide) (fun _ _ h => h.x.2.1)
    (fun _ _ _ h o k => ⟨h.x.1.keep k (by decide) (zX_out h o (.inr (by omega))),
      h.x.2.2.keep k (by decide)⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (blk (w' := Wk) (Y := XTm) (by taint_decide) fun ⟨P, i⟩ s h => h.elim
    fun I m₀ c e g L x => by
      subst e
      obtain ⟨c₂, h2⟩ := x.2
      rw [WP.block_append_iff]
      exact WP.mono (g.setWid_ok L.1) fun t₁ ⟨g₁, f₁, k₁⟩ => WP.mono (mov15_ok t₁ (.inr rfl))
        fun t ⟨⟨h15, hm⟩, k₂⟩ => ⟨I, m₀, c, rfl, g₁.same hm k₂ (by decide), L,
          (x.1.keep k₁ (by decide) (zX_frm h f₁)).keep k₂ (by decide) (zX_mem hm),
          ⟨c₂, h15.trans ((k₁.gpr .x2 (by decide)).trans h2)⟩⟩) ?_
  refine CTW.cons (by simp) (addA_w (Y := XL NT zX) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ h => h.x.2) (fun _ _ _ h o k => h.x.1.keep k (by decide)
      (zX_out h o (wdw_sep (by decide) (by decide) (by omega) (by simp only [Wk]; omega)))) (by taint_decide)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XL NT zX) (by decide) (by decide) (by decide)
    (fun _ _ _ h o k => h.x.keep k (by decide)
      (zX_out h o (wdw_sep (by decide) (by decide) (by omega) (by simp only [Wk]; omega)))) (by taint_decide)) ?_
  refine CTW.one (blk (w' := vk) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
    subst e
    rw [WP.block_append_iff]
    exact WP.mono (g.setNar_ok L.1) fun t₁ ⟨g₁, f₁, k₁⟩ => WP.mono (dec_ok t₁ .x6)
      fun t ⟨⟨h6, hm, _⟩, k₂⟩ => ⟨I, m₀, c, rfl, g₁.same hm k₂ (by decide), L,
        by rw [h6, k₁.gpr .x6 (by decide), x.1], zX_mem hm (zX_frm h f₁ x.2)⟩)

theorem twos_ct : CTW (GC Wk XT) (GC vk fun a s => zX a.1 s) twos := by
  unfold twos oneA
  simp only [List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := fun a s => zX a.1 s) (by decide) (fun ⟨P, i⟩ s t h _ _ z => by
    obtain ⟨I, m₀, c, e, g, L, -⟩ := h
    subst e
    exact (wv_eq_zero_iff _ _ _ _).mp (show wv t.mem I.B (slot (vk I.k) nXn) (vk I.k + 2) = 0 from z) (vk I.k)
      (by omega)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := fun a s => zX a.1 s) (by decide) (by decide) (by decide)
    (fun _ _ _ h o _ => zX_out h o (.inr (by omega)) h.x) (by taint_decide)) ?_
  refine CTW.cons (by simp) (wsblk (Y := fun a s => s.gpr .x6 = BitVec.ofNat 64 (NT a.1) ∧ zX a.1 s)
    (rws_drop (by simp [countN, ws])) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
      subst e
      exact WP.mono (countN_ok g.ws) fun t ⟨⟨h6, hm⟩, k⟩ =>
        ⟨I, m₀, c, rfl, g.same hm k (by decide), L, h6, zX_mem hm x⟩) ?_
  exact CTW.one (loop_w NT NT_ok twosBody_ct)

end VG.Proof.Rsa.AArch64.Rd
