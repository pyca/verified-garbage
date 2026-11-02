module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT4
import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.RdRoot
public import VerifiedGarbage.Proof.Rsa.AArch64.RdFin
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT4
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdRoot
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdFin
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvStore
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, the square root and the outputs

`sqrt_ct`: the square root's loop, its count `64 (v + 1)` in `x6`; then the
factors and the stores, between `GS` (the working space, the arguments,
the outputs and the mask, which the stores keep).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The square root -/

/-- The square root's count. -/
abbrev NS (P : DP) : Nat := 64 * (vk P.k + 1)

theorem NS_ok (I : RpIn) (L : RpLens I) : 0 < NS (dpub I) ∧ NS (dpub I) < 2 ^ 64 := by
  have := L.k2; simp only [NS, vk, dpub]; omega

/-- Register `r` a bit. -/
def BR (r : Reg) (s : State) : Prop := ∃ b : Bool, s.gpr r = BitVec.ofNat 64 b.toNat

theorem BR.keep {r : Reg} {rs : List Reg} {s t : State} (h : BR r s) (k : Keep rs s t) (hr : r ∉ rs) : BR r t := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, (k.gpr r hr).trans hb⟩

def XS1 (a : Pub) (s : State) : Prop := XL NS XN a s ∧ BR .x1 s
def XS2 (a : Pub) (s : State) : Prop := XL NS XN a s ∧ BR .x1 s ∧ BR .x2 s
def XS3 (a : Pub) (s : State) : Prop := XL NS XN a s ∧ BR .x2 s
def XSm (a : Pub) (s : State) : Prop := XL NS XN a s ∧ MR .x15 s

theorem sqrtBody_ct : CTW (GC vk (XL NS XN)) (GC vk (XL' NS XN)) sqrtBody := by
  unfold sqrtBody
  refine CTW.cons (by simp) (setWid_w (Y := XL NS XN) fun _ _ _ h _ k => h.x.keep k (by decide) id) ?_
  refine CTW.cons (by simp) (dblc_w (Y := XS1) (by decide) (fun _ s _ => cin_c0 s) (.inl rfl)
    (fun _ _ _ h _ k _ hb => ⟨h.x.keep k (by decide) id, hb⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (dblc_w (Y := XS2) (by decide) (fun _ s _ => cin_c0 s) (.inr rfl)
    (fun _ _ _ h _ k _ hb => ⟨h.x.1.keep k (by decide) id, h.x.2.keep k (by decide), hb⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setNar_w (Y := XS2) fun _ _ _ h _ k =>
    ⟨h.x.1.keep k (by decide) id, h.x.2.1.keep k (by decide), h.x.2.2.keep k (by decide)⟩) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XS3) (by decide)
    (fun _ s h => by obtain ⟨b, hb⟩ := h.x.2.1; exact cin_cOf (.inl rfl) hb)
    (fun _ _ _ h _ k _ => ⟨h.x.1.keep k (by decide) id, h.x.2.2.keep k (by decide)⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XL NS XN) (by decide)
    (fun _ s h => by obtain ⟨b, hb⟩ := h.x.2; exact cin_cOf (.inr rfl) hb)
    (fun _ _ _ h _ k _ => h.x.1.keep k (by decide) id) (by taint_decide)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XL NS XN) (by decide) (by decide) (by decide)
    (fun _ _ _ h _ k => h.x.keep k (by decide) id) (by taint_decide)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XL NS XN) (by decide) (fun _ s _ => cin_c0 s)
    (fun _ _ _ h _ k _ => h.x.keep k (by decide) id) (by taint_decide)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XL NS XN) (by decide) (fun _ s _ => cin_c1 s)
    (fun _ _ _ h _ k _ => h.x.keep k (by decide) id) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XSm) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ h _ k hm _ => ⟨h.x.keep k (by decide) id, hm⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (selA_w (Y := XSm) (by decide) (by decide) (by decide) (fun _ _ h => h.x.2)
    (fun _ _ _ h _ k => ⟨h.x.1.keep k (by decide) id, h.x.2.keep k (by decide)⟩) (by taint_decide)) ?_
  refine CTW.cons (by simp) (dblA_w (Y := XL NS XN) (by decide)
    (fun _ s h => by obtain ⟨c, hc⟩ := h.x.2; exact cin_mask hc)
    (fun _ _ _ h _ k _ => h.x.1.keep k (by decide) id) (by taint_decide)) ?_
  exact CTW.one (regs_w (by taint_decide) (rs := [.x6]) (by decide) fun a s h =>
    WP.mono (dec_ok s .x6) fun t ⟨⟨h6, hm, _⟩, k⟩ => ⟨⟨hm, by rw [h6, h.x.1], trivial⟩, k⟩)

theorem sqrt_ct : CTW (GC Wk XT) (GC vk XT) sqrt := by
  unfold sqrt
  simp only [List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (setNar_w (Y := XT) (by intros; trivial)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (wsblk (Y := fun a s => s.gpr .x6 = BitVec.ofNat 64 (NS a.1) ∧ XN a.1 s)
    (rws_drop (by simp [countS, ws])) (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L _ => by
      subst e
      exact WP.mono (countS_ok g.ws) fun t ⟨⟨h6, hm⟩, k⟩ =>
        ⟨I, m₀, c, rfl, g.same hm k (by decide), L, h6, trivial⟩) ?_
  refine CTW.cons (by simp) ((loop_w NS NS_ok sqrtBody_ct).mono (fun _ _ h => h) fun _ _ h =>
    h.imp (Y := XT) rfl fun _ => trivial) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.app (a := eqA nRm nZ) (by simp [eqA]) (by simp) (eqA_w (Y := XT) (by decide) (by decide)
    (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (andZero_w (Y := XT) (by intros; trivial))

/-! ## The factors and the stores -/

theorem factors_ct : CTW (GC vk XT) (GC vk XT) (seqs factorsA) := by
  refine CTW.cons (by simp) (regs_w (Y := fun _ s => MR .x15 s) (by taint_decide) (rs := [.x7, .x15]) (by decide)
    fun a s h => WP.mono (ones_ok s) fun t ⟨⟨h15, _, hm⟩, k⟩ => ⟨⟨hm, _, h15⟩, k⟩) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := fun _ s => MR .x15 s) (by decide)
    (fun _ _ _ h _ k _ => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (addA_w (Y := fun _ s => MR .x15 s) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun _ _ h => h.x) (fun _ _ _ h _ k => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (halfA_w (Y := fun _ s => MR .x15 s) (by decide) (by decide)
    (fun _ _ _ h _ k => h.x.keep k (by decide)) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (subA_w (Y := XT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (halfA_w (Y := XT) (by decide) (by decide) (by intros; trivial) (by taint_decide))

/-- Between the stores. -/
def GS (a : Pub) (s : State) : Prop :=
  ∃ (I : RpIn) (c : Bool), dpub I = a.1 ∧ Ws s I.B I.Z (vk I.k) ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD ∧ s.wr = I.W ∧ RpLens I ∧ DOuts I ∧
    word s.mem I.B (8 * Public.sMask) = mask c

theorem GS.ws {a : Pub} {s : State} (h : GS a s) : Ws s a.1.B a.1.Z (vk a.1.k) := by
  obtain ⟨I, c, e, h, -⟩ := h
  rw [← e]; exact h

theorem GC.gs {X : Pub → State → Prop} {a : Pub} {s : State} (h : GC vk X a s) : GS a s := by
  obtain ⟨I, m₀, c, e, g, L, -⟩ := h
  exact ⟨I, c, e, g.ws, g.args, g.wr, L.1, L.2, g.msk⟩

theorem pins_GS : Pins GS [.x0] :=
  pins_ws (fun a => a.1.B) (fun a => a.1.Z) (fun a => vk a.1.k) fun _ _ h => h.ws

theorem storeA_w {j sPtr : Nat} (hj : j < 16) (hP : sPtr < 32) (ptr : DP → Addr) (ptrI : RpIn → Addr)
    (hpI : ∀ I, ptr (dpub I) = ptrI I)
    (hA : ∀ (I : RpIn) (m : Mem), RpArgs m I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD → word m I.B (8 * sPtr) = ptrI I)
    (hO : ∀ I : RpIn, DOuts I → (∀ i < I.k, InRegions I.W (ptrI I + BitVec.ofNat 64 i) 1) ∧
      (∀ i < I.k, I.Z ≤ ofs I.B (ptrI I + BitVec.ofNat 64 i)))
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 Public.sK,
      .add .x .x1 .x1 .x9, ldh .x15 Public.sMask])) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x9]) storeBE hc₂).isSome = true) :
    CTW GS GS (seqs (storeA j sPtr Public.sK Public.sMask)) := by
  refine ⟨(pin_ct [.x0] [.x0, .x8, .x1, .x9] (Ψ := GS)
    (fun a => soVal a.1.B (off a.1.B (slot (vk a.1.k) j)) (ptr a.1) a.1.k) pins_GS ht₁ ?_ ht₂ ?_).mono
      (fun _ _ h => h) fun _ _ _ => trivial, ?_⟩
  · rintro ⟨P, i⟩ s ⟨I, c, rfl, hw, ha, -⟩
    exact storeBlk_ok hw hP (by decide) ((hA I s.mem ha).trans (hpI I).symm) ha.k
  all_goals
    rintro ⟨P, i⟩ s ⟨I, c, rfl, hw, ha, hW, L, O, hm⟩
    obtain ⟨hwr, hsep⟩ := hO I O
    have hn := hw.scr.nowrap
    have h256 := hw.h256
    refine WP.mono (storeA_ws hw hj hP (by decide) (hA I s.mem ha) ha.k hm (by have := L.k1; omega)
      (by have := L.k2; simp only [vk]; omega) (fun i hi => by rw [hW]; exact hwr i hi) hsep)
      fun t ⟨_, _, ht, hf, k⟩ => ?_
    have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
      fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)
    exact ⟨I, c, rfl, ht, ha.congr fun i hi => fw i (by unfold rArg at hi; omega), k.wr.trans hW, L, O,
      (fw _ (by decide)).trans hm⟩

theorem stores_ct : RelCT isa (Two (GC vk XT)) (seqs (storeA nP VG.Impl.Rsa.AArch64.Recover.sP Public.sK Public.sMask ++
    (storeA nQ VG.Impl.Rsa.AArch64.Recover.sQ Public.sK Public.sMask ++ ([.block retMask] : List (Prog isa)))))
    fun _ _ => True := by
  have h₁ := storeA_w (j := nP) (by decide) (by decide) DP.pP RpIn.pP (fun _ => rfl) (fun _ _ ha => ha.p)
    (fun I O => ⟨O.p, O.sp⟩) (by taint_decide) (by taint_decide)
  have h₂ := storeA_w (j := nQ) (by decide) (by decide) DP.pQ RpIn.pQ (fun _ => rfl) (fun _ _ ha => ha.q)
    (fun I O => ⟨O.q, O.sq⟩) (by taint_decide) (by taint_decide)
  have h₃ : CTW GS (fun _ _ => True) (seqs [.block retMask]) :=
    ⟨two_taint [.x0] pins_GS (by taint_decide), fun _ s ⟨_, _, _, hw, _, _, _, _, hm⟩ =>
      WP.mono (cvExit_ok hw hm) fun _ _ => trivial⟩
  exact ((h₁.mono (fun _ _ h => GC.gs h) fun _ _ h => h).app (by simp [storeA]) (by simp [storeA])
    (h₂.app (by simp [storeA]) (by simp) h₃)).1.mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.AArch64.Rd
