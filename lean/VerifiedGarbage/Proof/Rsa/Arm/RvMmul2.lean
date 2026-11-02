module
public import VerifiedGarbage.Proof.Rsa.Arm.RvMmul
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

import VerifiedGarbage.Proof.Rsa.Arm.RvCtx
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Rsa.Arm.RvViews
import VerifiedGarbage.Proof.Bignum.Arm.MontSelected
import VerifiedGarbage.Proof.Bignum.Arm.Stack

/-! # `vg_rsa_recover_primes` on ARMv7: a Montgomery product on a stage, as a piece (`mmul_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem MM.of_rest (h : MM P s) {rs : List Reg} (r : Rest rs s t) (m : t.mem = s.mem) : MM P t :=
  ⟨h.mr.of_read (fun d n _ => by rw [m]) (by rw [m, r.sp]) r.sp r.rd r.wr, m ▸ h.n0⟩

theorem AfterM.of_rest {o T : Nat} (h : AfterM P σ o T A live AW liveW V ls s) {rs : List Reg} (r : Rest rs s t)
    (m : t.mem = s.mem) : AfterM P σ o T A live AW liveW V ls t :=
  ⟨h.bs.of_rest r m, h.mm.of_rest r m, m ▸ h.cnt, m ▸ h.arrs, m ▸ h.arrsW, m ▸ h.sl, h.live_lt, h.liveW_lt,
    h.ls_ok, m ▸ h.val⟩

/-- The top words cleared: the stage, with the result. -/
theorem AfterM.clr {o T : Nat} (h : AfterM P σ o T A live AW liveW V ls s) (hw : Ws s P.B P.Z P.w nArr)
    (hi : o = 1 ∨ o = 5 ∨ o = 6 ∨ o = 7) (hlW : ∀ j ∈ liveW, j ≠ (mBase + o) / 2) :
    WP isa (.block (clrTop (mBase + o))) s fun t =>
      KS P σ (upd A (mBase + o) T) ((mBase + o) :: live) AW liveW V ls t ∧ MM P t ∧ Ws t P.B P.Z P.w nArr := by
  have sz := h.bs.pre.sizes
  have hj : mBase + o < nArr := by simp only [mBase, nArr]; omega
  rw [← List.append_nil (clrTop _)]
  refine clrTop_ok hw hj (by decide) (by show 2 ≤ 2 * P.w6 + 2; omega) fun t ht k e r => WP.block_nil ?_
  have hds : ∀ d ∈ ([] : List Nat), SlotOk d := by simp
  refine ⟨⟨h.bs.of_frame (k.frameS (by simpa using fitZ_w sz hj) (by simp) (hdr_Z sz)) r.sp r.rd r.wr, ht.r8,
    ?_, ?_, ?_, ?_, ?_, h.liveW_lt, h.ls_ok⟩, h.mm.of_keep h.bs k (by
      simp only [List.mem_singleton]; rintro j rfl; right; simp only [mBase, nArr]; omega)
      (by simp) r.sp r.rd r.wr, ht⟩
  · refine (BitVec.eq_of_toNat_eq ?_).trans h.cnt
    exact k.slot (e := 16) (by decide) (by simp)
  · intro j hj'
    by_cases e' : j = mBase + o
    · subst e'; rw [upd_self, e, show P.w - 2 = 2 * P.w6 by simp only [RP.w]; omega]; exact h.val
    · rw [upd_ne _ _ e', k.num (fun i hi e2 => by simp at hi; exact e' (hi ▸ e2.symm)) (by simp)
        (fit_w sz (h.live_lt j ((List.mem_cons.mp hj').resolve_left e')))]
      exact h.arrs j ((List.mem_cons.mp hj').resolve_left e') e'
  · exact h.arrsW.keepOf k.toW (fun j hj i hi => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hi; subst hi; exact (hlW j hj).symm)
      (by simp) fun j hj => fit_W sz (h.liveW_lt j hj)
  · intro d hd; rw [k.slot (h.ls_ok d hd).1 (by simp), h.sl d hd]
  · intro j hj'
    rcases List.mem_cons.mp hj' with rfl | hj''
    · exact hj
    · exact h.live_lt j hj''

end

section
variable {P : RP}

/-- `mmul o a b`, from a stage whose operands are below `n`, to the result
`T` given. -/
theorem mmul_vp {o a b : Nat} (hi : MIdx o a b) (hodd : P.n % 2 = 1)
    {E : State → Prop} {A : State → Nat → Nat} {live : List Nat} {AW : State → Nat → Nat} {liveW : List Nat}
    {V : State → Nat → Nat} {ls : List Nat} {T : State → Nat}
    (ha : mBase + a ∈ live) (hb : mBase + b ∈ live) (hl2 : mBase + 2 ∉ live) (hl3 : mBase + 3 ∉ live)
    (hlW : ∀ j ∈ liveW, j ≠ (mBase + 2) / 2 ∧ j ≠ (mBase + o) / 2)
    (hv : ∀ σ, E σ → A σ (mBase + a) < P.n ∧ A σ (mBase + b) < P.n ∧ T σ < P.n ∧
      T σ * 2 ^ (64 * P.w6) % P.n = A σ (mBase + a) * A σ (mBase + b) % P.n) :
    VP (fun σ s => E σ ∧ KS P σ (A σ) live (AW σ) liveW (V σ) ls s ∧ MM P s) (seqs (mmul o a b))
      (fun σ t => E σ ∧ KS P σ (upd (A σ) (mBase + o) (T σ)) ((mBase + o) :: live) (AW σ) liveW (V σ) ls t ∧
        MM P t ∧ Ws t P.B P.Z P.w nArr) := by
  have opd := hi.operand
  unfold mmul
  simp only [seqs]
  -- Frame word 0 into `r0`.
  refine VP.seq (G := fun σ s => (E σ ∧ KS P σ (A σ) live (AW σ) liveW (V σ) ls s ∧ MM P s) ∧
    s.gpr .r0 = P.M0) ?_ (VP.seq (G := fun σ s => E σ ∧ AfterM P σ o (T σ) (A σ) live (AW σ) liveW (V σ) ls s)
      ?_ ?_)
  · show VP _ (.block ([(Reg.r0, 0)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hm⟩ => ?_
    · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
    · refine wp_loadStack (by decide) (by simp) hm.mr.stackRead fun t u => WP.block_nil ?_
      exact ⟨⟨e, h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem (by decide),
        hm.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩,
        u.gpr.trans hm.mr.saved⟩
  -- The product.
  · refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨e, h, hm⟩, ptr⟩ => ?_
    · have sz₁ : ∀ σ s, ((E σ ∧ KS P σ (A σ) live (AW σ) liveW (V σ) ls s ∧ MM P s) ∧ s.gpr .r0 = P.M0) →
          ArithmeticReady P.M0 P.lenM P.w6 s ∧ numAt s.mem (State.addr P.M0) P.w6 b <
            numAt s.mem (State.addr P.M0) P.w6 0 := fun σ s ⟨⟨e, h, hm⟩, ptr⟩ => by
        have pre := h.bs.pre
        have sz := pre.sizes
        have hn2 : P.n < 2 ^ (64 * P.w6) := by
          have := hm.mr.modulus
          rw [← hm.n0, numAt_val32 sz pre.fS]
          have := val32_lt (m := s.mem) (base := State.addr P.B) (d := arr P.w (mBase + 0)) (k := 2 * P.w6)
          rw [show 32 * (2 * P.w6) = 64 * P.w6 by omega] at this
          exact this
        have hbv := (hv σ e).2.1
        refine ⟨hm.mr.ready ptr, ?_⟩
        rw [numAt_eq sz pre.fS (by rw [h.arrs _ hb]; omega), h.arrs _ hb, hm.n0]
        exact hbv
      refine (selectedMontOp_ct (base := P.M0) (len := P.lenM) (w := P.w6) opd.1 opd.2.1 opd.2.2 ?_).mono
        (fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨sz₁ _ _ h₁, sz₁ _ _ h₂, ?_⟩) fun _ _ h => h
      · simp only [arrAt, Spec.Rsa.Mont.hdrBytes, RP.lenM]; omega
      · rw [h₁.1.2.1.bs.sp, h₁.1.2.1.bs.pre.sp, h₂.1.2.1.bs.sp, h₂.1.2.1.bs.pre.sp]
    · obtain ⟨hav, hbv, hT, hTv⟩ := hv σ e
      exact WP.mono (montOp_after h hm ptr hi hodd ha hb hav hbv hT hTv hl2 hl3 hlW) fun t ht => ⟨e, ht⟩
  -- The context, and the top words cleared.
  · refine VP.block_append (G := fun σ s => (E σ ∧ AfterM P σ o (T σ) (A σ) live (AW σ) liveW (V σ) ls s ∧
      s.gpr .r8 = P.B) ∧ Ws s P.B P.Z P.w nArr) (VP.block_append (G := fun σ s =>
        E σ ∧ AfterM P σ o (T σ) (A σ) live (AW σ) liveW (V σ) ls s ∧ s.gpr .r8 = P.B) ?_ ?_) ?_
    · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
      refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h⟩ => ?_
      · rw [h₁.2.bs.sp, h₁.2.bs.pre.sp, h₂.2.bs.sp, h₂.2.bs.pre.sp]
      · refine h.bs.ldrSp (o := aoS) (by decide) (by decide) (by decide) fun t u => WP.block_nil ?_
        exact ⟨e, h.of_rest (u.rest (ws := [.r8]) (by simp)) u.mem, u.gpr.trans h.bs.pre.aS⟩
    · refine VP.taint [.r8] ctxw_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨e, h, r8⟩ => ?_
      · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2, h₂.2.2]
      · exact WP.mono (ctxw_ok h.bs r8 h.cnt) fun t ⟨ht, r, m⟩ =>
          ⟨⟨e, h.of_rest r m, by rw [r.gpr _ (by decide), r8]⟩, ht⟩
    · have cert : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block (clrTop (mBase + o))) hc).isSome
          = true := by
        rcases hi.1 with rfl | rfl | rfl | rfl
        exacts [clrTopY_taint, clrTopG_taint, clrTopXm_taint, clrTopX_taint]
      refine VP.taint [.r7, .r8, .r9] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, _⟩, hw⟩ => ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · rw [h₁.2.r7, h₂.2.r7]
        · rw [h₁.2.r8, h₂.2.r8]
        · rw [h₁.2.r9, h₂.2.r9]
      · exact WP.mono (h.clr hw hi.1 fun j hj => (hlW j hj).2) fun t ht => ⟨e, ht⟩

end

end VG.Proof.Rsa.Arm.Recover
