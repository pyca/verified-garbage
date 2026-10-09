import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCall

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_movz)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)

theorem cachedSaves_vals {p : Params} {s s1 : State} (o : Only [.x9] s s1) :
    ∀ j (hj : j < cachedVerifySaves.length), s1.gpr (cachedVerifySaves[j]'hj).1 = (cachedLay p s).vals.getD j 0 := by
  intro j hj
  have : j < 8 := hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [cachedVerifySaves, verifySaves, fRnd, fKey, fMsg, fLen, fCtx, fCtxLen, fSig, fScr, List.map_cons, List.map_nil, ite_true, Nat.reduceBEq, VG.Proof.MlDsa.AArch64.Message.Lay.vals, cachedLay, List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
      List.getD_cons_succ] <;> exact o.get _

theorem verifyMessageCached_wp (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hV : Message.OptimizedVerify.VerifyFn p c) (hp : p ∈ params) {s : State} (hpre : (verifyMessageCachedContract p (abi.withConsts signRootConsts) 16).pre s) :
    WP isa (verifyMessageCached v.callee n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageCachedContract p (abi.withConsts signRootConsts) 16).post s s' := by
  have h := cachedPre_of hpre
  unfold verifyMessageCached top
  refine WP.seq (WP.mono_syms (lsr_ok s) fun s1 ⟨o1, hc1⟩ hy1 => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := cachedLay_ok hp h h8
    refine wp_ite_f hc1 (WP.seq (WP.mono_syms (enter_ok hL rfl (by decide) rfl (o1.get .x6) (by rw [o1.sp]; rfl)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .x4) (cachedSaves_vals o1) (by decide))
      fun t hc hyt => ?_))
    have hXtr : (cachedLay p s).XS.Disjoint ⟨s.gpr .x7, 64⟩ :=
      h.trScr.symm.sub_left (cachedLay_X p s).sub
    have htr : bytesAt t.mem (s.gpr .x7) 64 = pkTr (bytesAt s.mem (s.gpr .x0) p.pkLen) := by
      rw [hc.bytesAt_eq hXtr h.stkTr (by decide), o1.mem]
      exact h.digest
    refine WP.seq (WP.seq (WP.mono_syms (muHash_ok v hL hc (tr := .slot fRnd) (by decide) rfl
      (fun t' hc' => by
        rw [hc'.slotV (f := fRnd) (j := 5) rfl (by omega)]
        rfl)
      ⟨⟨s.gpr .x7, 64⟩, by simp [cachedLay, h.rd], within_self _⟩
      (hXtr.symm.sub_right (Region.sub_prefix (by decide)))
      (hXtr.symm.sub_right (within_off (cachedLay p s).X (d := 200) (n := 640) (k := 1024) (by omega)).sub)
      h.stkTr) fun t₂ ⟨hc₂, hμ⟩ hymu => ?_))
    have hroots : StaticRoots 16 t₂ := roots_ctx h (by simpa only [o1.mem] using hc₂)
      (hymu.trans (hyt.trans hy1))
    refine WP.mono (verifyCall_ok hV hp h h8 hc₂ hroots) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun s'' ⟨hcs, hsp, hvs, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), hsp,
      fun r hr => (hvs r hr).trans (o1.vcs r hr)⟩, ?_⟩
    sig_post [verifyMessageCachedContract, verifyMessageCachedSig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range, List.range.loop]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₂.mem (s.gpr .x0) p.pkLen = bytesAt s.mem (s.gpr .x0) p.pkLen :=
      (hc₂.bytesAt_eq (p := (cachedLay p s).key) (n := p.pkLen) hL.xKey hL.kKey (by have := h.nPk; omega)).trans
        (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (s.gpr .x5) p.sigLen = bytesAt s.mem (s.gpr .x5) p.sigLen :=
      (hc₂.bytesAt_eq (p := (cachedLay p s).sig) (n := p.sigLen) (h.sigScr.symm.sub_left (cachedLay_X p s).sub) h.stkSig
        (by have := h.nSig; omega)).trans (by rw [hm₀]; rfl)
    have hμ' := hμ
    rw [htr, hm₀] at hμ'
    rw [ek, es, hμ'] at hq
    rw [hx0]
    simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (wp_movz fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp],
      fun r hr => by rw [o2.vcs r hr, o1.vcs r hr]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.x0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h9 : r ∉ [Reg.x9] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.get r h0, o1.get r h9]
    · sig_post [verifyMessageCachedContract, verifyMessageCachedSig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range,
        List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), e2]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
