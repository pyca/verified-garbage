import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_lsr wp_movz eval_nonzero ne_zero_iff)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots pairedSignRootConsts)

theorem signMessage_wp (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hS : SignFn p c) (hp : p ∈ params) {s : State} (hpre : (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).pre s) :
    WP isa (signMessage v.callee n c p) s fun s' =>
      abiPreserved s s' ∧ (signMessageContract p (abi.withConsts pairedSignRootConsts) 16).post s s' := by
  have h := sPre_of hpre
  unfold signMessage top
  refine WP.seq (WP.mono_syms (lsr_ok s) fun s1 ⟨o1, hc1⟩ hy1 => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := slay_ok hp h h8
    refine wp_ite_f hc1 (WP.seq (WP.mono_syms (enter_ok hL rfl (by decide) rfl (o1.get .x7) (by rw [o1.sp]; rfl)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .x4) (signSaves_vals o1) (by decide))
      fun t hc hyt => ?_))
    have hsk := (skLen_ge hp).1
    have wtr : Within ⟨(slay p s).key + BitVec.ofNat 64 64, 64⟩ (slay p s).KEY :=
      within_off _ (show 64 + 64 ≤ p.skLen by omega)
    have hst : Region.Sub ⟨(slay p s).ST, 200⟩ (slay p s).XS := by
      have := Offset.sub_base (slay p s).X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [x0] using this
    refine WP.seq (WP.seq (WP.mono_syms (muHash_ok v hL hc (tr := .slotOff fKey 64) (by decide) rfl
      (fun t' hc' => hc'.slotOffV 64) ⟨_, List.mem_append_left _ hL.inKey, wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right hst)
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Offset.sub_base _ (by omega : 200 + 640 ≤ 1024)))
      (hL.kKey.sub_right wtr.sub)) fun t₁ ⟨hc₁, hμ⟩ hyμ => ?_))
    have hroots : StaticRoots 16 t₁ := roots_ctx h (by simpa only [o1.mem] using hc₁) (hyμ.trans (hyt.trans hy1))
    have hpair := paired_ctx h (by simpa only [o1.mem] using hc₁) (hyμ.trans (hyt.trans hy1))
    refine WP.mono (signCall_ok hS hp h h8 hc₁ hroots hpair) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun s'' ⟨hcs, hsp, hvs, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), hsp,
      fun r hr => (hvs r hr).trans (o1.vcs r hr)⟩, ?_⟩
    sig_post [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.pairedSignRootConsts_eq, List.range, List.range.loop]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [signInternal, messageRep, skTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₁.mem (s.gpr .x0) p.skLen = bytesAt s.mem (s.gpr .x0) p.skLen :=
      (hc₁.bytesAt_eq (p := (slay p s).key) (n := p.skLen) hL.xKey hL.kKey (by have := h.nSk; omega)).trans
        (by rw [hm₀]; rfl)
    have er : bytesAt t₁.mem (s.gpr .x5) 32 = bytesAt s.mem (s.gpr .x5) 32 :=
      (hc₁.bytesAt_eq (p := (slay p s).rnd) (n := 32) (h.rndScr.symm.sub_left (slay_X p s).sub) h.stkRnd
        (by decide)).trans (by rw [hm₀]; rfl)
    have etr : bytesAt t.mem ((slay p s).key + BitVec.ofNat 64 64) 64 =
        ((bytesAt s.mem (s.gpr .x0) p.skLen).drop 64).take 64 := by
      rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide), hm₀,
        Proof.MlKem.bytesAt_slice _ _ (by omega)]
      rfl
    rw [ek, er, hμ, etr, hm₀] at hq
    rw [hx0, hm]
    simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (wp_movz fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp],
      fun r hr => by rw [o2.vcs r hr, o1.vcs r hr]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.x0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h9 : r ∉ [Reg.x9] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.get r h0, o1.get r h9]
    · sig_post [signMessageContract, signMessageSig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.pairedSignRootConsts_eq, List.range, List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), e2]
      rfl

end VG.Proof.MlDsa.AArch64.Message.Paired
