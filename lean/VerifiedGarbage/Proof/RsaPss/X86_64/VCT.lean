module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VCTBack
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VCTBack
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: constant time

The call of the public operation is constant time for its contract, whose
public data the entry's fix (`callV_ct`); MGF1 is, for the same public
data in both runs (`v_mgf`); `verifyMain` is, piece by piece
(`verMain_ct`); the prologues, the selectors and the checks are, their
branches on public data (`verBody_ct`); and so is
`vg_rsa_pss_verify_precomputed` (`ver_constantTime`), which meets the
shared contract (`ver_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sCtr sHD sK oEm oSt oDig oLh oBuf oW oRsa scr lay)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub Lay Rep upd nW tw frT lenOf nopin sizes
  ME MQ MFit stackArg_entry e_entry_regs mgf_ct relCT_alloc cf_false fns_of_tab SelPt selProW_ct)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG.Proof.HashFns (StreamingOK)

variable {kH kG : Nat}

theorem ks_sub' {ks : List Nat} (h : ks.all (fun k => decide (k ∈ vKs)) = true) : ∀ k ∈ ks, k ∈ vKs :=
  fun k hk => of_decide_eq_true (List.all_eq_true.mp h k hk)

/-! ## The call of the public operation -/

/-- Before the call. -/
def JC (s t : State) : Prop := VS PC s t ∧ RC s t

/-- The state the public operation starts from. -/
abbrev vEntry (s t : State) : State := t.callEntry.withRegions (callRdV s) (callWrV s)

theorem JC.w {s t : State} (h : JC s t) :
    t.mem.readW (off (fb s) (8 * 0)) 64 = stackArg s 0 ∧ t.mem.readW (off (fb s) (8 * 1)) 64 = s.gpr .rsi ∧
      t.mem.readW (off (fb s) (8 * 2)) 64 = off (stackArg s 4) oRsa ∧
      t.mem.readW (off (fb s) (8 * 3)) 64 = stackArg s 5 - 1024 := by
  obtain ⟨⟨-, -, ⟨V, W, R, -, -, -, w0, w1, w2, w3⟩, -⟩, -⟩ := h
  exact ⟨(R.fr 0 (by decide)).trans w0, (R.fr 1 (by decide)).trans w1, (R.fr 2 (by decide)).trans w2,
    (R.fr 3 (by decide)).trans w3⟩

/-- What the public operation's contract makes public, from the anchor. -/
theorem callV_view {a s t : State} (S : VSib kH kG a s) (h : JC s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (vEntry s t).gpr =
      [off (stackArg a 4) oEm, a.gpr .rsi, stackArg a 6, stackArg a 7, a.gpr .rdx, a.gpr .rcx, fb a - 8] ∧
    stackArg (vEntry s t) 0 = stackArg a 0 ∧ stackArg (vEntry s t) 1 = a.gpr .rsi ∧
    stackArg (vEntry s t) 2 = off (stackArg a 4) oRsa ∧ stackArg (vEntry s t) 3 = stackArg a 5 - 1024 ∧
    Spec.Rsa.wordsAt (vEntry s t).mem ((vEntry s t).gpr .rdx) ((vEntry s t).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat ∧
    Spec.Rsa.bytesAt (vEntry s t).mem ((vEntry s t).gpr .r8) ((vEntry s t).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  have hp := S.1
  have hw := h.w
  obtain ⟨⟨he, L, -, -⟩, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfv : FrV s t.callEntry.mem :=
    he.fr.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  have hF8 := L.F8
  have hFw := L.Fw
  have sa : ∀ i < 4, stackArg (vEntry s t) i = t.mem.readW (off (fb s) (8 * i)) 64 := fun i hi =>
    stackArg_entry he.rsp hF8 _ _ (by unfold frameBytes at hFw; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e_entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.arg (j := 4) (by decide),
      S.gpr (r := .rsi) (by decide), S.arg (j := 6) (by decide), S.arg (j := 7) (by decide),
      S.gpr (r := .rdx) (by decide), S.gpr (r := .rcx) (by decide)]
  · rw [sa 0 (by decide), hw.1, S.arg (j := 0) (by decide)]
  · rw [sa 1 (by decide), hw.2.1, S.gpr (r := .rsi) (by decide)]
  · rw [sa 2 (by decide), hw.2.2.1, S.arg (j := 4) (by decide)]
  · rw [sa 3 (by decide), hw.2.2.2, S.arg (j := 5) (by decide)]
  · simp only [vEntry, State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx, State.withRegions_mem]
    rw [preV_words hp hfv]
    exact S.2.1.2.2.2.2.2.1.symm
  · simp only [vEntry, State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9, State.withRegions_mem]
    rw [FrV.bytes hfv hp.dKe hp.deS.symm (by have := hp.wE; omega)]
    exact S.2.1.2.2.2.2.1.symm

theorem callV_ct (v : PublicImpl) : RelCT isa (Two (VAt kH kG JC)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := callV_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := callV_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := callV_covers S₁.1 j₁.1.1.rd j₁.1.1.wr
  obtain ⟨c₂, w₂⟩ := callV_covers S₂.1 j₂.1.1.rd j₂.1.1.wr
  have p₁ := callV_pre S₁.1 j₁.1.1.rsp j₁.w.1 j₁.w.2.1 j₁.w.2.2.1 j₁.w.2.2.2 j₁.2.1 j₁.2.2.1 j₁.2.2.2.1
    j₁.2.2.2.2.1 j₁.2.2.2.2.2.1 j₁.2.2.2.2.2.2
  have p₂ := callV_pre S₂.1 j₂.1.1.rsp j₂.w.1 j₂.w.2.1 j₂.w.2.2.1 j₂.w.2.2.2 j₂.2.1 j₂.2.2.1 j₂.2.2.2.1
    j₂.2.2.2.2.1 j₂.2.2.2.2.2.1 j₂.2.2.2.2.2.2
  exact ⟨callRdV s₁, callWrV s₁, callRdV s₂, callWrV s₂, p₁, p₂, ⟨List.map_inj_left.mp (r₁.trans r₂.symm),
    a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm, a3₁.trans a3₂.symm, n₁.trans n₂.symm,
    e₁.trans e₂.symm⟩, c₁, w₁, c₂, w₂, by rw [j₁.1.1.rsp, j₂.1.1.rsp, S₁.fb, S₂.fb]⟩

/-! ## MGF1 and `verifyMain` -/

section
variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh) (sH : Spec.HashFns.streaming kH = some TH) (sG : Spec.HashFns.streaming kG = some TG)
  (eH : Spec.HashId.mgf1 kH = some Hh) (eG : Spec.HashId.mgf1 kG = some Gh)

include hTG sG eG in
/-- MGF1 unmasks `DB` with `H`. -/
theorem v_mgf : RelCT isa (Two (VAt kH kG (VS PM))) (mgfXor lay) fun _ _ => True :=
  two_map (fun a => (⟨fb a, stackArg a 4, [vscrR a], vE a + vDb a, vD a, vE a, vDb a, a,
      tw a.mem (stackArg a 11) 0, tw a.mem (stackArg a 11) 1, tw a.mem (stackArg a 11) 2⟩ : MQ))
    (fun a t ⟨s, S, h⟩ => by
      have hp := S.1
      obtain ⟨he, L, ⟨V, W, R, hA, -, -, hM⟩, hf⟩ := h
      obtain ⟨d1, d2, -⟩ := hf.sizes hp
      have e : Spec.HashId.mgf1 (vselG s) = some Gh := by rw [S.2.2.2.1]; exact eG
      have fit : MFit (vE s + vDb s) (vD s) (vE s) (vDb s) :=
        ⟨by unfold oBuf oSt at *; omega, by unfold oBuf oSt at *; omega, .inr (Nat.le_refl _), d1,
          by unfold oBuf at d2; omega⟩
      refine ⟨?_, ?_, ?_, ⟨V, W, ?_, ?_, ?_, ?_⟩, S.calls he (.inr rfl) (S.fns (.inr ⟨rfl, sG⟩))⟩
      · show VG.Proof.RsaOaep.X86_64.FrV 1 (fb a) [vscrR a] t
        rw [← S.fb, ← S.scr_eq]; exact he.frv hp
      · show Lay t (fb a) (stackArg a 4)
        rw [← S.fb, ← S.arg (j := 4) (by decide)]; exact L
      · show MFit (vE a + vDb a) (vD a) (vE a) (vDb a)
        rw [← S.e_eq, ← S.db_eq, ← S.d_eq]; exact fit
      · show Rep t.mem (fb a) (stackArg a 4) V W
        rw [← S.fb, ← S.arg (j := 4) (by decide)]; exact R
      · show VG.Proof.RsaOaep.X86_64.MArgs W (stackArg a 4) (vE a + vDb a) (vD a) (vE a) (vDb a)
        rw [← S.arg (j := 4) (by decide), ← S.e_eq, ← S.db_eq, ← S.d_eq]; exact hM
      · rw [← S.tw (.inr rfl) (i := 0) (by decide), ← S.tw (.inr rfl) (i := 1) (by decide),
          ← S.tw (.inr rfl) (i := 2) (by decide)]
        exact hA.sel.2.2.2
      · rw [hA.sel.2.1, VG.Proof.RsaOaep.X86_64.lenOf_eq hTG e])
    (mgf_ct hTG 1 (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid (.inr (.inr rfl)))

include hTH hTG sH sG eH eG in
theorem verMain_ct (v : PublicImpl) :
    RelCT isa (Two (VAt kH kG JM)) (verifyMain v.name v.code) fun _ _ => True := by
  unfold verifyMain seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `DB`'s slots.
  refine RelCT.seq (v_post (J' := VS PT) (v_taintF (ks := [14, 31]) vcW
      (fun s t _ h => ⟨h.1, fun k hk => h.2.2.1.fr k ((by decide : ∀ k ∈ [14, 31], k < nW) k hk)⟩)
      (fun a s S k hk => S.cw (ks_sub' (by decide) k hk)) [.rax] (by decide)
      (v_pins [.rax] (fun s _ => BitVec.ofNat 64 (vk s - loV (n0v s) - (lenOf (vselH s) + 2)))
        (fun s t _ h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.2.2.1)
        (fun a s S r _ => by simp only [vk, S.n0, S.gpr (r := .rsi) (by decide), vselH, S.arg (j := 8) (by decide)]))
      ⟨_, by taint_decide⟩) fun _ _ _ _ h => vdb_step h) ?_
  -- The public operation.
  refine RelCT.seq (v_post (J' := JC) (v_taintS (fun _ _ h => h) [] [14, 21, 23, 26] (ks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ _ _ S h => vpub_step S.1 h) ?_
  refine RelCT.seq (v_post (J' := VS PT) (callV_ct v) fun _ _ _ S h => vcall_step v S.1 h.1 h.2) ?_
  -- The accumulator and MGF1.
  refine RelCT.seq (v_post (J' := VS PT) (v_taintS (fun _ _ h => h) [] [14, 23, 30, 31, 33] (ks_sub (by decide))
    nopin ⟨_, by taint_decide⟩) fun _ _ _ S h => vacc_step S.1 h) ?_
  refine RelCT.seq (v_post (J' := VS PM) (v_taintS (fun _ _ h => h) [] [33, 39, 44] (ks_sub (by decide))
    nopin ⟨_, by taint_decide⟩) fun _ _ _ _ h => vmgfArgs_step h) ?_
  refine RelCT.seq (v_post (J' := VS PT) (v_mgf hTG sG eG) fun _ _ _ S h =>
    vmgf_step hTG S.1 (S.fns (.inr ⟨rfl, sG⟩)) (by rw [S.2.2.2.1]; exact eG) h) ?_
  refine RelCT.seq (v_post (J' := VS PT) (v_taintS (fun _ _ h => h) [] [30, 33] (ks_sub (by decide))
    nopin ⟨_, by taint_decide⟩) fun _ _ _ S h => vclear_step S.1 h) ?_
  -- The scan, and the salt's hash.
  exact RelCT.assoc (RelCT.seq (v_post (J' := VS PP) (v_taintS (fun _ _ h => h) [] [28, 29, 33, 44]
    (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩) fun _ _ _ S h => vscan_step S.1 h) (saltBack_ct hTH sH eH))

end

end VG.Proof.RsaPss.X86_64
