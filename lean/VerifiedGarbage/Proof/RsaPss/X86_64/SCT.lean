module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SCTMain
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SCTMain
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the encoding and the private-key operation in constant time

`H = Hash(0⁸ ‖ mHash ‖ salt)` (`shashM_ct`), MGF1 (`s_mgf`), the pieces of
`signEnc` (`signEnc_ct`), and the private-key operation's arguments and call
(`signMain_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes oEm oSt oDig oBuf oW oRsa lay)
open VG.Impl.Mgf1.X86_64 (seqs mgfXor)
open VG.Proof.RsaOaep.X86_64 (fb Lay Rep nW lenOf FnsD MQ MFit mgf_ct nopin sizes outR)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)
open VG.Proof.HashFns (StreamingOK)

variable {kH kG : Nat}

section
variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh) (sH : Spec.HashFns.streaming kH = some TH) (sG : Spec.HashFns.streaming kG = some TG)
  (eH : Spec.HashId.mgf1 kH = some Hh) (eG : Spec.HashId.mgf1 kG = some Gh)

include hTH eH in
theorem SSib.dl {a s : State} (S : SSib kH kG a s) : (stackArg s 11).toNat = sgD s := by
  have e : Spec.HashId.mgf1 (sselH s) = some Hh := by rw [S.2.2.1]; exact eH
  rw [S.1.dl Hh e, hTH.len, VG.Proof.RsaOaep.X86_64.lenOf_eq hTH e]

include hTH sH in
/-- `H`'s state set to represent the prefix. -/
theorem shashPrefix_ct {P : State → (Nat → BitVec 64) → Prop} :
    RelCT isa (Two (SAt kH kG (SS P))) hashPrefix (Two (SAt kH kG (SS P))) := by
  have hT := hTH
  have hfn : ∀ a s, SSib kH kG a s → FnsD s TH 18 := fun a s S => S.fns (.inl ⟨rfl, sH⟩)
  unfold hashPrefix seqs seqs seqs
  refine RelCT.seq (s_post (J' := fun s t => SS P s t ∧ t.gpr .rdi = off (stackArg s 14) oSt)
    (s_taintS (fun _ _ h => h) [] [14] (sks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => sscr_step h) ?_
  refine RelCT.seq (s_post (J' := SS P) (s_init hT hfn (fun _ _ h => h) ⟨_, by taint_decide⟩)
    fun _ s _ S h => sinit_step hT (hfn _ s S) h.1 h.2) ?_
  refine RelCT.seq (s_post (J' := fun s t => SS P s t ∧ SRU (off (stackArg s 14) oMp) (sgD s + 8) 0 s t)
    (s_taintS (fun _ _ h => h) [] [14, 39] (sks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => spre_step h) ?_
  refine s_post (s_upd hT hfn (fun _ => oMp) (fun s => sgD s + 8) (fun _ => 0)
    (fun s t hp h => ⟨h.1, h.2, ?_⟩) (fun a s S => ⟨rfl, by rw [S.d_eq], rfl⟩) ⟨_, by taint_decide⟩)
    fun _ s _ S h => ?_
  · obtain ⟨-, -, -, hD64, -⟩ := h.1.2.2.2.sizes hp
    obtain ⟨hzS, -, hzW, -⟩ := sizes hT
    exact ⟨by unfold oMp oRsa; omega, .inr (by unfold oMp oSt; omega), .inl (by unfold oMp oW; omega)⟩
  · obtain ⟨-, -, -, hD64, -⟩ := h.1.2.2.2.sizes S.1
    obtain ⟨hzS, -, hzW, -⟩ := sizes hT
    exact supd_step hT (hfn _ s S) h.1 (by unfold oMp oRsa; omega) (.inr (by unfold oMp oSt; omega))
      (.inl (by unfold oMp oW; omega)) h.2

include hTH sH in
/-- `H = Hash(0⁸ ‖ mHash ‖ salt)`. -/
theorem shashM_ct : RelCT isa (Two (SAt kH kG (SS PT))) hashM (Two (SAt kH kG (SS PT))) := by
  have hT := hTH
  have hfn : ∀ a s, SSib kH kG a s → FnsD s TH 18 := fun a s S => S.fns (.inl ⟨rfl, sH⟩)
  unfold hashM seqs seqs seqs seqs
  refine RelCT.seq (shashPrefix_ct hTH sH) ?_
  refine RelCT.seq (s_post (J' := fun s t => SS PT s t ∧ SRU (stackArg s 12) (ssl s) (sgD s + 8) s t)
    (s_taintS (fun _ _ h => h) [] [14, 28, 29, 39] (sks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ S h => ssalt_step S.1 h) ?_
  refine RelCT.seq (s_post (J' := SS PT) (s_updExt hT hfn (fun s => sgD s + 8) (fun _ _ _ h => h)
    (fun a s S => by rw [S.d_eq]) ⟨_, by taint_decide⟩)
    fun _ s _ S h => supdExt_step hT S.1 (hfn _ s S) h.1 h.2) ?_
  refine RelCT.seq (s_post (J' := fun s t => SS PT s t ∧ SRF oDig (sgD s + 8 + ssl s) s t)
    (s_taintS (fun _ _ h => h) [] [14, 29, 39] (sks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => sfinSl_step h) ?_
  exact s_post (s_fin hT hfn (fun _ => oDig) (fun s => sgD s + 8 + ssl s)
    (fun _ _ _ h => ⟨h.1, h.2, .inr ⟨by decide, by decide⟩⟩) (fun a s S => ⟨rfl, by rw [S.d_eq, S.sl_eq]⟩)
    ⟨_, by taint_decide⟩)
    fun _ s _ S h => sfin_step hT (hfn _ s S) h.1 (.inr ⟨by decide, by decide⟩) h.2

include hTG sG eG in
/-- MGF1 masks `DB` with `H`. -/
theorem s_mgf : RelCT isa (Two (SAt kH kG (SS PMS))) (mgfXor lay) fun _ _ => True :=
  two_map (fun a => (⟨fb a, stackArg a 14, [outR a, sscrR a], sgE a + sgDb a, sgD a, sgE a, sgDb a, a,
      VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 19) 0, VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 19) 1,
      VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 19) 2⟩ : MQ))
    (fun a t ⟨s, S, h⟩ => by
      have hp := S.1
      obtain ⟨he, L, ⟨V, W, R, hA, -, -, hM⟩, hf⟩ := h
      obtain ⟨d1, d2, -⟩ := hf.sizes hp
      have e : Spec.HashId.mgf1 (sselG s) = some Gh := by rw [S.2.2.2.1]; exact eG
      have fit : MFit (sgE s + sgDb s) (sgD s) (sgE s) (sgDb s) :=
        ⟨by unfold oBuf oSt at *; omega, by unfold oBuf oSt at *; omega, .inr (Nat.le_refl _), d1,
          by unfold oBuf at d2; omega⟩
      refine ⟨?_, ?_, ?_, ⟨V, W, ?_, ?_, ?_, ?_⟩, S.calls he (.inr rfl) (S.fns (.inr ⟨rfl, sG⟩))⟩
      · show VG.Proof.RsaOaep.X86_64.FrV 2 (fb a) [outR a, sscrR a] t
        rw [← S.fb, ← S.out_eq, ← S.scr_eq]; exact he.frv hp
      · show Lay t (fb a) (stackArg a 14)
        rw [← S.fb, ← S.arg (j := 14) (by decide)]; exact L
      · show MFit (sgE a + sgDb a) (sgD a) (sgE a) (sgDb a)
        rw [← S.e_eq, ← S.db_eq, ← S.d_eq]; exact fit
      · show Rep t.mem (fb a) (stackArg a 14) V W
        rw [← S.fb, ← S.arg (j := 14) (by decide)]; exact R
      · show VG.Proof.RsaOaep.X86_64.MArgs W (stackArg a 14) (sgE a + sgDb a) (sgD a) (sgE a) (sgDb a)
        rw [← S.arg (j := 14) (by decide), ← S.e_eq, ← S.db_eq, ← S.d_eq]; exact hM
      · rw [← S.tw (.inr rfl) (i := 0) (by decide), ← S.tw (.inr rfl) (i := 1) (by decide),
          ← S.tw (.inr rfl) (i := 2) (by decide)]
        exact hA.sel.2.2.2
      · rw [hA.sel.2.1, VG.Proof.RsaOaep.X86_64.lenOf_eq hTG e])
    (mgf_ct hTG 2 (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid (.inl rfl))

include hTH hTG sH sG eH eG in
/-- After the checks: `EM`. -/
theorem signEnc_ct : RelCT isa (Two (SAt kH kG JMS)) signEnc (Two (SAt kH kG (SS PT))) := by
  unfold signEnc seqs seqs seqs seqs seqs seqs seqs seqs
  -- `DB`'s slots.
  refine RelCT.seq (s_post (J' := SS PT) (s_taintF (ks := [14, 31]) scW
      (fun s t _ h => ⟨h.1, fun k hk => h.2.2.1.fr k ((by decide : ∀ k ∈ [14, 31], k < nW) k hk)⟩)
      (fun a s S k hk => S.cw (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> decide))
      [.rax] (by decide)
      (s_pins [.rax] (fun s _ => BitVec.ofNat 64 (sk s - loV (sn0v s) - (lenOf (sselH s) + 2)))
        (fun s t _ h r hr => by rw [List.mem_singleton.mp hr]; exact h.2.2.2.1)
        (fun a s S r _ => by simp only [sk, S.n0, S.gpr (r := .rcx) (by decide), sselH, S.arg (j := 16) (by decide)]))
      ⟨_, by taint_decide⟩) fun _ _ _ _ h => sdb_step h) ?_
  -- `EM` cleared, and the prefix.
  refine RelCT.seq (s_post (J' := SS PT) (s_taintS (fun _ _ h => h) [] [14] (sks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ _ _ _ h => sclrEm_step h) ?_
  refine RelCT.seq (s_post (J' := SS PT) (s_taintS (fun _ _ h => h) [] [14, 27, 39] (sks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ _ _ S h => smp_step S.1 (S.dl hTH eH) h) ?_
  -- `H`, `0x01` and the salt, `H` and `0xbc`.
  refine RelCT.seq (shashM_ct hTH sH) ?_
  refine RelCT.seq (s_post (J' := SS PT) (s_taintS (fun _ _ h => h) [] [28, 29, 33, 44] (sks_sub (by decide))
    nopin ⟨_, by taint_decide⟩) fun _ _ _ S h => sputSalt_step S.1 h) ?_
  refine RelCT.seq (RelCT.assoc (RelCT.seq (s_post (J' := SS PT) (s_taintS (fun _ _ h => h) [] [14, 33, 39, 44]
      (sks_sub (by decide)) nopin ⟨_, by taint_decide⟩) fun _ _ _ S h => sputHd_step S.1 h)
    (s_post (J' := SS PT) (s_taintS (fun _ _ h => h) [] [14, 23] (sks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
      fun _ _ _ S h => sputBc_step S.1 h))) ?_
  -- MGF1, and the top bits.
  refine RelCT.seq (s_post (J' := SS PMS) (s_taintS (fun _ _ h => h) [] [33, 39, 44] (sks_sub (by decide))
    nopin ⟨_, by taint_decide⟩) fun _ _ _ _ h => smgfArgs_step h) ?_
  refine RelCT.seq (s_post (J' := SS PT) (s_mgf hTG sG eG) fun _ _ _ S h =>
    smgf_step hTG S.1 (S.fns (.inr ⟨rfl, sG⟩)) (by rw [S.2.2.2.1]; exact eG) h) ?_
  exact s_post (J' := SS PT) (s_taintS (fun _ _ h => h) [] [30, 33] (sks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ _ _ S h => sclear_step S.1 h

theorem sPrivArgs_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block privArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩

include hTH hTG sH sG eH eG in
/-- After the checks: the encoding, and the private-key operation. -/
theorem signMain_ct (v : PrivImpl) :
    RelCT isa (Two (SAt kH kG JMS)) (signMain v.name v.code) fun _ _ => True := by
  unfold signMain seqs seqs
  refine RelCT.seq (signEnc_ct hTH hTG sH sG eH eG) ?_
  exact RelCT.seq (s_post (J' := SSet) (two_taint [.rsp] (s_pins [.rsp] (fun s _ => fb s)
      (fun s t _ h r hr => by rw [List.mem_singleton.mp hr]; exact h.1.rsp) (fun a s S r _ => S.fb))
      sPrivArgs_taint.choose_spec) fun _ _ _ S h => sargs_step S.1 h) (privS_ct v)

end

end VG.Proof.RsaPss.X86_64
