module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VCTMain
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VCTMain
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: `saltBack` in constant time

With the salt's length given, `fixedBack` hashes the salt at its place;
with any, `autoBack` hashes every candidate, `dbLen` of them, a public
number; the branch is on whether a length is given, which is public too.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sCtr sHD oEm oSt oDig oLh oBuf oW oRsa scr lay shift)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor initF updF finF ldFn)
open VG.Proof.RsaOaep.X86_64 (encStack fb Lay Rep upd nW tw frT lenOf nopin sizes)
open VG.Proof.HashFns (StreamingOK)

variable {kH kG : Nat}

section
variable {TH : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (sH : Spec.HashFns.streaming kH = some TH) (eH : Spec.HashId.mgf1 kH = some Hh)

/-- With the salt's length given. -/
def PF (s : State) (W : Nat → BitVec 64) : Prop := PP s W ∧ vfixed s = true

include hTH sH eH in
theorem fixedBack_ct : RelCT isa (Two (VAt kH kG (VS PF))) fixedBack fun _ _ => True := by
  have hfn : ∀ a s, VSib kH kG a s → VFns s TH 10 := fun a s S => S.fns (.inl ⟨rfl, sH⟩)
  obtain ⟨hzS, -, hzW, -⟩ := sizes hTH
  unfold fixedBack seqs seqs seqs seqs seqs seqs
  refine RelCT.seq (v_post (J' := VS PF) (v_taintS (fun _ _ h => h) [] [14, 27, 39] (ks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ s _ S h => vmp_step S.1 (S.r9 hTH eH) h) ?_
  refine RelCT.seq (hashPrefix_ct hTH sH) ?_
  refine RelCT.seq (v_post (J' := fun s t => VS PF s t ∧ RU (vE s + vDb s - vsl s) (vsl s) (vD s + 8) s t)
    (v_taintS (fun _ _ h => h) [] [14, 29, 33, 39, 44] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ s _ S h => vfix_step S.1 (VS.getP (P := PP) (Q := fun s => vfixed s = true) h) h) ?_
  refine RelCT.seq (v_post (J' := VS PF) (v_upd hTH (j := 45) (.inl ⟨rfl, rfl⟩) hfn
    (fun s => vE s + vDb s - vsl s) vsl (fun s => vD s + 8) (fun s t hp h => ⟨h.1, h.2, ?_⟩)
    (fun a s S => ⟨by rw [S.e_eq, S.db_eq, S.sl_eq], S.sl_eq, by rw [S.d_eq]⟩) ⟨_, by taint_decide⟩)
    fun _ s _ S h => ?_) ?_
  · obtain ⟨-, d2, -, -, -, d6, -⟩ := h.1.2.2.2.sizes hp
    exact ⟨by unfold oBuf oRsa at *; omega, .inl (by unfold oBuf oSt at *; omega), .inl (by unfold oBuf oW at *; omega)⟩
  · obtain ⟨-, d2, -, -, -, d6, -⟩ := h.1.2.2.2.sizes S.1
    obtain ⟨a, b, c, d, e⟩ := h.2
    exact vupd_step hTH (.inl ⟨rfl, rfl⟩) (hfn _ s S) h.1 (by unfold oBuf oRsa at *; omega)
      (.inl (by unfold oBuf oSt at *; omega)) (.inl (by unfold oBuf oW at *; omega)) a c d e
  refine RelCT.seq (v_post (J' := fun s t => VS PF s t ∧ RF oDig (vD s + 8 + vsl s) s t)
    (v_taintS (fun _ _ h => h) [] [14, 29, 39] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ s _ S h => vfinSl_step (VS.getP (P := PP) (Q := fun s => vfixed s = true) h) h) ?_
  refine RelCT.seq (v_post (J' := VS PF) (v_fin hTH (j := 45) (.inl ⟨rfl, rfl⟩) hfn (fun _ => oDig)
    (fun s => vD s + 8 + vsl s) (fun s t _ h => ⟨h.1, h.2, .inr (by decide)⟩)
    (fun a s S => ⟨rfl, by rw [S.d_eq, S.sl_eq]⟩) ⟨_, by taint_decide⟩)
    fun _ s _ S h => vfin_step hTH (.inl ⟨rfl, rfl⟩) (hfn _ s S) h.1 (.inr (by decide)) h.2.1 h.2.2.2.1
      h.2.2.2.2) ?_
  exact v_taintS (fun _ _ h => h) [] [14, 33, 39, 44] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩

/-- The candidate `c`, which the checks bound. -/
def JK (c : Nat) (s t : State) : Prop := VS (PK c) s t ∧ c < vDb s

include hTH sH in
theorem cand_ct (c : Nat) : RelCT isa (Two (VAt kH kG (JK c))) cand fun _ _ => True := by
  have hfn : ∀ a s, VSib kH kG a s → VFns s TH 10 := fun a s S => S.fns (.inl ⟨rfl, sH⟩)
  obtain ⟨hzS, -, hzW, -⟩ := sizes hTH
  have hq : ∀ {a b : Nat}, a + 256 ≤ oRsa → b + 256 ≤ oRsa → (a + 256 ≤ b ∨ b + 256 ≤ a) → a < 2 ^ 31 →
      b < 2 ^ 31 → (∃ hc, (taint.check (frT [] [14] 1) (copyQ a b) hc).isSome = true) →
      RelCT isa (Two (VAt kH kG (JK c))) (copyQ a b) (Two (VAt kH kG (JK c))) :=
    fun h1 h2 h3 h4 h5 ht => v_post (v_taintS (fun _ _ h => h.1) [] [14] (ks_sub (by decide)) nopin ht)
      fun _ _ _ _ h => WP.mono (vcopyQ_step h1 h2 h3 h4 h5 h.1) fun _ h' => ⟨h', h.2⟩
  unfold cand seqs seqs seqs seqs seqs seqs
  refine RelCT.seq (hq (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩) ?_
  unfold finCand
  refine RelCT.seq (RelCT.seq (v_post (J' := fun s t => JK c s t ∧ RF oLh (vD s + 8 + c) s t)
    (v_taintS (fun _ _ h => h.1) [] [14, 39] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => WP.mono (vfinArgs_step h.1) fun _ h' => ⟨⟨h'.1, h.2⟩, h'.2⟩)
    (v_post (J' := JK c) (v_fin hTH (j := 45) (.inl ⟨rfl, rfl⟩) hfn (fun _ => oLh) (fun s => vD s + 8 + c)
      (fun s t _ h => ⟨h.1.1, h.2, .inr (by decide)⟩) (fun a s S => ⟨rfl, by rw [S.d_eq]⟩) ⟨_, by taint_decide⟩)
      fun _ s _ S h => WP.mono (vfin_step hTH (.inl ⟨rfl, rfl⟩) (hfn _ s S) h.1.1 (.inr (by decide)) h.2.1 h.2.2.2.1
        h.2.2.2.2) fun _ h' => ⟨h', h.1.2⟩)) ?_
  refine RelCT.seq (v_post (J' := JK c) (v_taintS (fun _ _ h => h.1) [] [14] (ks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ s _ S h => WP.mono (vselC_step (by
      obtain ⟨-, -, -, -, -, -, d7⟩ := h.1.2.2.2.sizes S.1; have := h.2; omega) h.1)
      fun _ h' => ⟨h', h.2⟩) ?_
  refine RelCT.seq (hq (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩) ?_
  unfold updCand
  refine RelCT.seq (RelCT.seq (v_post (J' := fun s t => JK c s t ∧ RU (oBuf + c) 1 (vD s + 8 + c) s t)
    (v_taintS (fun _ _ h => h.1) [] [14, 39] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => WP.mono (vupdArgs_step h.1) fun _ h' => ⟨⟨h'.1, h.2⟩, h'.2⟩)
    (v_post (J' := JK c) (v_upd hTH (j := 45) (.inl ⟨rfl, rfl⟩) hfn (fun _ => oBuf + c) (fun _ => 1)
      (fun s => vD s + 8 + c) (fun s t hp h => ⟨h.1.1, h.2, ?_⟩) (fun a s S => ⟨rfl, rfl, by rw [S.d_eq]⟩)
      ⟨_, by taint_decide⟩)
      fun _ s _ S h => WP.mono (vupd_step hTH (.inl ⟨rfl, rfl⟩) (hfn _ s S) h.1.1 (a := oBuf + c) (len := 1) ?_
        ?_ ?_ h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun _ h' => ⟨h', h.1.2⟩)) ?_
  · obtain ⟨-, -, -, -, -, -, d7⟩ := h.1.1.2.2.2.sizes hp
    have := h.1.2
    exact ⟨by unfold oBuf oRsa; omega, .inl (by unfold oBuf oSt; omega), .inl (by unfold oBuf oW; omega)⟩
  · obtain ⟨-, -, -, -, -, -, d7⟩ := h.1.1.2.2.2.sizes S.1
    have := h.1.2; unfold oBuf oRsa; omega
  · obtain ⟨-, -, -, -, -, -, d7⟩ := h.1.1.2.2.2.sizes S.1
    have := h.1.2; exact .inl (by unfold oBuf oSt; omega)
  · obtain ⟨-, -, -, -, -, -, d7⟩ := h.1.1.2.2.2.sizes S.1
    have := h.1.2; exact .inl (by unfold oBuf oW; omega)
  refine RelCT.seq (hq (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩) ?_
  exact v_taintS (fun _ _ h => h.1) [] [44] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩

theorem ne_cond {t : State} {j n : Nat} (hj : j < n) (hz : t.zf = some (decide (j + 1 = n))) :
    isa.eval .ne t = some (decide (j + 1 < n)) := by
  show t.zf.map (!·) = _
  rw [hz]
  by_cases hl : j + 1 < n
  · rw [decide_eq_false (show ¬ j + 1 = n by omega), decide_eq_true hl]; rfl
  · rw [decide_eq_true (show j + 1 = n by omega), decide_eq_false hl]; rfl

/-- After the last candidate. -/
def PKe (s : State) (W : Nat → BitVec 64) : Prop := PK (vDb s) s W

include hTH sH in
theorem cands_ct :
    RelCT isa (Two (VAt kH kG (VS (PK 0)))) (.loop cand .ne) (Two (VAt kH kG (VS PKe))) := by
  refine (two_loop (Φ := fun a j t => VAt kH kG (JK j) a t) (Ψ := VAt kH kG (VS PKe)) vDb
    (fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ e₁ e₂ =>
      cand_ct hTH sH p.2 _ _ _ _ _ _ ⟨p.1, h₁, h₂⟩ e₁ e₂) fun a j t hj ⟨s, S, h⟩ => ?_).mono ?_ fun _ _ h => h
  · rw [← S.db_eq] at hj ⊢
    refine WP.mono (vcand_step hTH S.1 (S.fns (.inl ⟨rfl, sH⟩)) hj h.1) fun t' ⟨hz, h'⟩ =>
      ⟨ne_cond hj hz, fun hl => ⟨s, S, h', hl⟩,
        fun he => ⟨s, S, by rw [he] at h'; exact h'⟩⟩
  · rintro s₁ s₂ ⟨a, ⟨x₁, S₁, h₁⟩, ⟨x₂, S₂, h₂⟩⟩
    have d := (h₁.2.2.2.sizes S₁.1).1
    exact ⟨a, ⟨by rw [← S₁.db_eq]; omega, x₁, S₁, h₁, by omega⟩, by rw [← S₁.db_eq]; omega, x₂, S₂, h₂,
      by rw [S₂.db_eq, ← S₁.db_eq]; omega⟩

include hTH sH eH in
theorem autoBack_ct : RelCT isa (Two (VAt kH kG (VS PP))) autoBack fun _ _ => True := by
  unfold autoBack seqs seqs seqs seqs seqs seqs seqs
  refine RelCT.seq (v_post (J' := VS PP) (v_taintS (fun _ _ h => h) [] [14, 27, 39] (ks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ s _ S h => vmp_step S.1 (S.r9 hTH eH) h) ?_
  refine RelCT.assoc (RelCT.seq (v_post (J' := VS PP) (v_taintS (fun _ _ h => h) [] [14, 33, 44]
    (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩) fun _ s _ S h => WP.seq (WP.mono (vcopyDb_step S.1 h)
      fun _ h' => vshift_step S.1 h'.1 h'.2)) ?_)
  refine RelCT.seq (hashPrefix_ct hTH sH) ?_
  refine RelCT.seq (v_post (J' := VS PP) (v_taintS (fun _ _ h => h) [] [14] (ks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ _ _ _ h => vcopyQ_step (by decide) (by decide) (by decide) (by decide)
      (by decide) h) ?_
  refine RelCT.seq (v_post (J' := VS (PK 0)) (v_taintS (fun _ _ h => h) [] [] (ks_sub (by decide)) nopin
    ⟨_, by taint_decide⟩) fun _ _ _ _ h => vctr0_step h) ?_
  refine RelCT.seq (cands_ct hTH sH) ?_
  exact v_taintS (fun _ _ h => h) [] [14, 33, 39, 44] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩

include hTH sH eH in
theorem saltBack_ct : RelCT isa (Two (VAt kH kG (VS PP))) saltBack fun _ _ => True := by
  unfold saltBack
  refine RelCT.seq (v_post (J' := fun s t => VS PP s t ∧ t.zf = some (vfixed s))
    (v_taintS (fun _ _ h => h) [] [28] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => vany_step h) ?_
  refine v_ite (fun s => some (vfixed s)) (fun s t h => h.2) (fun a s S => by rw [S.fixed])
    (v_branch (J' := VS PF) (fun s t _ h e => ?_) (fixedBack_ct hTH sH eH))
    (v_branch (J' := VS PP) (fun _ _ _ h _ => h.1) (autoBack_ct hTH sH eH))
  have : t.zf = some true := e
  rw [h.2, Option.some.injEq] at this
  exact h.1.addP this

end

end VG.Proof.RsaPss.X86_64
