module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the prologues and the checks, and `Verified`

The prologue and the selectors' prologue are checked by the taint analysis
(`selProW_ct`); the checks branch on `n₀`, `k`, `hLen` and the salt's
length, which are public (`signBody_ct`); so `vg_rsa_pss_sign` is constant
time (`sign_constantTime`) and meets the shared contract (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes)
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Proof.RsaOaep.X86_64 (decStack fb Rep nW frT lenOf nopin relCT_alloc cf_false fns_of_tab SelPt selProW_ct)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl)
open VG.Proof.HashFns (StreamingOK)

variable {kH kG : Nat}

theorem spro_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block signPrologue) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- At the entry of the frame. -/
def JAS (s t : State) : Prop := t = allocState frameBytes s

/-- A point in the frame whose words, at the slots `ks`, are `scW`'s: the
taint analysis from them. -/
theorem s_taintW {J : State → State → Prop} {W : State → Nat → BitVec 64}
    (hJ : ∀ s t, SPre s → J s t → SEnv s t ∧ ∃ V, Rep t.mem (fb s) (stackArg s 14) V (W s))
    (ks : List Nat) (hks : ks.all (fun k => decide (k ∈ vKs)) = true)
    (hW : ∀ s, ∀ k ∈ ks, W s k = scW s k) (rs : List Reg) (hpin : Pins (SAt kH kG J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 2) c hc).isSome = true) :
    RelCT isa (Two (SAt kH kG J)) c fun _ _ => True :=
  have hk : ∀ k ∈ ks, k ∈ vKs := fun k hk => of_decide_eq_true (List.all_eq_true.mp hks k hk)
  s_taintF scW (fun s t hp j => by
      obtain ⟨he, V, R⟩ := hJ s t hp j
      exact ⟨he, fun k hk' => (R.fr k (by have := vKs_iff (hk k hk'); unfold nW frameBytes; omega)).trans
        (hW s k hk')⟩)
    (fun _ _ S k hk' => S.cw (hk k hk')) rs
    (fun k hk' => by have := vKs_iff (hk k hk'); unfold nW frameBytes; omega) hpin h

/-- Zeros to `out`, and 0. -/
theorem sfail_ct {J : State → State → Prop} {W : State → Nat → BitVec 64}
    (hJ : ∀ s t, SPre s → J s t → SEnv s t ∧ ∃ V, Rep t.mem (fb s) (stackArg s 14) V (W s))
    (hW : ∀ s, ∀ k ∈ [21, 23], W s k = scW s k) :
    RelCT isa (Two (SAt kH kG J)) signFail fun _ _ => True :=
  s_taintW hJ [21, 23] (by decide) hW [] nopin ⟨_, by taint_decide⟩

theorem signW_scW {s : State} {k : Nat} (hk : k ∈ [21, 22, 23, 39]) : signW s k = scW s k :=
  (scW_eq (by simp at hk; omega) (by simp at hk; omega)).symm

section
variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh) (sH : Spec.HashFns.streaming kH = some TH) (sG : Spec.HashFns.streaming kG = some TG)
  (eH : Spec.HashId.mgf1 kH = some Hh) (eG : Spec.HashId.mgf1 kG = some Gh)

include hTH hTG sH sG eH eG in
/-- The prologues and the checks, then `signMain`. -/
theorem signBody_ct (iH : kH ∈ Spec.RsaPss.hashIds) (iG : kG ∈ Spec.RsaPss.hashIds) (v : PrivImpl) :
    RelCT isa (Two (SAt kH kG JAS)) (signBody v.name v.code) fun _ _ => True := by
  have hkm : ∀ {k : Nat}, k ∈ Spec.RsaPss.hashIds → k ∈ pssLens.map (·.1) := fun h =>
    List.mem_map.mpr ⟨_, mem_pssLens h, rfl⟩
  unfold signBody seqs seqs seqs
  -- The prologue.
  refine RelCT.seq (s_post (J' := JPS signPW) (two_taint [.rsp]
    (s_pins [.rsp] (fun s _ => fb s) (fun s t _ h r hr => by rw [List.mem_singleton.mp hr, h]; rfl)
      (fun a s S r _ => S.fb)) spro_taint.choose_spec) fun _ s t S h => by subst h; exact spro_step S.1) ?_
  -- The selectors.
  have hsel : ∀ a t, SAt kH kG (JPS signPW) a t →
      SelPt fb (fun a => stackArg a 14) 16 17 (fun _ => kH) (fun _ => kG) (fun a => stackArg a 18)
        (fun a => stackArg a 19) a t := by
    rintro a t ⟨s, S, k1, L1, R1, f1, -⟩
    have hp := S.1
    have hrd := k1.2.1
    have i1 := hp.arg_in hrd (j := 16) (by decide)
    have i2 := hp.arg_in hrd (j := 17) (by decide)
    have ar : ∀ m', Frame [⟨fb s, frameBytes⟩] t.mem m' →
        m'.readW (off (fb s) (frameBytes + 8 + 8 * 16)) 64 = BitVec.ofNat 64 kH ∧
          m'.readW (off (fb s) (frameBytes + 8 + 8 * 17)) 64 = BitVec.ofNat 64 kG := fun m' hm => ⟨by
      rw [arg_readS hp (f1.trans hm) (j := 16) (by decide), ← S.2.2.1]; simp, by
      rw [arg_readS hp (f1.trans hm) (j := 17) (by decide), ← S.2.2.2.1]; simp⟩
    have tH := hp.tab hrd f1 (j := 18) (.inl rfl)
    have tG := hp.tab hrd f1 (j := 19) (.inr rfl)
    rw [S.fb, S.arg (j := 14) (by decide)] at L1 R1
    rw [S.fb] at i1 i2 ar
    rw [S.fb, S.arg (j := 18) (by decide)] at tH
    rw [S.fb, S.arg (j := 19) (by decide)] at tG
    exact ⟨L1, ⟨_, _, R1⟩, i1, i2, ar, ⟨_, _, _, tH⟩, ⟨_, _, _, tG⟩⟩
  refine RelCT.seq (s_post (J' := JPS signW) (two_map id hsel
      (selProW_ct (F := fb) (S := fun a => stackArg a 14) (kH := fun _ => kH) (kG := fun _ => kG) pssLensOK
        (fun _ => hkm iH) (fun _ => hkm iG) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
        ⟨_, by taint_decide⟩))
    fun _ s _ S h => ssel_step S.1 h) ?_
  -- `n₀`, and its check.
  refine RelCT.seq (s_post (J' := SN) (s_taintW (W := signW) (fun s t hp h => ⟨h.env hp, _, h.2.2.1⟩) [22]
    (by decide) (fun _ _ hk => signW_scW (by simp at hk; simp [hk])) [] nopin ⟨_, by taint_decide⟩)
    fun _ s _ S h => sn0_step S.1 h) ?_
  refine s_ite (fun s => some (decide (sn0v s = 0))) (fun s t h => h.2.2.2.2) (fun a s S => by rw [S.n0])
    (s_branch (J' := SN) (fun _ _ _ h _ => h) (sfail_ct (W := signW) (fun _ _ _ h => ⟨h.1, _, h.2.2.1⟩)
      fun _ _ hk => signW_scW (by simp at hk; rcases hk with rfl | rfl <;> simp)))
    (s_branch (J' := fun s t => SN s t ∧ sn0v s ≠ 0) (fun s t _ h e => ⟨h, by
      have : t.zf = some false := e
      rw [h.2.2.2.2, Option.some.injEq] at this
      exact of_decide_eq_false this⟩) ?_)
  -- `emLen`, and its check.
  unfold seqs seqs
  refine RelCT.assoc (RelCT.seq (s_post (J' := SE) (s_taintW (W := signW) (fun s t _ h => ⟨h.1.1, _, h.1.2.2.1⟩)
    [23, 39] (by decide) (fun _ _ hk => signW_scW (by simp at hk; rcases hk with rfl | rfl <;> simp)) [.rax]
    (s_pins [.rax] (fun s _ => BitVec.ofNat 64 (sn0v s)) (fun s t _ h r hr => by
      rw [List.mem_singleton.mp hr]; exact h.1.2.2.2.1) (fun a s S r _ => by rw [S.n0]))
    ⟨_, by taint_decide⟩) fun _ s _ S h => sem_step S.1 h.1 h.2) ?_)
  refine s_ite (fun s => some (decide (sk s - loV (sn0v s) < lenOf (sselH s) + 2))) (fun s t h => h.2.2.2.2.1)
    (fun a s S => by simp only [sk, S.n0, S.gpr (r := .rcx) (by decide), sselH, S.arg (j := 16) (by decide)])
    (s_branch (J' := SE) (fun _ _ _ h _ => h) (sfail_ct (W := scW) (fun _ _ _ h => ⟨h.1, _, h.2.2.1⟩)
      fun _ _ _ => rfl))
    (s_branch (J' := fun s t => SE s t ∧ lenOf (sselH s) + 2 ≤ sk s - loV (sn0v s))
      (fun s t _ h e => ⟨h, by have := cf_false h.2.2.2.2.1 e; omega⟩) ?_)
  -- The salt's room, and its check.
  unfold seqs
  refine RelCT.seq (s_post (J' := SF) (s_taintW (W := scW) (fun s t _ h => ⟨h.1.1, _, h.1.2.2.1⟩) [29, 39]
    (by decide) (fun _ _ _ => rfl) [.rax]
    (s_pins [.rax] (fun s _ => BitVec.ofNat 64 (sk s - loV (sn0v s))) (fun s t _ h r hr => by
      rw [List.mem_singleton.mp hr]; exact h.1.2.2.2.1)
      (fun a s S r _ => by simp only [sk, S.n0, S.gpr (r := .rcx) (by decide)]))
    ⟨_, by taint_decide⟩) fun _ s _ S h => sfit_step S.1 h.1 h.2) ?_
  refine s_ite (fun s => some (decide (sk s - loV (sn0v s) - (lenOf (sselH s) + 2) < ssl s)))
    (fun s t h => h.2.2.2.2.1)
    (fun a s S => by simp only [sk, ssl, S.n0, S.gpr (r := .rcx) (by decide), sselH, S.arg (j := 16) (by decide),
      S.arg (j := 13) (by decide)])
    (s_branch (J' := SF) (fun _ _ _ h _ => h) (sfail_ct (W := scW) (fun _ _ _ h => ⟨h.1, _, h.2.2.1⟩)
      fun _ _ _ => rfl))
    (s_branch (J' := JMS) (fun s t _ h e => ?_) (signMain_ct hTH hTG sH sG eH eG v))
  have hc := cf_false h.2.2.2.2.1 e
  obtain ⟨he, L, R, hax, -, hn0, hfit⟩ := h
  exact ⟨he, L, R, hax, hn0, by omega⟩

end

/-- `vg_rsa_pss_sign`, calling the implementation `v` of
`vg_rsa_private_checked`, is constant time. -/
theorem sign_constantTime (v : PrivImpl) :
    ConstantTime isa scontract.pre scontract.pub (sign v.name v.code) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (relCT_alloc (R := fun _ _ => True) ?_)
  rintro _ _ t₁ t₂ s₁' s₂' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, rfl, rfl⟩ e₁ e₂
  have hp₁ := spre_of h₁
  have hp₂ := spre_of h₂
  obtain ⟨TH, Hh, sH, eH, oH, -⟩ := fns_of_tab hp₁.fH
  obtain ⟨TG, Gh, sG, eG, oG, -⟩ := fns_of_tab hp₁.fG
  have a : ∀ j < 20, stackArg s₁ j = stackArg s₂ j := fun j hj =>
    (List.map_inj_left.mp hpub.2.1) j (List.mem_range.mpr hj)
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r := hpub.1
  have rd₂ : s₂.rd = s₁.rd := by
    rw [hp₂.hrd, hp₁.hrd]
    simp only [srd, snR, seR, spR, sqR, sdpR, sdqR, sqiR, sdgR, ssaR, stabH, stabG, sargsR, stackArgAddr,
      a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
      a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
      a 12 (by decide), a 13 (by decide), a 18 (by decide), a 19 (by decide), r .rdx (by simp), r .rcx (by simp),
      r .r8 (by simp), r .r9 (by simp), r .rsp (by simp)]
  have wr₂ : s₂.wr = s₁.wr := by
    rw [hp₂.hwr, hp₁.hwr]
    simp only [soR, sscrR, a 14 (by decide), a 15 (by decide), r .rdi (by simp), r .rsi (by simp)]
  have S₁ : SSib (sselH s₁) (sselG s₁) s₁ s₁ := ⟨hp₁, sPub_refl s₁, rfl, rfl, rfl, rfl⟩
  have S₂ : SSib (sselH s₁) (sselG s₁) s₁ s₂ :=
    ⟨hp₂, hpub, by simp only [sselH, a 16 (by decide)], by simp only [sselG, a 17 (by decide)], rd₂, wr₂⟩
  exact signBody_ct oH oG sH sG eH eG hp₁.iH hp₁.iG v _ _ _ _ _ _ ⟨s₁, ⟨s₁, S₁, rfl⟩, ⟨s₂, S₂, rfl⟩⟩ e₁ e₂

/-- `vg_rsa_pss_sign`, calling the implementation `v` of
`vg_rsa_private_checked`, meets the shared contract. -/
theorem sign_verified (v : PrivImpl) :
    Verified target (sign v.name v.code) (Spec.RsaPss.signAnyContract abi decStack) :=
  Verified.of_correct (k := scontract) (sign_correct v) (sign_constantTime v) simplies

end VG.Proof.RsaPss.X86_64
