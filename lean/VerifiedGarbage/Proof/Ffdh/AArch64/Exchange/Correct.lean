module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_ffdh_exchange` on AArch64: correctness

From `exContract`'s precondition, `Exchange.code` writes the shared value or
zeros and returns its flag (`ex_correct`), by its stages.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Ffdh

/-- A step that keeps the caller's registers. -/
theorem kstep {s₀ t : State} {c : Prog isa} {P Q : State → Prop} (hk : KX s₀ t)
    (h : WP isa c t fun u => P u ∧ KX t u) (k : ∀ u, P u → KX s₀ u → Q u) : WP isa c t Q :=
  WP.mono h fun u ⟨hp, k'⟩ => k u hp (keep_trans hk k')

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    Exchange.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++ (r2Steps M.mm ++
      (pow W.code S.code M.mm sY sK sX sXl ++ (range aY ++ ([.block finBlk, storeBE, .block [ldh .x0 sF]] : List (Prog isa)))))) := by
  simp only [Exchange.main, List.append_assoc]

/-- The public data of a state. -/
def exOf (s : State) : ExP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .x4).toNat, (s.gpr .x3).toNat, s.gpr .x2, exDom s, s.gpr .x0,
    s.gpr .x5, (s.gpr .x6).toNat, s.gpr .x7, exY s, s.sp⟩

theorem cr_of (s : State) (h : exPre s) : CR (exOf s) (exX s) s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `vg_ffdh_exchange`. -/
theorem ex_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : exContract.pre s) :
    ∃ t s', Exec isa (Exchange.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      exContract.post s s' := by
  suffices hwp : WP isa (Exchange.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ exContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  have hok := cr_ok hCR
  have hpost : ∀ t : State, exContract.post s t ↔ (domainValid (exOf s).k (exOf s).dom →
      publicValid ⟨domainOf (exOf s).k (exOf s).dom, Spec.Rsa.os2ip (exOf s).yb⟩ →
      Spec.Rsa.written t.mem (exOf s).op (exOf s).k ((t.gpr .x0).setWidth 32)
        (exchangeOp (domainOf (exOf s).k (exOf s).dom) (Spec.Rsa.os2ip (exX s)) (Spec.Rsa.os2ip (exOf s).yb))) := by
    intro t
    show exPost s t ↔ _
    unfold exPost
    rw [show (s.gpr .x1).toNat = (exOf s).k from (exCtx_of h).ol]
    exact Iff.rfl
  simp only [hpost]
  generalize exOf s = p at hCR hok
  generalize exX s = xb at hCR hok
  have hb₀ := cr_base p xb s hCR
  unfold Exchange.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_e1 p xb s hCR) fun t₁ ⟨⟨e1, hd₁⟩, k₁⟩ => ?_
  refine kstep k₁ (e1_ce _ _ e1) fun t₂ ce k₂ => ?_
  refine WP.ite (BitVec.ofNat 64 (p.D xb).mv.toNat == 0) (ce_eval ce) (fun hb => ?_) (fun hb => ?_)
  · -- p is not a valid modulus.
    refine WP.mono (ret_ok t₂ (by decide)) fun u ⟨_, k⟩ =>
      ⟨abiPreserved_of_keep (keep_trans k₂ (k.mono (by decide))), fun hv => ?_⟩
    have hm : (p.D xb).mv = false := by cases hm' : (p.D xb).mv <;> simp_all
    have := domainValid_mod hv
    exact absurd this (by show ¬ (p.D xb).mv = true; rw [hm]; decide)
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval ce, hb]
  have hm := ce_valid ce he
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp [r2Steps]) (kstep k₂ (ce_in _ _ ce he) fun t₃ h₃ k₃ => ?_)
  refine wp_seqs_append (by simp [r2Steps]) (by simp [pow]) (kstep k₃ (x1_x2 M p xb t₃ ⟨h₃, (cr_dst p xb s hCR).keep k₃,
    hok⟩) fun t₄ h₄ k₄ => ?_)
  refine wp_seqs_append (by simp [pow]) (by simp [range]) (kstep k₄ (x2_x3 W M S p xb t₄ h₄) fun t₅ h₅ k₅ => ?_)
  refine wp_seqs_append (by simp [range]) (by simp) (kstep k₅ (x3_x4 p xb t₅ h₅) fun t₆ h₆ k₆ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₆ (x4_x5 p xb t₆ h₆) fun t₇ h₇ k₇ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₇ (x5_x6 p xb t₇ h₇) fun t₈ h₈ k₈ => ?_)
  rw [seqs_one]
  refine kstep k₈ (x6_x7 p xb t₈ h₈) fun t ⟨hbytes, h0⟩ k => ⟨abiPreserved_of_keep k, fun hv hpv => ?_⟩
  -- The value written.
  have hp1 := (valid_facts hm hb₀.k1)
  have hlo : 256 ^ (p.k - 1) ≤ (p.D xb).P := by
    have := hm
    unfold FD.mv Spec.Rsa.modulusValid at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hhi : (p.D xb).P < 256 ^ p.k := by
    have := os2ip_lt ((p.D xb).dom.take (p.D xb).k)
    rw [hb₀.plen] at this
    exact this
  have hk := octets_bitLength (by have := hb₀.k1; simp at this; omega) hlo hhi
  rw [exchangeOp_eq hpv (by have := hp1.2.1; exact Nat.lt_trans (by decide) this) hk, h0]
  have hP : (domainOf p.k p.dom).p = (p.D xb).P := rfl
  have hfl : fl p xb ↔ (1 < zv p xb ∧ zv p xb < (p.D xb).P - 1) :=
    ⟨fun ⟨a, b⟩ => ⟨a, (lt_pm1 hp1.1 _).mp b⟩, fun ⟨a, b⟩ => ⟨a, (lt_pm1 hp1.1 _).mpr b⟩⟩
  rw [hP]
  by_cases hc : 1 < zv p xb ∧ zv p xb < (p.D xb).P - 1
  · rw [ite_eq_left hc]
    exact ⟨by unfold bit; rw [ite_eq_left (hfl.mpr hc)]; rfl, by rw [hbytes, ite_eq_left (hfl.mpr hc)]⟩
  · rw [ite_eq_right hc]
    exact ⟨by unfold bit; rw [ite_eq_right (mt hfl.mp hc)]; rfl,
      by rw [hbytes, ite_eq_right (mt hfl.mp hc), i2osp_zero']⟩

end VG.Proof.Ffdh.AArch64.Exchange
