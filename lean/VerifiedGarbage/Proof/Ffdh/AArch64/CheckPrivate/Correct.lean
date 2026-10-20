module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_ffdh_check_private` on AArch64: correctness

From `kpContract`'s precondition, `CheckPrivate.code` returns the status
(`kp_correct`), by its stages.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

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

/-- The final part. -/
abbrev fin (W : Window) (M : Mont) (S : Selector) : List (Prog isa) :=
  pow W.code S.code M.mm sG sK sX sXl ++ Crt.loadArr aXm sY sK ++ eqArr aY aXm ++ [.block [mov .x0 .x9]]

theorem tail_eq (W : Window) (M : Mont) (S : Selector) :
    CheckPrivate.tail W.code S.code M.mm = r2Steps M.mm ++ (.block [leave] :: .block qTest ::
      [.ite (.zero .x .x3) (.block [enter, movi .x9 1])
        (seqs (scan sQ ++ ([.block [enter]] : List (Prog isa)) ++ pow W.code S.code M.mm sY sK sEp sEl ++ isOne aY)),
       .ite (.zero .x .x9) (ret 0) (seqs (fin W M S))]) := rfl

theorem scalarRange_eq : CheckPrivate.scalarRange = isNonzero aXm ++ (.block [sth .x9 sF, leave] ::
    .block qTest :: [.ite (.zero .x .x3) (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY)), .block andF]) := rfl

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    CheckPrivate.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++ (Crt.loadArr aXm sX sXl ++
      (CheckPrivate.scalarRange ++ ([.ite (.zero .x .x9) (ret 2) (seqs (Crt.loadArr aXm sY sK ++ (range aXm ++
        ([.ite (.zero .x .x9) (ret 0) (seqs (CheckPrivate.tail W.code S.code M.mm))] : List (Prog isa)))))] : List (Prog isa))))) := by
  simp only [CheckPrivate.main, List.append_assoc]

/-- The public data of a state. -/
def kpOf (s : State) : KpP :=
  ⟨s.gpr .x7, (stackArg s 0).toNat * 8, (s.gpr .x2).toNat, (s.gpr .x1).toNat, s.gpr .x0, kpDom s, s.gpr .x3,
    kpY s, s.gpr .x5, (s.gpr .x6).toNat,
    privateValid (domainOf (s.gpr .x2).toNat (kpDom s)) (Spec.Rsa.os2ip (kpX s)), s.sp⟩

theorem cr_of (s : State) (h : kpPre s) : CR (kpOf s) (kpX s) s :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A return of `r`, after which `post` holds. -/
theorem ret_post {s₀ t : State} {r : Nat} (hr : r < 65536) (hk : KX s₀ t)
    (hv : domainValid (s₀.gpr .x2).toNat (kpDom s₀) → r = privateStatus (domainOf (s₀.gpr .x2).toNat (kpDom s₀))
      (Spec.Rsa.os2ip (kpY s₀)) (Spec.Rsa.os2ip (kpX s₀))) :
    WP isa (ret r) t fun u => abiPreserved s₀ u ∧ kpContract.post s₀ u :=
  WP.mono (ret_ok t hr) fun u ⟨⟨h0, _⟩, k⟩ => ⟨abiPreserved_of_keep (keep_trans hk (k.mono (by decide))), fun hd => by
    show ((u.gpr .x0).setWidth 32).toNat = _
    rw [h0, setWidth32_ofNat (by omega), hv hd]⟩

theorem bit_true {t : State} {P : Prop} [Decidable P] (h : isa.eval (.zero .x .x9) t = some (bit P == 0))
    (he : isa.eval (.zero .x .x9) t = some false) : P := by
  rw [h] at he
  by_contra hc
  simp [bit, hc] at he

theorem bit_false' {t : State} {P : Prop} [Decidable P] (h : isa.eval (.zero .x .x9) t = some (bit P == 0))
    (he : isa.eval (.zero .x .x9) t = some true) : ¬ P := by
  rw [h] at he
  intro hp
  simp [bit, hp] at he

/-- x's bound. -/
theorem k5_k6 (p : KpP) (xb : List Byte) (t : State) (h : K5 p xb t) :
    WP isa (.ite (.zero .x .x3) (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ Crt.loadArr aY sQ sK ++ ltArr aXm aY))) t fun u => K6 p xb u ∧ KX t u :=
  WP.ite (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) (k5_eval h) (fun hb => k5_k6n p xb t h (by rw [k5_eval h, hb]))
    (fun hb => k5_k6q p xb t h (by rw [k5_eval h, hb]))

/-- y's subgroup. -/
theorem k12_k13 (W : Window) (M : Mont) (S : Selector) (p : KpP) (xb : List Byte) (t : State) (h : K12 p xb t) :
    WP isa (.ite (.zero .x .x3) (.block [enter, movi .x9 1])
      (seqs (scan sQ ++ ([.block [enter]] : List (Prog isa)) ++ pow W.code S.code M.mm sY sK sEp sEl ++ isOne aY))) t
      fun u => K13 p xb u ∧ KX t u :=
  WP.ite (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) (k12_eval h) (fun hb => k12_k13n p xb t h (by rw [k12_eval h, hb]))
    (fun hb => k12_k13q W M S p xb t h (by rw [k12_eval h, hb]))

/-- `vg_ffdh_check_private`. -/
theorem kp_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : kpContract.pre s) :
    ∃ t s', Exec isa (CheckPrivate.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      kpContract.post s s' := by
  suffices hwp : WP isa (CheckPrivate.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ kpContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  have hok := cr_ok hCR
  have hst : ∀ r, (domainValid (s.gpr .x2).toNat (kpDom s) → r = privateStatus (domainOf (s.gpr .x2).toNat (kpDom s))
      (Spec.Rsa.os2ip (kpY s)) (Spec.Rsa.os2ip (kpX s))) ↔ (domainValid (kpOf s).k (kpOf s).dom →
      r = privateStatus (kpOf s).a (kpOf s).Y (X (kpX s))) := fun r => Iff.rfl
  have hpv : (kpOf s).pv = privateValid (kpOf s).a (X (kpX s)) := rfl
  generalize kpOf s = p at hCR hok hst hpv
  generalize hxb : kpX s = xb at hCR hok hpv
  have hb₀ := cr_base p xb s hCR
  unfold CheckPrivate.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_e1 p xb s hCR) fun t₁ ⟨e1, k₁⟩ => ?_
  refine kstep k₁ (e1_ce _ _ e1) fun t₂ ce k₂ => ?_
  refine WP.ite (BitVec.ofNat 64 (p.D xb).mv.toNat == 0) (ce_eval ce) (fun hb => ?_) (fun hb => ?_)
  · refine ret_post (by decide) k₂ ((hst 0).mpr fun hd => ?_)
    rw [hxb] at *
    have := domainValid_mod hd
    have hm : (p.D xb).mv = false := by cases hm' : (p.D xb).mv <;> simp_all
    exact absurd this (by show ¬ (p.D xb).mv = true; rw [hm]; decide)
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval ce, hb]
  have hm := ce_valid ce he
  have hodd := (valid_facts hm hb₀.k1).1
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (kstep k₂ (ce_in _ _ ce he) fun t₃ h₃ k₃ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange]) (kstep k₃ (k1_k2 p xb t₃
    ⟨h₃, hok⟩) fun t₄ h₄ k₄ => ?_)
  rw [scalarRange_eq, List.append_assoc]
  refine wp_seqs_append (by simp [isNonzero, geArr, cmpArr]) (by simp) (kstep k₄ (k2_k3 p xb t₄ h₄)
    fun t₅ h₅ k₅ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₅ (k3_k4 p xb t₅ h₅) fun t₆ h₆ k₆ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₆ (k4_k5 p xb t₆ h₆) fun t₇ h₇ k₇ => ?_)
  simp only [List.cons_append]
  refine wp_seqs_cons (by simp) (kstep k₇ (k5_k6 p xb t₇ h₇) fun t₈ h₈ k₈ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₈ (k6_k7 p xb t₈ h₈) fun t₉ h₉ k₉ => ?_)
  simp only [List.append_eq, List.nil_append]
  rw [seqs_one]
  refine WP.ite (bit (p.pv = true) == 0) (k7_eval h₉) (fun hb => ?_) (fun hb => ?_)
  · -- x out of range.
    refine ret_post (by decide) k₉ ((hst 2).mpr fun hd => ?_)
    have hn := bit_false' (k7_eval h₉) (by rw [k7_eval h₉, hb])
    rw [privateStatus_eq (by unfold domainValid at hd; simp only [Bool.and_eq_true] at hd; exact hd.1),
      ite_eq_left (by rw [hxb, ← hpv]; simpa using hn)]
  have he₉ : isa.eval (.zero .x .x9) t₉ = some false := by rw [k7_eval h₉, hb]
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [range]) (kstep k₉ (k7_k8 p xb t₉ h₉ he₉)
    fun t₁₀ h₁₀ k₁₀ => ?_)
  refine wp_seqs_append (by simp [range]) (by simp) (kstep k₁₀ (k8_k9 p xb t₁₀ h₁₀) fun t₁₁ h₁₁ k₁₁ => ?_)
  rw [seqs_one]
  have hpvT : p.pv = true := h₁₀.2.2
  have hpvX : privateValid p.a (X xb) = true := by rw [← hpv]; exact hpvT
  have hpf : ∀ hd : domainValid p.k p.dom = true, privateStatus p.a p.Y (X xb) =
      if publicValid ⟨p.a, p.Y⟩ = true ∧ p.a.g ^ X xb % p.a.p = p.Y then 1 else 0 := fun hd => by
    rw [privateStatus_eq (by unfold domainValid at hd; simp only [Bool.and_eq_true] at hd; exact hd.1),
      ite_eq_right (by simp [hpvX])]
  refine WP.ite (bit (p.rg xb) == 0) (k9_eval h₁₁) (fun hb => ?_) (fun hb => ?_)
  · -- y out of range.
    refine ret_post (by decide) k₁₁ ((hst 0).mpr fun hd => ?_)
    have hn := bit_false' (k9_eval h₁₁) (by rw [k9_eval h₁₁, hb])
    rw [hxb, hpf hd, ite_eq_right fun ⟨hv, _⟩ => hn ⟨((publicValid_eq _ _).mp hv).1.1,
      (lt_pm1 hodd _).mpr ((publicValid_eq _ _).mp hv).1.2⟩]
  have he₁₁ : isa.eval (.zero .x .x9) t₁₁ = some false := by rw [k9_eval h₁₁, hb]
  rw [tail_eq]
  refine wp_seqs_append (by simp [r2Steps]) (by simp) (kstep k₁₁ (k9_k10 M p xb t₁₁ h₁₁ he₁₁) fun t₁₂ h₁₂ k₁₂ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₁₂ (k10_k11 p xb t₁₂ h₁₂) fun t₁₃ h₁₃ k₁₃ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₁₃ (k11_k12 p xb t₁₃ h₁₃) fun t₁₄ h₁₄ k₁₄ => ?_)
  refine wp_seqs_cons (by simp) (kstep k₁₄ (k12_k13 W M S p xb t₁₄ h₁₄) fun t₁₅ h₁₅ k₁₅ => ?_)
  rw [seqs_one]
  refine WP.ite (bit (p.qc xb) == 0) (k13_eval h₁₅) (fun hb => ?_) (fun hb => ?_)
  · -- y not in the subgroup.
    refine ret_post (by decide) k₁₅ ((hst 0).mpr fun hd => ?_)
    have hn := bit_false' (k13_eval h₁₅) (by rw [k13_eval h₁₅, hb])
    have hdl : p.dom.length = p.dl := hb₀.doml
    rw [hxb, hpf hd, ite_eq_right fun ⟨hv, _⟩ => hn fun hq => ((publicValid_eq _ _).mp hv).2 _ (by
      simp only [KpP.a, domainOf, hdl]; rw [ite_eq_left hq]; rfl)]
  have he₁₅ : isa.eval (.zero .x .x9) t₁₅ = some false := by rw [k13_eval h₁₅, hb]
  simp only [fin, List.append_assoc]
  refine wp_seqs_append (by simp [pow]) (by simp [Crt.loadArr]) (kstep k₁₅ (k13_k14 W M S p xb t₁₅ h₁₅ he₁₅)
    fun t₁₆ h₁₆ k₁₆ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [eqArr]) (kstep k₁₆ (k14_k15 p xb t₁₆ h₁₆)
    fun t₁₇ h₁₇ k₁₇ => ?_)
  refine wp_seqs_append (by simp [eqArr]) (by simp) (kstep k₁₇ (k15_k16 p xb t₁₇ h₁₇) fun t₁₈ h₁₈ k₁₈ => ?_)
  rw [seqs_one]
  refine WP.mono (WP.keep [.x0] (c := .block [mov .x0 .x9]) (Q := fun t => t.gpr .x0 = t₁₈.gpr .x9) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h0, k⟩ =>
      ⟨abiPreserved_of_keep (keep_trans k₁₈ (k.mono (by decide))), fun hd => ?_⟩
  show ((t.gpr .x0).setWidth 32).toNat = _
  obtain ⟨h9, -, -, hr, hqc⟩ := h₁₈
  refine (hst _).mpr (fun hd' => ?_) hd
  have hpub : publicValid ⟨p.a, p.Y⟩ = true := (publicValid_eq _ _).mpr ⟨⟨hr.1, (lt_pm1 hodd _).mp hr.2⟩,
    fun q hq => by
      have hdl : p.dom.length = p.dl := hb₀.doml
      simp only [KpP.a, domainOf, hdl] at hq
      by_cases e : p.dl = 3 * p.k
      · rw [ite_eq_left e, Option.some.injEq] at hq
        subst hq
        exact hqc e
      · rw [ite_eq_right e] at hq; exact absurd hq (by simp)⟩
  rw [h0, h9, setWidth32_bit, hxb, hpf hd']
  by_cases hc : (p.D xb).G ^ X xb % (p.D xb).P = p.Y
  · rw [ite_eq_left hc, ite_eq_left ⟨hpub, hc⟩]
  · rw [ite_eq_right hc, ite_eq_right fun ⟨_, h'⟩ => hc h']

end VG.Proof.Ffdh.AArch64.CheckPrivate
