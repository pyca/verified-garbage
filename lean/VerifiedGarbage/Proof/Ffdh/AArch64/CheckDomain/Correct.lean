module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_ffdh_check_domain` on AArch64: correctness

From `cdContract`'s precondition, `CheckDomain.code` returns whether the
domain is valid (`cd_correct`), by its stages.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckDomain

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

/-- The q block's checks of its range. -/
abbrev qblk : List (Prog isa) :=
  isOdd aXm ++ [.block [sth .x9 sF]] ++ gt1 aXm ++ [.block andF] ++ ltP aXm ++ [.block andF]

/-- After `q ∣ p − 1`. -/
abbrev fin (W : Window) (M : Mont) (S : Selector) : List (Prog isa) :=
  [.block [leave]] ++ pSetup ++ r2Steps M.mm ++ pow W.code S.code M.mm sG sK sEp sEl ++ isOne aY ++
    [.block [mov .x0 .x9]]

/-- After q's range. -/
abbrev rest (W : Window) (M : Mont) (S : Selector) : List (Prog isa) :=
  [.block [leave]] ++ scan sQ ++ CheckDomain.pMinus1 ++ [.block (wsSetup sEl ++ [enter])] ++ modSetup sEp sEl ++
    Crt.redc M.mm aX ++ isZero Crt.aXc ++ [.ite (.zero .x .x9) (ret 0) (seqs (fin W M S))]

theorem withQ_eq (W : Window) (M : Mont) (S : Selector) :
    CheckDomain.withQ W.code S.code M.mm = .block [enter] :: (Crt.loadArr aXm sQ sK ++ (qblk ++
      ([.ite (.zero .x .x9) (ret 0) (seqs (rest W M S))] : List (Prog isa)))) := by
  simp only [CheckDomain.withQ, qblk, rest, fin, List.append_assoc, List.cons_append, List.nil_append]

theorem rest_eq (W : Window) (M : Mont) (S : Selector) :
    rest W M S = .block [leave] :: (scan sQ ++ (CheckDomain.pMinus1 ++
      ((([.block (wsSetup sEl ++ [enter])] : List (Prog isa)) ++ modSetup sEp sEl) ++ (Crt.redc M.mm aX ++ (isZero Crt.aXc ++
        ([.ite (.zero .x .x9) (ret 0) (seqs (fin W M S))] : List (Prog isa))))))) := by
  simp only [rest, List.append_assoc, List.cons_append, List.nil_append]

theorem fin_eq (W : Window) (M : Mont) (S : Selector) :
    fin W M S = .block [leave] :: (pSetup ++ (r2Steps M.mm ++ (pow W.code S.code M.mm sG sK sEp sEl ++
      (isOne aY ++ ([.block [mov .x0 .x9]] : List (Prog isa)))))) := by
  simp only [fin, List.append_assoc, List.cons_append, List.nil_append]

theorem main_eq (W : Window) (M : Mont) (S : Selector) :
    CheckDomain.main W.code S.code M.mm = seqs ((([.block head] : List (Prog isa)) ++ pSetup) ++ (Crt.loadArr aXm sG sK ++
      (range aXm ++ ([.ite (.zero .x .x9) (ret 0) (.seq (.block (leave :: qTest))
        (.ite (.zero .x .x3) (ret 1) (seqs (CheckDomain.withQ W.code S.code M.mm))))] : List (Prog isa))))) := by
  simp only [CheckDomain.main, List.append_assoc]

/-- The public data of a state. -/
def cdOf (s : State) : CdP :=
  ⟨s.gpr .x3, (s.gpr .x4).toNat * 8, (s.gpr .x2).toNat, (s.gpr .x1).toNat, s.gpr .x0, cdDom s, s.sp⟩

theorem cr_of (s : State) (h : cdPre s) : CR (cdOf s) s := ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A return of `r`, after which `post` holds. -/
theorem ret_post {s₀ t : State} {r : Nat} (hr : r < 65536) (hk : KX s₀ t)
    (hv : r = if domainValid (s₀.gpr .x2).toNat (cdDom s₀) then 1 else 0) :
    WP isa (ret r) t fun u => abiPreserved s₀ u ∧ cdContract.post s₀ u :=
  WP.mono (ret_ok t hr) fun u ⟨⟨h0, _⟩, k⟩ => ⟨abiPreserved_of_keep (keep_trans hk (k.mono (by decide))), by
    show ((u.gpr .x0).setWidth 32).toNat = _
    rw [h0, setWidth32_ofNat (by omega), hv]⟩

/-- `domainValid`, on the run's data. -/
theorem dv_iff {p : CdP} {t : State} (hb : Base p.D t) :
    domainValid p.D.k p.D.dom = true ↔ p.D.mv = true ∧ (1 < p.G ∧ p.G < p.P - 1) ∧
      (p.D.dl = 3 * p.D.k → (p.Q % 2 = 1 ∧ 1 < p.Q ∧ p.Q < p.P - 1) ∧ (p.P - 1) % p.Q = 0 ∧
        p.G ^ p.Q % p.P = 1) := by
  rw [domainValid_iff]
  have hq : (domainOf p.D.k p.D.dom).q = if p.D.dl = 3 * p.D.k then some p.Q else none := by
    simp only [domainOf, hb.doml]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun e => h3 _ (by rw [hq, ite_eq_left e])⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun q e => ?_⟩
    rw [hq] at e
    by_cases e3 : p.D.dl = 3 * p.D.k
    · rw [ite_eq_left e3, Option.some.injEq] at e
      subst e
      exact h3 e3
    · rw [ite_eq_right e3] at e; exact absurd e (by simp)

theorem bit_false {P : Prop} [Decidable P] (h : (bit P == 0) = true) : ¬ P := by
  intro hp; simp [bit, hp] at h

/-- `vg_ffdh_check_domain`. -/
theorem cd_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : cdContract.pre s) :
    ∃ t s', Exec isa (CheckDomain.code W.code S.code M.mm) s t s' ∧ abiPreserved s s' ∧
      cdContract.post s s' := by
  suffices hwp : WP isa (CheckDomain.code W.code S.code M.mm) s fun s' =>
      abiPreserved s s' ∧ cdContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hCR := cr_of s h
  have hval : domainValid (s.gpr .x2).toNat (cdDom s) = domainValid (cdOf s).D.k (cdOf s).D.dom := rfl
  generalize cdOf s = p at hCR hval
  have hb₀ := cr_base p s hCR
  have hdv := dv_iff hb₀
  unfold CheckDomain.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cr_e1 p s hCR) fun t₁ ⟨e1, k₁⟩ => ?_
  refine kstep k₁ (e1_ce _ _ e1) fun t₂ ce k₂ => ?_
  refine WP.ite (BitVec.ofNat 64 p.D.mv.toNat == 0) (ce_eval ce) (fun hb => ?_) (fun hb => ?_)
  · -- p is not a valid modulus.
    refine ret_post (by decide) k₂ ?_
    have hm : p.D.mv = false := by cases hm' : p.D.mv <;> simp_all
    rw [hval, ite_eq_right fun hv => absurd ((hdv.mp hv).1) (by rw [hm]; decide)]
  have he : isa.eval (.zero .x .x9) t₂ = some false := by rw [ce_eval ce, hb]
  have hm := ce_valid ce he
  have hodd := (valid_facts hm hb₀.k1).1
  rw [main_eq]
  -- The workspaces, g and its range.
  refine wp_seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (kstep k₂ (ce_in _ _ ce he) fun t₃ h₃ k₃ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp) (kstep k₃ (s1_s2 p t₃ h₃) fun t₄ h₄ k₄ => ?_)
  refine wp_seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp) (kstep k₄ (s2_s3 p t₄ h₄)
    fun t₅ h₅ k₅ => ?_)
  rw [seqs_one]
  refine WP.ite (bit p.rg == 0) (s3_eval h₅) (fun hb => ?_) (fun hb => ?_)
  · -- g out of range.
    refine ret_post (by decide) k₅ ?_
    have hr := bit_false hb
    rw [hval, ite_eq_right fun hv => hr ⟨(hdv.mp hv).2.1.1, (lt_pm1 hodd _).mpr (hdv.mp hv).2.1.2⟩]
  have hr : p.rg := bit_ne hb
  have hg : 1 < p.G ∧ p.G < p.P - 1 := ⟨hr.1, (lt_pm1 hodd _).mp hr.2⟩
  refine WP.seq (kstep k₅ (s3_s4 p t₅ h₅) fun t₆ h₆ k₆ => ?_)
  refine WP.ite (BitVec.ofNat 64 (p.D.dl - 2 * p.D.k) == 0) (s4_eval h₆) (fun hb => ?_) (fun hb => ?_)
  · -- No q.
    refine ret_post (by decide) k₆ ?_
    have h2 := hb₀.noq hb
    have := hb₀.k1
    rw [hval, ite_eq_left (hdv.mpr ⟨hm, hg, fun e => absurd (e.symm.trans h2) (by omega)⟩)]
  -- With q.
  have hq := hb₀.q hb
  rw [withQ_eq]
  refine wp_seqs_cons (by simp [Crt.loadArr]) (kstep k₆ (s4_q0 p t₆ h₆ (by rw [s4_eval h₆, hb]))
    fun t₇ h₇ k₇ => ?_)
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp) (kstep k₇ (q0_q1 p t₇ h₇) fun t₈ h₈ k₈ => ?_)
  refine wp_seqs_append (by simp [isOdd]) (by simp) (kstep k₈ (q1_q2 p t₈ h₈) fun t₉ h₉ k₉ => ?_)
  rw [seqs_one]
  refine WP.ite (bit p.qr == 0) (q2_eval h₉) (fun hb => ?_) (fun hb => ?_)
  · -- q out of range.
    refine ret_post (by decide) k₉ ?_
    have hr := bit_false hb
    rw [hval, ite_eq_right fun hv => by
      obtain ⟨⟨o, l, u⟩, -⟩ := (hdv.mp hv).2.2 hq
      exact hr ⟨o, l, (lt_pm1 hodd _).mpr u⟩]
  have hqr : p.qr := bit_ne hb
  rw [rest_eq]
  refine wp_seqs_cons (by simp [scan]) (kstep k₉ (q2_q3 p t₉ h₉ (by rw [q2_eval h₉, hb])) fun t₁₀ h₁₀ k₁₀ => ?_)
  refine wp_seqs_append (by simp [scan]) (by simp [CheckDomain.pMinus1]) (kstep k₁₀ (q3_q4 p t₁₀ h₁₀)
    fun t₁₁ h₁₁ k₁₁ => ?_)
  refine wp_seqs_append (by simp [CheckDomain.pMinus1]) (by simp) (kstep k₁₁ (q4_q5 p t₁₁ h₁₁)
    fun t₁₂ h₁₂ k₁₂ => ?_)
  refine wp_seqs_append (by simp) (by simp [Crt.redc]) (kstep k₁₂ (q5_q6 p t₁₂ h₁₂) fun t₁₃ h₁₃ k₁₃ => ?_)
  refine wp_seqs_append (by simp [Crt.redc]) (by simp) (kstep k₁₃ (q6_q7 M p t₁₃ h₁₃) fun t₁₄ h₁₄ k₁₄ => ?_)
  refine wp_seqs_append (by simp [isZero, ltArr, cmpArr]) (by simp) (kstep k₁₄ (q7_q8 p t₁₄ h₁₄)
    fun t₁₅ h₁₅ k₁₅ => ?_)
  rw [seqs_one]
  refine WP.ite (bit ((p.P - 1) % p.Q = 0) == 0) (q8_eval h₁₅) (fun hb => ?_) (fun hb => ?_)
  · -- q does not divide p − 1.
    refine ret_post (by decide) k₁₅ ?_
    have hr := bit_false hb
    rw [hval, ite_eq_right fun hv => hr ((hdv.mp hv).2.2 hq).2.1]
  rw [fin_eq]
  refine wp_seqs_cons (by simp [pSetup]) (kstep k₁₅ (q8_q9 p t₁₅ h₁₅ (by rw [q8_eval h₁₅, hb]))
    fun t₁₆ h₁₆ k₁₆ => ?_)
  refine wp_seqs_append (by simp [pSetup]) (by simp [r2Steps]) (kstep k₁₆ (q9_q10 p t₁₆ h₁₆)
    fun t₁₇ h₁₇ k₁₇ => ?_)
  refine wp_seqs_append (by simp [r2Steps]) (by simp [pow]) (kstep k₁₇ (q10_q11 M p t₁₇ h₁₇)
    fun t₁₈ h₁₈ k₁₈ => ?_)
  refine wp_seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (kstep k₁₈ (q11_q12 W M S p t₁₈ h₁₈)
    fun t₁₉ h₁₉ k₁₉ => ?_)
  refine wp_seqs_append (by simp [isOne, eqArr]) (by simp) (kstep k₁₉ (q12_q13 p t₁₉ h₁₉)
    fun t₂₀ h₂₀ k₂₀ => ?_)
  rw [seqs_one]
  refine WP.mono (WP.keep [.x0] (c := .block [mov .x0 .x9]) (Q := fun t => t.gpr .x0 = t₂₀.gpr .x9) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h0, k⟩ =>
      ⟨abiPreserved_of_keep (keep_trans k₂₀ (k.mono (by decide))), ?_⟩
  show ((t.gpr .x0).setWidth 32).toNat = _
  have hd : (p.P - 1) % p.Q = 0 := bit_ne hb
  rw [h0, h₂₀, setWidth32_bit, hval]
  by_cases hgq : p.G ^ p.Q % p.P = 1
  · rw [ite_eq_left hgq, ite_eq_left (hdv.mpr ⟨hm, hg, fun _ => ⟨⟨hqr.1, hqr.2.1, (lt_pm1 hodd _).mp hqr.2.2⟩, hd, hgq⟩⟩)]
  · rw [ite_eq_right hgq, ite_eq_right fun hv => hgq ((hdv.mp hv).2.2 hq).2.2]

end VG.Proof.Ffdh.AArch64.CheckDomain
