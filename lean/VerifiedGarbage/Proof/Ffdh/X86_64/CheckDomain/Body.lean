module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Context
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Ffdh.X86_64.CheckDomain.Main`, which only this module used -/

section

/-! # FFDH domain validation on x86-64: the main computation -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckDomain/WithQ.lean`, which only this module imported.
section

/-! # FFDH domain validation on x86-64: the optional subgroup order -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem bit_and_left {P Q : Prop} [Decidable P] [Decidable Q] (hp : P) : bit Q = bit (P ∧ Q) := by
  by_cases hq : Q <;> simp [bit, hp, hq]

abbrev CdP.relation (p : CdP) : Prop := p.qr ∧ (p.P - 1) % p.Q = 0 ∧ p.G ^ p.Q % p.P = 1

private theorem withQ_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code) =
      .block [enter] :: (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange ++
        ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ, List.cons_append, List.nil_append]

theorem withQ_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = p.B) (hm : p.mv = true) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code))) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = bit p.relation) := by
  rw [withQ_eq]
  refine wp_seqs_cons (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (h.enter hd) fun u ⟨hw, hdi, hm', k⟩ => ?_)
  have S₁ : StepPost p s (fun _ => True) u := ⟨trivial, by rw [hm']; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hm']), k.mono (by decide)⟩
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (WP.mono (order_range hw hdi hq) fun v S₂ => ?_)
  have H := S₁.trans S₂
  obtain ⟨hw', hd', hz⟩ := S₂.1
  simp only [seqs]
  refine WP.ite (!decide p.qr) (by simp [eval, hz]) (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬p.qr := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hn)
    refine WP.mono (ret_inner (hw'.mem.ctx hd') (r := 0) (by decide)) fun t ⟨hdi, ha, hmem, kk⟩ => ?_
    exact ⟨⟨hdi, by simpa [bit, CdP.relation, hn'] using ha⟩, by rw [hmem]; exact H.2.1,
      (fun i hi => by rw [hmem]; exact H.2.2.1 i hi), keep_trans H.2.2.2 (kk.mono (by decide))⟩
  · have hy' : p.qr := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hy)
    exact WP.mono (divides_ok M E R hw' hd' hm hq hy'.1 hy'.2.1) fun t S₃ =>
      ⟨⟨S₃.1.1, S₃.1.2.trans (bit_and_left hy')⟩, (H.trans S₃).2⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave loadArr)

private theorem bit_true {P : Prop} [Decidable P] (hp : P) : bit P = 1 := by
  simp only [bit, ite_eq_left hp]

abbrev CdP.accept (p : CdP) : Prop := p.gr ∧ (p.dl = 2 * p.k ∨ p.relation)

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++ (loadArr aXm sG sK ++
        (rangeTest aXm ++ ([.ite .e (retInner 0) (.seq (.block (leave :: qTest))
          (.ite .e (ret 1) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code)))))] : List (Prog isa))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main, List.append_assoc]

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : CdP} {s : State}
    (h : Base p s) (hd : s.gpr .rdi = p.B) (hG : word s.mem p.B (8 * sG) = off p.dp p.k)
    (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)) (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = bit p.accept) := by
  rw [main_eq]
  refine wp_seqs_append (a := ([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)
    (b := loadArr aXm sG sK ++ (rangeTest aXm ++ ([.ite .e (retInner 0) (.seq (.block (leave :: qTest))
      (.ite .e (ret 1) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code)))))] : List (Prog isa))))
    (by simp) (by simp [loadArr])
    (WP.mono (setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := loadArr aXm sG sK) (by simp [loadArr]) (by simp [rangeTest])
    (WP.mono (load_generator hw₁ hd₁) fun u₂ S₂ => ?_)
  refine wp_seqs_append (a := rangeTest aXm) (by simp [rangeTest, range, gt1, ltArr, cmpArr]) (by simp)
    (WP.mono (generator_range S₂.1.1 S₂.1.2.1 S₂.1.2.2) fun u₃ S₃ => ?_)
  have H := (S₁.trans S₂).trans S₃
  obtain ⟨hw₃, hd₃, hz₃⟩ := S₃.1
  simp only [seqs]
  refine WP.ite (!decide p.gr) (by simp [eval, hz₃]) (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬p.gr := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hn)
    exact WP.mono (ret_inner (hw₃.mem.ctx hd₃) (r := 0) (by decide)) fun t ⟨hdi, ha, hmem, k⟩ =>
      ⟨⟨hdi, by simpa [bit, CdP.accept, hn'] using ha⟩, by rw [hmem]; exact H.2.1,
        (fun i hi => by rw [hmem]; exact H.2.2.1 i hi), keep_trans H.2.2.2 (k.mono (by decide))⟩
  · have hy' : p.gr := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hy)
    have hb₃ := hw₃.base
    have hk := hb₃.k1
    have hk' := hb₃.k2
    have hdl := hb₃.dl
    refine WP.seq (WP.mono (leaveQ_ok (hw₃.mem.ctx hd₃)
      (hb₃.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [CdP.headers]))
      (hb₃.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
      (by rcases hdl with h | h <;> omega_using [h]) (by rcases hdl with h | h <;> omega_using [hk', h]))
      fun u₄ ⟨hd₄, _, hz₄, hm₄, k₄⟩ => ?_)
    have hw₄ := hw₃.keep hm₄ k₄
    have H₄ : StepPost p s (fun _ => True) u₄ := ⟨trivial,
      by rw [hm₄]; exact H.2.1, (fun i hi => by rw [hm₄]; exact H.2.2.1 i hi),
      keep_trans H.2.2.2 (k₄.mono (by decide))⟩
    refine WP.ite (decide (p.dl = 2 * p.k)) (by simp [eval, hz₄]) (fun hq => ?_) (fun hq => ?_)
    · have hq' := of_decide_eq_true hq
      exact WP.mono (ret_ok u₄ (r := 1) (by decide)) fun t ⟨ha, hm', k⟩ =>
        ⟨⟨(k.gpr (by decide)).trans hd₄, ha.trans (bit_true (show p.accept from ⟨hy', Or.inl hq'⟩)).symm⟩,
          by rw [hm']; exact H₄.2.1,
          (fun i hi => by rw [hm']; exact H₄.2.2.1 i hi), keep_trans H₄.2.2.2 (k.mono (by decide))⟩
    · have hn' := of_decide_eq_false hq
      have hq' : p.dl = 3 * p.k := by rcases hdl with h | h <;> omega_arith
      refine WP.mono (withQ_ok M E R hw₄ hd₄ hm hq') fun t S₅ => ?_
      have he : p.relation = p.accept := propext (by simp only [CdP.accept]; grind)
      exact ⟨⟨S₅.1.1, by simpa only [bit, he] using S₅.1.2⟩, (H₄.trans S₅).2⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: complete body correctness -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckDomain/Math.lean`, which only this module imported.
section

/-! # FFDH domain validation on x86-64: relation to the specification -/

section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem Base.params_none {p : CdP} {s : State} (h : Base p s)
    (hd : p.dl = 2 * p.k) : p.params.q = none := by
  change (if p.dom.length = 3 * p.k then some p.Q else none) = none
  have hk := h.k1
  rw [h.doml, hd, ite_eq_right (by omega)]

theorem Base.params_some {p : CdP} {s : State} (h : Base p s)
    (hd : p.dl = 3 * p.k) : p.params.q = some p.Q := by
  change (if p.dom.length = 3 * p.k then some p.Q else none) = some p.Q
  rw [h.doml, hd, ite_eq_left rfl]

theorem accept_valid {p : CdP} {s : State} (h : Base p s) (hm : p.mv = true) :
    p.accept ↔ Spec.Ffdh.domainValid p.k p.dom = true := by
  have ho := (valid_facts hm h.k1).1
  have hv := domainValid_iff p.k p.dom
  change Spec.Ffdh.domainValid p.k p.dom = true ↔ (p.mv = true ∧
    (1 < p.G ∧ p.G < p.P - 1) ∧ ∀ q, p.params.q = some q →
      (q % 2 = 1 ∧ 1 < q ∧ q < p.P - 1) ∧ (p.P - 1) % q = 0 ∧ p.G ^ q % p.P = 1) at hv
  rw [hv]
  simp only [hm, true_and]
  have heG := lt_pm1 ho p.G
  have heQ := lt_pm1 ho p.Q
  rcases h.dl with hd | hd
  · have hq := h.params_none hd
    simp only [CdP.accept, CdP.gr, hd, true_or, and_true, hq, reduceCtorEq, false_implies, implies_true]
    exact and_congr_right (fun _ => heG)
  · have hq := h.params_some hd
    have hk := h.k1
    have hn : ¬p.dl = 2 * p.k := by omega
    simp only [CdP.accept, hn, false_or, CdP.relation, CdP.gr, CdP.qr, hq, Option.some.injEq, forall_eq']
    rw [heG, heQ]

theorem invalid_modulus {p : CdP} (hm : p.mv = false) : Spec.Ffdh.domainValid p.k p.dom = false := by
  cases hv : Spec.Ffdh.domainValid p.k p.dom with
  | false => rfl
  | true =>
    have he : p.mv = true := domainValid_mod hv
    rw [hm] at he
    contradiction

end VG.Proof.Ffdh.X86_64.CheckDomain
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem bit_bool (b : Bool) : ((bit (b = true)).setWidth 32).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem cd_body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (c : CdCtx s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      cdPost s t ∧ t.gpr .rdi = (cdOf s).B ∧ InScr (cdOf s).B (cdOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (cdOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u₁ ⟨hb₁, hd₁, hi₁, hs₁, k₁⟩ => ?_
  refine WP.mono (dom_base hb₁ hd₁) fun u₂ ⟨hb₂, hz₂, hd₂, hG, hQ, hi₂, hs₂, k₂⟩ => ?_
  have hi := hi₁.trans hi₂
  have hs : ∀ i < 6, word u₂.mem (cdOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs₂ i hi).trans (hs₁ i hi)
  have k := keep_trans k₁ k₂
  refine WP.ite (!(cdOf s).mv) (by simp [eval, hz₂]) (fun hn => ?_) (fun hy => ?_)
  · have hn' : (cdOf s).mv = false := by simpa only [Bool.not_eq_true'] using hn
    have hv := invalid_modulus hn'
    refine WP.mono (ret_ok u₂ (r := 0) (by decide)) fun t ⟨ha, hm, kk⟩ => ?_
    refine ⟨?_, (kk.gpr (by decide)).trans hd₂, by rw [hm]; exact hi,
      (fun i hi => by rw [hm]; exact hs i hi), keep_trans k (kk.mono (by decide))⟩
    change ((t.gpr .rax).setWidth 32).toNat = if Spec.Ffdh.domainValid (cdOf s).k (cdOf s).dom then 1 else 0
    rw [ha, hv]; rfl
  · have hy' : (cdOf s).mv = true := by simpa only [Bool.not_eq_false'] using hy
    refine WP.mono (main_ok M E R hb₂ hd₂ hG hQ hy') fun t S₃ => ?_
    refine ⟨?_, S₃.1.1, hi.trans S₃.2.1,
      (fun i hi => (S₃.2.2.1 i hi).trans (hs i hi)), keep_trans k S₃.2.2.2⟩
    change ((t.gpr .rax).setWidth 32).toNat = if Spec.Ffdh.domainValid (cdOf s).k (cdOf s).dom then 1 else 0
    have he := propext (accept_valid hb₂ hy')
    rw [S₃.1.2]
    simpa only [bit, he] using bit_bool (Spec.Ffdh.domainValid (cdOf s).k (cdOf s).dom)

end VG.Proof.Ffdh.X86_64.CheckDomain
