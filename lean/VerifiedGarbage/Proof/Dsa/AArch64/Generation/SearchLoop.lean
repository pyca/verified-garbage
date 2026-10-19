module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchAdvance
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStatus

/-! # Total correctness of the bounded native candidate-search loop

The payload invariant describes the candidate and witness tape; the
controller owns only its three words. Each rejected candidate advances
exactly once, including the final rejection at the attempt limit.
-/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Payload facts survive changes confined to the controller and its two
volatile registers. The payload must not include the controller words. -/
def SearchPayload (B : Addr) (P : State → Prop) : Prop :=
  ∀ {s t}, P s → Outside B 0 24 s.mem t.mem → Keep [.x3, .x4, .x5, .x7] s t → P t

theorem SearchControl.congr {s t : State} {B : Addr} {counter stride : Nat}
    (h : SearchControl B counter stride s) (hm : t.mem = s.mem) (hk : Keep [.x3] s t) :
    SearchControl B counter stride t :=
  ⟨h.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.x0, hm ▸ h.count, hm ▸ h.offset⟩

/-- One candidate body may finish or request the next attempt. An exhausted
attempt budget is a distinct terminal outcome handled by `done`. -/
theorem searchIteration_ok {body : Prog isa} {B : Addr} {limit stride counter : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288) (hs : stride ≤ 12)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      word t.mem B 16 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, word t.mem B 16 = BitVec.ofNat 64 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} (hc : counter < limit) (hi : I counter s) (h : SearchControl B counter stride s) :
    WP isa (Impl.Dsa.AArch64.Generation.pSearchIteration body limit stride) s fun t =>
      (eval (.zero .x .x3) t = some false ∧ Q t) ∨
      (eval (.zero .x .x3) t = some true ∧ I (counter + 1) t ∧
        SearchControl B (counter + 1) stride t ∧ counter + 1 < limit) := by
  unfold Impl.Dsa.AArch64.Generation.pSearchIteration
  simp only [Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (body_ok counter s hc hi h) fun u ⟨hu, status, hv, hstat, hp⟩ => ?_)
  refine WP.seq (WP.mono (searchStatusCmp_ok hu hv hstat) fun v ⟨hz, hm, hk⟩ => ?_)
  have hvctrl := hu.congr hm hk
  have hframe : Outside B 0 24 u.mem v.mem := by rw [hm]; exact Outside.refl _ _ _ _
  by_cases hretry : status = 3
  · have hiu : I (counter + 1) u := by simpa only [hretry, ite_true] using hp
    have hiv := stable (counter + 1) hiu hframe (hk.mono (by decide))
    refine WP.seq (WP.ite true (by simp [hz, hretry]) (fun _ => ?_) (fun he => Bool.noConfusion he))
    refine WP.mono (searchAdvance_ok hvctrl hc hl hs) fun w ⟨hw, hstatus, hf, kw⟩ => ?_
    have hiw := stable (counter + 1) hiv hf kw
    let next := if counter + 1 < limit then 3 else 2
    have hn : next ≤ 3 := by dsimp [next]; split <;> decide
    refine WP.mono (searchStatusCmp_ok hw hn hstatus) fun t ⟨hzt, hmt, kt⟩ => ?_
    have hit := stable (counter + 1) hiw (by rw [hmt]; exact Outside.refl _ _ _ _) (kt.mono (by decide))
    have ht := hw.congr hmt kt
    by_cases hlt : counter + 1 < limit
    · exact Or.inr ⟨by simp [hzt, next, hlt], hit, ht, hlt⟩
    · have he : counter + 1 = limit := by omega
      refine Or.inl ⟨by simp [hzt, next, hlt], ?_⟩
      apply done t (he ▸ hit) (he ▸ ht)
      rw [hmt, hstatus, ite_eq_right hlt]
      rfl
  · have hqu : Q u := by simpa only [hretry, ite_false] using hp
    have hqv := finish hqu hframe (hk.mono (by decide))
    refine WP.seq (WP.ite false (by simp [hz, hretry]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_))
    refine WP.mono (searchStatusCmp_ok hvctrl hv (hm ▸ hstat)) fun t ⟨hzt, hmt, kt⟩ => ?_
    exact Or.inl ⟨by simp [hzt, hretry],
      finish hqv (by rw [hmt]; exact Outside.refl _ _ _ _) (kt.mono (by decide))⟩

/-- The native loop always terminates within its public attempt budget. -/
theorem searchLoop_ok {body : Prog isa} {B : Addr} {limit stride : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288) (hs : stride ≤ 12)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      word t.mem B 16 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, word t.mem B 16 = BitVec.ofNat 64 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} {counter : Nat} (hc : counter < limit)
    (hi : I counter s) (h : SearchControl B counter stride s) :
    WP isa (.loop (Impl.Dsa.AArch64.Generation.pSearchIteration body limit stride) (.zero .x .x3)) s Q := by
  exact WP.loop
    (fun n t => ∃ c, n = limit - c ∧ c < limit ∧ I c t ∧ SearchControl B c stride t)
    (fun n t ⟨c, hn, hc, hi, hctrl⟩ =>
      WP.mono (searchIteration_ok hl hs stable finish done body_ok hc hi hctrl)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hc', hlt⟩ =>
          ⟨hz, limit - (c + 1), by omega, c + 1, rfl, hlt, hi', hc'⟩)
    (limit - counter) s ⟨counter, rfl, hc, hi, h⟩

/-- Initialization and the bounded search compose without any host loop. -/
theorem pSearch_ok {body : Prog isa} {B : Addr} {limit stride : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288) (hpos : 0 < limit) (hs : stride ≤ 12)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      word t.mem B 16 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, word t.mem B 16 = BitVec.ofNat 64 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} (hi : I 0 s) (h : Scr s B 24) (hdi : s.gpr .x0 = B) :
    WP isa (Impl.Dsa.AArch64.Generation.pSearch body limit stride) s Q := by
  unfold Impl.Dsa.AArch64.Generation.pSearch
  refine WP.seq (WP.mono (searchInit_ok h hdi stride) fun t ⟨ht, hf, hk⟩ => ?_)
  exact searchLoop_ok hl hs stable finish done body_ok hpos
    (stable 0 hi (hf.mono (by decide) (by decide)) (hk.mono (by decide))) ht

end VG.Proof.Dsa.AArch64.Generation
