module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStatus

import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchAdvance
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchControl

/-! # Total correctness of the bounded native candidate-search loop

The payload invariant describes the candidate and witness tape; the
controller owns only its three words. Each rejected candidate advances
exactly once, including the final rejection at the attempt limit.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- Payload facts survive changes confined to the controller and its two
volatile registers. The payload must not include the controller words. -/
def SearchPayload (B : Addr) (P : State → Prop) : Prop :=
  ∀ {s t}, P s → Outside B 0 12 s.mem t.mem → Keeps [.eax, .ecx] s t → P t

theorem SearchControl.congr {s t : State} {B : Addr} {counter stride : Nat}
    (h : SearchControl B counter stride s) (hm : t.mem = s.mem) (hk : Keeps [.eax] s t) :
    SearchControl B counter stride t := h.unchanged hm hk (by decide) (by decide)

/-- One candidate body may finish or request the next attempt. An exhausted
attempt budget is a distinct terminal outcome handled by `done`. -/
theorem searchIteration_ok {body : Prog isa} {B : Addr} {limit stride counter : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      t.mem.readW (off B 8) 32 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, t.mem.readW (off B 8) 32 = BitVec.ofNat 32 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} (hc : counter < limit) (hi : I counter s) (h : SearchControl B counter stride s) :
    WP isa (Impl.Dsa.X86.Generation.pSearchIteration body limit stride) s fun t =>
      (eval .e t = some false ∧ Q t) ∨
      (eval .e t = some true ∧ I (counter + 1) t ∧
        SearchControl B (counter + 1) stride t ∧ counter + 1 < limit) := by
  unfold Impl.Dsa.X86.Generation.pSearchIteration
  refine WP.seq (WP.mono (body_ok counter s hc hi h) fun u ⟨hu, status, hv, hstat, hp⟩ => ?_)
  refine WP.seq (WP.mono (pSearchStatusCmp_ok hu hv hstat) fun v ⟨hz, hm, hk⟩ => ?_)
  have hvctrl := hu.congr hm hk
  have hframe : Outside B 0 12 u.mem v.mem := by rw [hm]; exact Outside.refl _ _ _ _
  by_cases hretry : status = 3
  · have hiu : I (counter + 1) u := by simpa only [hretry, ite_true] using hp
    have hiv := stable (counter + 1) hiu hframe (hk.mono (by decide))
    refine WP.seq (WP.ite true (by simp [eval, hz, hretry]) (fun _ => ?_) (fun he => Bool.noConfusion he))
    refine WP.mono (pSearchAdvance_ok hvctrl hc hl) fun w ⟨hw, hstatus, hf, kw⟩ => ?_
    have hiw := stable (counter + 1) hiv hf kw
    let next := if counter + 1 < limit then 3 else 2
    have hn : next ≤ 3 := by dsimp [next]; split <;> decide
    refine WP.mono (pSearchStatusCmp_ok hw hn hstatus) fun t ⟨hzt, hmt, kt⟩ => ?_
    have hit := stable (counter + 1) hiw (by rw [hmt]; exact Outside.refl _ _ _ _) (kt.mono (by decide))
    have ht := hw.congr hmt kt
    by_cases hlt : counter + 1 < limit
    · exact Or.inr ⟨by simp [eval, hzt, next, hlt], hit, ht, hlt⟩
    · have he : counter + 1 = limit := by omega
      refine Or.inl ⟨by simp [eval, hzt, next, hlt], ?_⟩
      apply done t (he ▸ hit) (he ▸ ht)
      rw [hmt, hstatus, ite_eq_right hlt]
      rfl
  · have hqu : Q u := by simpa only [hretry, ite_false] using hp
    have hqv := finish hqu hframe (hk.mono (by decide))
    refine WP.seq (WP.ite false (by simp [eval, hz, hretry]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_))
    refine WP.mono (pSearchStatusCmp_ok hvctrl hv (hm ▸ hstat)) fun t ⟨hzt, hmt, kt⟩ => ?_
    exact Or.inl ⟨by simp [eval, hzt, hretry],
      finish hqv (by rw [hmt]; exact Outside.refl _ _ _ _) (kt.mono (by decide))⟩

/-- The native loop always terminates within its public attempt budget. -/
theorem searchLoop_ok {body : Prog isa} {B : Addr} {limit stride : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      t.mem.readW (off B 8) 32 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, t.mem.readW (off B 8) 32 = BitVec.ofNat 32 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} {counter : Nat} (hc : counter < limit)
    (hi : I counter s) (h : SearchControl B counter stride s) :
    WP isa (.loop (Impl.Dsa.X86.Generation.pSearchIteration body limit stride) .e) s Q := by
  exact WP.loop
    (fun n t => ∃ c, n = limit - c ∧ c < limit ∧ I c t ∧ SearchControl B c stride t)
    (fun n t ⟨c, hn, hc, hi, hctrl⟩ =>
      WP.mono (searchIteration_ok hl stable finish done body_ok hc hi hctrl)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hc', hlt⟩ =>
          ⟨hz, limit - (c + 1), by omega, c + 1, rfl, hlt, hi', hc'⟩)
    (limit - counter) s ⟨counter, rfl, hc, hi, h⟩

/-- Initialization and the bounded search compose without any host loop. -/
theorem pSearch_ok {body : Prog isa} {B : Addr} {limit stride : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288) (hpos : 0 < limit)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      t.mem.readW (off B 8) 32 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, t.mem.readW (off B 8) 32 = BitVec.ofNat 32 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} (hi : I 0 s) (h : Scr s B 12) :
    WP isa (Impl.Dsa.X86.Generation.pSearch body limit stride) s Q := by
  unfold Impl.Dsa.X86.Generation.pSearch
  refine WP.seq (WP.mono (pSearchInit_ok h (by decide)) fun t ⟨count, offset, frame, keeps⟩ => ?_)
  have Ct : SearchControl B 0 stride t := ⟨h.of_keeps keeps (by decide), count, by simpa using offset⟩
  exact searchLoop_ok hl stable finish done body_ok hpos
    (stable 0 hi (frame.mono (by omega) (by omega)) (keeps.mono (by decide))) Ct

end VG.Proof.Dsa.X86.Generation
