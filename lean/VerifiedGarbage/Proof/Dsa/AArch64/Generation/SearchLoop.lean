module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Dsa.AArch64.Generation.SearchAdvance`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.SearchStatus`, which this module and modules that import it used -/

section

/-! # Status handling and termination test of the native p search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem searchStatus_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.pSearchStatus status)) s fun t =>
      SearchControl B counter stride t ∧ word t.mem B 16 = BitVec.ofNat 64 status ∧
      Outside B 16 8 s.mem t.mem ∧ Keep [.x3] s t := by
  have hst := h.scr.st (d := 16) (by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = s.mem.writeW (off B 16) (BitVec.ofNat 64 status)) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchStatus, h.x0,
      hdr_enc (by decide : 2 < 32), hst]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hv]) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 16 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ⟨⟨h.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.x0, ?_, ?_⟩,
    by rw [hm, word_writeW_self], ho, hk⟩
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.count
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.offset

theorem searchStatusCmp_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3)
    (hstat : word s.mem B 16 = BitVec.ofNat 64 status) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pSearchStatusCmp) s fun t =>
      eval (.zero .x .x3) t = some (decide (status = 3)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    eval (.zero .x .x3) t = some (decide (status = 3)) ∧ t.mem = s.mem) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchStatusCmp, h.x0,
      hdr_enc (by decide : 2 < 32), h.scr.ld (d := 16) (by decide), hstat, eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
    change BitVec.ofNat 64 status = (3#64) ↔ status = 3
    constructor
    · intro he
      have hn := congrArg BitVec.toNat he
      change status % 2 ^ 64 = 3 at hn
      rwa [Nat.mod_eq_of_lt (by omega_using [hv] : status < 2 ^ 64)] at hn
    · intro he; subst status; rfl) rfl rfl rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The p search advances exactly one counter and one hash stride -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem searchAdvance_ok {s : State} {B : Addr} {counter stride limit : Nat}
    (h : SearchControl B counter stride s) (hc : counter < limit) (hl : limit ≤ 12288)
    (hs : stride ≤ 12) :
    WP isa (Impl.Dsa.AArch64.Generation.pSearchAdvance limit stride) s fun t =>
      SearchControl B (counter + 1) stride t ∧
      word t.mem B 16 = BitVec.ofNat 64 (if counter + 1 < limit then 3 else 2) ∧
      Outside B 0 24 s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x7] s t := by
  unfold Impl.Dsa.AArch64.Generation.pSearchAdvance
  refine WP.seq (WP.mono (searchAdvanceHead_ok h hc hl hs) fun u ⟨hu, hflag, ho, hk⟩ => ?_)
  refine WP.ite (decide (counter + 1 < limit)) (by
    by_cases he : counter + 1 < limit
    · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hflag,
        ite_eq_right (show ¬ limit ≤ counter + 1 by omega_using [he]), decide_eq_true he]; rfl
    · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hflag,
        ite_eq_left (show limit ≤ counter + 1 by omega_using [he]), decide_eq_false he]; rfl) (fun hyes => ?_) (fun hno => ?_)
  · have hlt : counter + 1 < limit := of_decide_eq_true hyes
    refine WP.mono (searchStatus_ok hu (by decide : 3 ≤ 3)) fun t ⟨ht, hstat, hot, kt⟩ => ?_
    exact ⟨ht, by simpa only [hlt, ite_true] using hstat,
      (ho.mono (by decide) (by decide)).trans (hot.mono (by decide) (by decide)),
      (hk.trans kt).mono (by decide)⟩
  · have hge : ¬ counter + 1 < limit := of_decide_eq_false hno
    refine WP.mono (searchStatus_ok hu (by decide : 2 ≤ 3)) fun t ⟨ht, hstat, hot, kt⟩ => ?_
    exact ⟨ht, by simpa only [hge, ite_false] using hstat,
      (ho.mono (by decide) (by decide)).trans (hot.mono (by decide) (by decide)),
      (hk.trans kt).mono (by decide)⟩

theorem searchInit_ok {s : State} {B : Addr} (h : Scr s B 24) (hdi : s.gpr .x0 = B) (stride : Nat) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pSearchInit) s fun t =>
      SearchControl B 0 stride t ∧ Outside B 0 16 s.mem t.mem ∧ Keep [.x3] s t := by
  let m := (s.mem.writeW (off B 0) (BitVec.ofNat 64 0)).writeW (off B 8) (BitVec.ofNat 64 1)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = m) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchInit, hdi,
      hdr_enc (by decide : 0 < 32), hdr_enc (by decide : 1 < 32),
      h.st (d := 0) (by decide), h.st (d := 8) (by decide)]; rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 0 16 s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ B _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ B _ (d := 8) (by decide)).mono (by decide) (by decide))
  refine ⟨⟨h.congr hk.wr, (hk.gpr _ (by decide)).trans hdi, ?_, ?_⟩, ho, hk⟩
  · rw [hm]
    dsimp only [m]
    rw [(writeW_outside _ B _ (d := 8) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hm, Nat.zero_mul, Nat.add_zero]; exact word_writeW_self _ _ _ _

end VG.Proof.Dsa.AArch64.Generation

end

end

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
    · have he : counter + 1 = limit := by omega_using [hc, hlt]
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
          ⟨hz, limit - (c + 1), by omega_using [hn, hc], c + 1, rfl, hlt, hi', hc'⟩)
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
