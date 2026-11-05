module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Tests
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on RISC-V: the tests in constant time

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{CTBase,CTDraw,CTMr,CTTest,CTRes,CTTests}.lean`):
two runs are related by `Two Φ`, both satisfying `Φ a` for the same public
data `a`, whatever the registers they save on entry (`PP.with`). Each piece
is checked by the taint analysis from the registers the predicate pins:
what a piece loads from memory (the tape's address and length, a count) is
pinned by the next predicate. The branches are on what the public data
decides: a witness's range and its round's result, a test's status, the
tape's length.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.Taint VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_nonzero eval_zero_ofNat eval_nonzero_ofNat)
open VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (RoundImpl A)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.Bignum.RISCV64.Precompute (loadN)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-! ## Relating two runs -/

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨g a, h _ _ h₁, h _ _ h₂, hsp⟩) fun _ _ h => h

theorem two_mono {α : Type} {Φ Φ' : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a s, Φ a s → Φ' a s) (hct : RelCT isa (Two Φ') c Q) : RelCT isa (Two Φ) c Q :=
  two_map id h hct

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩

/-- A branch on a condition `Φ a` decides. -/
theorem two_ite' {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop} (b : α → Bool) (hc : ∀ a s, Φ a s → isa.eval cond s = some (b a))
    (ht : RelCT isa (Two fun a s => Φ a s ∧ b a = true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ b a = false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q :=
  two_ite (fun a _ _ h₁ h₂ => (hc a _ h₁).trans (hc a _ h₂).symm)
    (two_mono (fun a s ⟨h, hb⟩ => ⟨h, by rw [hc a s h] at hb; exact Option.some.inj hb⟩) ht)
    (two_mono (fun a s ⟨h, hb⟩ => ⟨h, by rw [hc a s h] at hb; exact Option.some.inj hb⟩) he)

/-- A loop whose condition `Φ a` decides (`go a`), from data `next a` of
smaller measure when it goes on. -/
theorem two_loopD {α : Type} {Φ Ψ : α → State → Prop} (μ : α → Nat) (next : α → α) (go : α → Bool)
    {body : Prog isa} {cond : isa.Cond}
    (hct : RelCT isa (Two Φ) body fun _ _ => True)
    (hw : ∀ a s, Φ a s → WP isa body s fun s' => isa.eval cond s' = some (go a) ∧
      (go a = false → Ψ a s') ∧ (go a = true → μ (next a) < μ a ∧ Φ (next a) s')) :
    RelCT isa (Two Φ) (.loop body cond) (Two Ψ) := by
  have key := RelCT.loop (M := isa) (body := body) (c := cond) (Q := Two Ψ)
    (fun n s₁ s₂ => ∃ a, n = μ a ∧ Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp) (fun n => by
      have hp := two_post (Φ := fun a s => n = μ a ∧ Φ a s)
        (Ψ := fun a s' => n = μ a ∧ isa.eval cond s' = some (go a) ∧
          (go a = false → Ψ a s') ∧ (go a = true → μ (next a) < μ a ∧ Φ (next a) s'))
        (two_mono (fun a s h => h.2) hct) fun a s h => WP.mono (hw a s h.2) fun s' h' => ⟨h.1, h'⟩
      refine hp.mono (fun s₁ s₂ ⟨a, hn, h₁, h₂, hsp⟩ => ⟨a, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
      rintro s₁ s₂ ⟨a, ⟨hn, e₁, f₁, g₁⟩, ⟨-, e₂, f₂, g₂⟩, hsp⟩
      refine ⟨by rw [e₁, e₂], fun h => ?_, fun h => ?_⟩
      · have hg : go a = false := by rw [e₁] at h; exact Option.some.inj h
        exact ⟨a, f₁ hg, f₂ hg, hsp⟩
      · have hg : go a = true := by rw [e₁] at h; exact Option.some.inj h
        exact ⟨μ (next a), by rw [hn]; exact (g₁ hg).1, next a, rfl, (g₁ hg).2, (g₂ hg).2, hsp⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  exact key (μ a) _ _ _ _ _ _ ⟨a, rfl, h₁, h₂, hsp⟩ e₁ e₂

theorem beq_zero_of_iff {x : BitVec 64} {P : Prop} [Decidable P] (h : x = 0#64 ↔ P) : (x == 0) = decide P := by
  apply Bool.eq_iff_iff.mpr; rw [beq_iff_eq, decide_eq_true_iff]; exact h

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_s6 {α : Type} {Φ : α → State → Prop} (B : α → Addr) (h : ∀ a s, Φ a s → s.gpr .s6 = B a) :
    Pins Φ [.s6] := by
  intro a s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h a _ h₁, h a _ h₂]

/-- `p`'s public data with a run's saved registers. -/
def PP.with (p : PP) (sv : Nat → BitVec 64) : PP := { p with sv := sv }

/-- In a modulus's working space, the registers `Ph` and `St` fix. -/
theorem pins_ph {α : Type} {Φ : α → State → Prop} (q : α → PP) (mb : α → Nat)
    (h : ∀ a s, Φ a s → ∃ sv C, St ((q a).with sv) s ∧ Ph ((q a).with sv) (mb a) C s) :
    Pins Φ [.a7, .s5, .t0, .s6] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, _, st₁, p₁⟩ := h a s₁ h₁
  obtain ⟨_, _, st₂, p₂⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [p₁.a7, p₂.a7]; rfl
  · rw [p₁.s5, p₂.s5]
  · rw [p₁.t0, p₂.t0]
  · rw [st₁.s6, st₂.s6]; rfl

/-! ## A draw -/

/-- A draw's public data. -/
structure DrawD where
  q : PP
  mb : Nat
  N : Nat
  u : Nat
  i : Nat
  K : Nat

/-- Before a draw. -/
def DI (d : DrawD) (s : State) : Prop :=
  ∃ sv, MSt (d.q.with sv) d.mb d.N d.K s ∧ word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧
    d.u + (d.mb + 7) / 8 ≤ d.q.r.length ∧ word s.mem d.q.B 176 = BitVec.ofNat 64 d.i ∧
    word s.mem d.q.B 160 = BitVec.ofNat 64 4 ∧ d.i < 2 ^ 62

theorem pins_DI : Pins DI [.a7, .s5, .t0, .s6] :=
  pins_ph DrawD.q DrawD.mb fun _ _ ⟨sv, M, _⟩ => ⟨sv, _, M.st, M.ph⟩

/-- After a draw's head. -/
def DA (d : DrawD) (t : State) : Prop :=
  ∃ sv s, (MSt (d.q.with sv) d.mb d.N d.K s ∧ word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧
    d.u + (d.mb + 7) / 8 ≤ d.q.r.length ∧ word s.mem d.q.B 176 = BitVec.ofNat 64 d.i ∧
    word s.mem d.q.B 160 = BitVec.ofNat 64 4 ∧ d.i < 2 ^ 62) ∧ DHead (d.q.with sv) d.mb d.u s t

theorem pins_DA : Pins DA [.s7, .s8, .a7, .s5, .t0, .s6] := by
  rintro d s₁ s₂ ⟨_, _, ⟨M₁, -⟩, ⟨a7, a8, a77, -⟩, k₁, -⟩ ⟨_, _, ⟨M₂, -⟩, ⟨b7, b8, b77, -⟩, k₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a7, b7]; rfl
  · rw [a8, b8]
  · rw [a77, b77]; rfl
  · rw [k₁.gpr (by decide), k₂.gpr (by decide), M₁.ph.s5, M₂.ph.s5]
  · rw [k₁.gpr (by decide), k₂.gpr (by decide), M₁.ph.t0, M₂.ph.t0]
  · rw [k₁.gpr (by decide), k₂.gpr (by decide), M₁.st.s6, M₂.st.s6]; rfl

theorem drawHead_ct : RelCT isa (Two DI) (.block dHeadB) (Two DA) :=
  two_post (two_taint _ pins_DI (by taint_decide)) fun _ s ⟨sv, M, hu, hroom, hI, hS, hi⟩ =>
    WP.mono (dHead_ok ⟨M, hu, hroom⟩) fun t ht => ⟨sv, s, ⟨M, hu, hroom, hI, hS, hi⟩, ht⟩

/-- After the witness's octets are loaded. -/
def DLd (d : DrawD) (t : State) : Prop := ∃ sv, DL (d.q.with sv) d.mb d.N d.u d.i d.K t ∧ d.i < 2 ^ 62

theorem pins_DLd : Pins DLd [.a7, .s5, .t0, .s6] :=
  pins_ph DrawD.q DrawD.mb fun _ _ ⟨sv, h, _⟩ => ⟨sv, _, h.m.st, h.m.ph⟩

theorem drawLoad_ct : RelCT isa (Two DA) (.seq loadN (.block [.addi .a7 .s6 hdrBytes])) (Two DLd) :=
  two_post (two_taint _ pins_DA (by taint_decide)) fun _ _ ⟨sv, _, ⟨M, hu, hroom, hI, hS, hi⟩, ht⟩ =>
    WP.mono (drawLoad2_ok M hu hroom hI hS ht) fun _ h' => ⟨sv, h', hi⟩

/-- Before a draw's branches. -/
def DMd (d : DrawD) (t : State) : Prop := ∃ sv, DMid (d.q.with sv) d.mb d.N d.u d.i d.K t ∧ d.i < 2 ^ 62

theorem drawMid_ct : RelCT isa (Two DLd) (.seq (.seq (.block cutB) atLeast2) ltN) (Two DMd) :=
  two_post (two_taint _ pins_DLd (by taint_decide)) fun _ _ ⟨sv, h, hi⟩ =>
    WP.mono (drawMid_ok h) fun _ h' => ⟨sv, h', hi⟩

/-- The round's call, from a witness in range. -/
def rcOf (d : DrawD) : RcD := ⟨d.q.B, d.q.n, wOf d.mb, d.N, wA d.mb d.q.r d.u⟩

/-- After the round. -/
def DR (d : DrawD) (t : State) : Prop :=
  t.gpr .a0 = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u) then 1 else 0) ∧
    t.gpr .s6 = d.q.B

theorem round_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two fun d s => (DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
      decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) (Search.round R.name R.code) fun _ _ => True := by
  have hrc : ∀ d s, ((DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
      decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) → RC (rcOf d) s := by
    rintro d s ⟨⟨⟨sv, h, _⟩, h2⟩, hN⟩
    simp only [decide_eq_false_iff_not, Decidable.not_not] at h2 hN
    exact h.rc (by show wA d.mb d.q.r d.u < d.N; omega)
  unfold Search.round
  refine RelCT.seq (two_post (two_map rcOf hrc hR.ct) (Ψ := DR) fun d s h => ?_) ?_
  · exact WP.mono (hR.ok _ s (hrc d s h)) fun t ht => ⟨ht.a0, ht.prep.s6⟩
  refine two_ite' (fun d => decide ((if Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u) then 1 else 0) = 0))
    (fun d s h => eval_zero_ofNat s .a0 (by split <;> decide) h.1)
    (two_taint _ (pins_s6 (fun d : DrawD => d.q.B) fun _ _ h => h.1.2) (by taint_decide))
    (two_taint _ (pins_s6 (fun d : DrawD => d.q.B) fun _ _ h => h.1.2) (by taint_decide))

theorem drawBranch_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two DMd) (drawBranch R.name R.code) fun _ _ => True := by
  unfold drawBranch
  refine two_ite' (fun d => decide (wA d.mb d.q.r d.u < 2)) (fun d s ⟨sv, h, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z3]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) ?_
  refine two_ite' (fun d => decide (¬ wA d.mb d.q.r d.u < d.N - 1)) (fun d s ⟨⟨sv, h, _⟩, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z4]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) (round_ct hR)

/-- A draw leaks the same from the same public data. -/
theorem draw_ct {R : RoundImpl} (hR : RoundCall R) : RelCT isa (Two DI) (draw R.name R.code) fun _ _ => True := by
  rw [draw_eq]
  exact RelCT.seq (RelCT.seq drawHead_ct drawLoad_ct)
    (RelCT.assoc (RelCT.assoc (RelCT.seq drawMid_ct (drawBranch_ct hR))))

/-! ## The witnesses -/

/-- The witness loop's public data. -/
structure MrD where
  q : PP
  mb : Nat
  N : Nat
  res : Option (Bool × List Byte)
  i : Nat
  u : Nat
  K : Nat

/-- At the head of the witness loop. -/
def MI (a : MrD) (s : State) : Prop :=
  (∃ sv, MrSt (a.q.with sv) a.mb a.N a.K a.res a.i a.u s) ∧ Spec.RsaKeyGen.bitLength (a.N - 1) = a.mb

/-- After the loop. -/
def ME (a : MrD) (s : State) : Prop := ∃ sv, MrEnd (a.q.with sv) a.mb a.N a.K a.res s

def mrNext (a : MrD) : MrD :=
  { a with i := dIdx a.N a.i (wA a.mb a.q.r a.u), u := a.u + (a.mb + 7) / 8 }

/-- The working space's address. -/
def R6 (a : MrD) (s : State) : Prop := s.gpr .s6 = a.q.B

theorem pins_R6 : Pins R6 [.s6] := pins_s6 (fun a : MrD => a.q.B) fun _ _ h => h

theorem pins_MI : Pins MI [.a7, .s5, .t0, .s6] :=
  pins_ph MrD.q MrD.mb fun _ _ ⟨⟨sv, h⟩, _⟩ => ⟨sv, _, h.m.st, h.m.ph⟩

/-- After the head's block. -/
def MH (a : MrD) (s : State) : Prop :=
  MI a s ∧ s.gpr .t4 = BitVec.ofNat 64 (if a.q.r.length - a.u < (a.mb + 7) / 8 then 1 else 0)

theorem headBlk_MH {a : MrD} {s : State} (h : MI a s) : WP isa (.block tapeShort) s (MH a) := by
  obtain ⟨⟨sv, hs⟩, hbl⟩ := h
  refine WP.mono (mrHeadBlk_ok hs) fun t ⟨⟨⟨t4, tm⟩, k⟩, tsp⟩ => ⟨⟨⟨sv, ?_⟩, hbl⟩, t4⟩
  have M : MSt (a.q.with sv) a.mb a.N a.K t := hs.m.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp
    (by decide) (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide))
  exact ⟨M, by rw [tm]; exact hs.used, by rw [tm]; exact hs.idx, by rw [tm]; exact hs.stat, hs.ul, hs.ik, hs.rest⟩

theorem mrBody_ct {R : RoundImpl} (hR : RoundCall R) : RelCT isa (Two MI)
    (.seq (.block tapeShort)
      (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw R.name R.code))
        (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) fun _ _ => True := by
  refine RelCT.seq (two_post (two_taint _ pins_MI (by taint_decide)) fun _ _ h => headBlk_MH h)
    (RelCT.seq (R := Two R6) ?_ ?_)
  rotate_left
  · exact two_taint _ pins_R6 (by taint_decide)
  have ev : ∀ a s, MH a s → isa.eval (.nonzero .t4) s =
      some (decide ((if a.q.r.length - a.u < (a.mb + 7) / 8 then 1 else 0) ≠ 0)) :=
    fun a s h => eval_nonzero_ofNat s .t4 (by split <;> decide) h.2
  refine two_ite' (fun a => decide ((if a.q.r.length - a.u < (a.mb + 7) / 8 then 1 else 0) ≠ 0)) ev ?_ ?_
  · refine two_post (two_taint _ (fun a s₁ s₂ h₁ h₂ => pins_MI a s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide))
      fun a s h => ?_
    obtain ⟨⟨⟨⟨sv, hs⟩, -⟩, -⟩, -⟩ := h
    have l160 := hs.m.st.st (d := 160) (by decide)
    have a160 := hs.m.st.al (d := 160) (by decide) (by decide)
    refine WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .s6 = a.q.B) ?_ (by rfl) (by rfl)) fun t ⟨ht, _⟩ => ht
    simp only [sth, hStat]; brun [hs.m.st.s6, l160, a160, exec_li (show imm12 0 by decide)]; rfl
  · have hd : ∀ a s, MH a s ∧ decide ((if a.q.r.length - a.u < (a.mb + 7) / 8 then 1 else 0) ≠ 0) = false →
        DI ⟨a.q, a.mb, a.N, a.u, a.i, a.K⟩ s := by
      rintro a s ⟨⟨⟨⟨sv, hs⟩, -⟩, -⟩, hb⟩
      simp only [decide_eq_false_iff_not, Decidable.not_not] at hb
      have hul : a.u ≤ a.q.r.length := hs.ul
      have hik : a.i < a.K := hs.ik
      have hK : a.K ≤ 128 := hs.m.ph.k2
      have hr : a.u + (a.mb + 7) / 8 ≤ a.q.r.length := by
        by_contra hc; rw [ite_eq_left (by omega)] at hb; exact absurd hb (by decide)
      exact ⟨sv, hs.m, hs.used, hr, hs.idx, hs.stat, show a.i < 2 ^ 62 by omega⟩
    refine two_post (two_map (fun a : MrD => (⟨a.q, a.mb, a.N, a.u, a.i, a.K⟩ : DrawD)) hd (draw_ct hR)) fun a s h => ?_
    obtain ⟨sv, M, hu, hroom, hI, hS, hi⟩ := hd a s h
    exact WP.mono (draw_ok hR M hu hroom hI hS hi) fun t ht => ht.1.st.s6

/-- Before the witness loop. -/
def MI0 (a : MrD) (s : State) : Prop :=
  (∃ sv, MSt (a.q.with sv) a.mb a.N a.K s ∧ word s.mem a.q.B 152 = BitVec.ofNat 64 a.u) ∧
    a.u ≤ a.q.r.length ∧ a.i = 0 ∧ a.res = checkWitnesses a.N a.K (a.q.r.drop a.u) ∧
    Spec.RsaKeyGen.bitLength (a.N - 1) = a.mb

theorem pins_MI0 : Pins MI0 [.a7, .s5, .t0, .s6] :=
  pins_ph MrD.q MrD.mb fun _ _ ⟨⟨sv, M, _⟩, _⟩ => ⟨sv, _, M.st, M.ph⟩

/-- The witness loop leaks the same in runs testing the same modulus from the
same tape. -/
theorem millerRabin_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two MI0) (millerRabin R.name R.code) (Two ME) := by
  unfold millerRabin
  refine RelCT.seq (two_post (two_taint _ pins_MI0 (by taint_decide)) (Ψ := MI) fun a s h => ?_)
    (two_loopD (fun a => a.q.r.length + 1 - a.u) mrNext (fun a => mrGo a.q.r a.mb a.N a.i a.u a.K) (mrBody_ct hR)
      fun a s h => ?_)
  · obtain ⟨⟨sv, M, hu⟩, hul, hi, hres, hbl⟩ := h
    refine WP.mono (mrInit_ok M hu hul) fun t ht => ⟨⟨sv, ?_⟩, hbl⟩
    rw [hi, hres]; exact ht
  · obtain ⟨⟨sv, hs⟩, hbl⟩ := h
    have hm1 := hs.m.mb1
    refine WP.mono (mrIter_ok hR hbl hs) fun t ⟨he, hend, hgo⟩ =>
      ⟨he, fun hg => ⟨sv, hend hg⟩, fun hg => ⟨?_, ⟨sv, hgo hg⟩, hbl⟩⟩
    have hul : a.u + (a.mb + 7) / 8 ≤ a.q.r.length := (hgo hg).ul
    show a.q.r.length + 1 - (a.u + (a.mb + 7) / 8) < a.q.r.length + 1 - a.u
    omega

/-! ## A test -/

/-- The candidate's state, whatever the registers saved on entry. -/
def PS (q : PP) (s : State) : Prop := ∃ sv, St (q.with sv) s

theorem pins_PS : Pins PS [.s6] := pins_s6 PP.B fun _ _ ⟨_, h⟩ => h.s6

/-- After `phase b`'s head: the bit length and words in the header. -/
def PH1 (b : Bool) (q : PP) (s : State) : Prop :=
  ∃ sv, St (q.with sv) s ∧ word s.mem q.B (8 * hMb) = BitVec.ofNat 64 (mbOf q b) ∧
    word s.mem q.B (8 * hW) = BitVec.ofNat 64 (wOf (mbOf q b))

theorem pins_PH1 (b : Bool) : Pins (PH1 b) [.s6] := pins_s6 PP.B fun _ _ ⟨_, h, _⟩ => h.s6

/-- After `topMask`'s first block: its count. -/
def PT (b : Bool) (q : PP) (s : State) : Prop :=
  s.gpr .s6 = q.B ∧ s.gpr .t3 = BitVec.ofNat 64 (mbOf q b + 64 - 64 * wOf (mbOf q b))

theorem pins_PT (b : Bool) : Pins (PT b) [.t3, .s6] := by
  rintro q s₁ s₂ ⟨a6, a3⟩ ⟨b6, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a6, b6]

theorem phaseHead_ct (b : Bool) : RelCT isa (Two PS) (.block (phaseHead b)) fun _ _ => True := by
  cases b
  · exact two_taint _ pins_PS (by taint_decide)
  · exact two_taint _ pins_PS (by taint_decide)

theorem phase_ct (b : Bool) : RelCT isa (Two PS) (phase b) fun _ _ => True := by
  unfold phase topMask
  refine RelCT.seq (two_post (phaseHead_ct b) (Ψ := PH1 b) fun q s ⟨sv, h⟩ => ?_)
    (RelCT.seq (two_post (two_taint _ (pins_PH1 b) (by taint_decide)) (Ψ := PT b)
      fun q s ⟨sv, h, hm, hw⟩ => ?_) (two_taint _ (pins_PT b) (by taint_decide)))
  · exact WP.mono (WP.rdwr (phaseHead_ok h b)) fun u ⟨⟨⟨_, _, _, um, _, uw, _, _, _, uf⟩, ku⟩, _, _, usp⟩ =>
      ⟨sv, h.step (Frm.toMut (uf.mono fun r hr => List.mem_append_left _ hr) (phRanges_mut _)) ku usp, um, uw⟩
  · exact WP.mono (topT1_ok h hm hw) fun u ⟨⟨u3, _, _⟩, ku⟩ => ⟨(ku.gpr (by decide)).trans h.s6, u3⟩

/-- In a modulus's working space. -/
def PA (b : Bool) (q : PP) (s : State) : Prop := ∃ sv C, St (q.with sv) s ∧ Ph (q.with sv) (mbOf q b) C s

theorem pins_PA (b : Bool) : Pins (PA b) [.a7, .s5, .t0, .s6] :=
  pins_ph id (fun q => mbOf q b) fun _ _ h => h

/-- After `shapeP`'s first block. -/
def SH1 (q : PP) (s : State) : Prop :=
  s.gpr .s6 = q.B ∧ s.gpr .a7 = off q.B (slot (wOf q.bits) 0) ∧ s.gpr .t0 = BitVec.ofNat 64 (wOf q.bits) ∧
    s.gpr .s7 = off q.rp 0 ∧ s.gpr .s8 = BitVec.ofNat 64 q.L

theorem pins_SH1 : Pins SH1 [.s6, .a7, .t0, .s7, .s8] := by
  rintro q s₁ s₂ ⟨a6, a7, a0, a77, a8⟩ ⟨b6, b7, b0, b77, b8⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a7, b7]
  · rw [a0, b0]
  · rw [a77, b77]
  · rw [a8, b8]

theorem shapeP_ct : RelCT isa (Two (PA false)) shapeP fun _ _ => True := by
  unfold shapeP
  refine RelCT.seq (two_post (two_taint _ (pins_PA false) (by taint_decide)) (Ψ := SH1) fun q s ⟨sv, _, h, hp⟩ =>
    WP.mono (shapeHead_ok h) fun u ⟨⟨u7, u8, _⟩, ku⟩ => ⟨(ku.gpr (by decide)).trans h.s6,
      (ku.gpr (by decide)).trans hp.a7, (ku.gpr (by decide)).trans hp.t0, u7, u8⟩)
    (two_taint _ pins_SH1 (by taint_decide))

theorem phasePA_ct (b : Bool) : RelCT isa (Two PS) (phase b) (Two (PA b)) :=
  two_post (phase_ct b) fun _ _ ⟨sv, h⟩ => WP.mono (phase_ok h b) fun _ ⟨⟨⟨ht, hp, _⟩, _⟩, _⟩ => ⟨sv, _, ht, hp⟩

/-- A test's public data, once its modulus is in place. -/
structure TD where
  q : PP
  mb : Nat
  N : Nat
  u : Nat
  K : Nat

/-- Before a test's Montgomery set-up. -/
def TC (d : TD) (s : State) : Prop := ∃ sv, TCPre (d.q.with sv) d.mb d.N d.u d.K s

theorem pins_TC : Pins TC [.a7, .s5, .t0, .s6] := pins_ph TD.q TD.mb fun _ _ ⟨sv, h⟩ => ⟨sv, _, h.st, h.ph⟩

/-- The witness loop's data. -/
def mrOf (d : TD) : MrD :=
  ⟨d.q, d.mb, d.N, checkWitnesses d.N d.K (d.q.r.drop d.u), 0, d.u, d.K⟩

theorem testCore_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two TC) (.seq montPrep (millerRabin R.name R.code)) (Two ME) :=
  RelCT.seq (two_post (two_taint _ pins_TC (by taint_decide)) (Ψ := fun d => MI0 (mrOf d)) fun _ _ ⟨sv, h⟩ =>
      WP.mono (montPrep_mst h.st h.ph h.mb1 h.mb2 h.n h.odd h.n3) fun _ ⟨M, _, h152⟩ =>
        ⟨⟨sv, M, h152.trans h.used⟩, h.ul, rfl, rfl, h.bl⟩)
    (two_map mrOf (fun _ _ h => h) (millerRabin_ct hR))

/-- A test's public data: the candidate and the tape's offset. -/
structure TQD where
  q : PP
  c : Nat
  u : Nat

/-- Before q's test. -/
def TQ (d : TQD) (s : State) : Prop :=
  ∃ sv, St (d.q.with sv) s ∧ d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧
    wv s.mem d.q.B (slot (wOf d.q.bits) 0) (wOf d.q.bits) = (d.c - 1) / 2 ∧ ((d.c - 1) / 2) % 2 = 1 ∧
    word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧ d.u ≤ d.q.r.length

/-- q's test leaks the same from the same candidate and tape. -/
theorem testQ_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two TQ) (test true (.block []) R.name R.code) (Two ME) := by
  unfold test
  simp only [↓reduceIte]
  refine RelCT.assoc (RelCT.seq (two_post ?_
    (Ψ := fun d => TC ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, d.u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩)
    fun _ _ ⟨sv, h, hc, hq, hqo, hu, hul⟩ => WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht => ⟨sv, ht⟩)
    (RelCT.seq (two_post (two_map _ (fun _ _ h => h) (two_taint _ pins_TC (by taint_decide)))
      (Ψ := fun d => TC ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, d.u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩)
      fun _ _ h => WP.block_nil_iff.mpr h)
    (two_map _ (fun _ _ h => h) (testCore_ct hR))))
  exact two_map TQD.q (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩)
    (RelCT.seq (phasePA_ct true) (two_taint _ (pins_PA true) (by taint_decide)))

/-- Before p's test. -/
def TP (d : TQD) (s : State) : Prop :=
  ∃ sv, St (d.q.with sv) s ∧ d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧
    word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧ d.u ≤ d.q.r.length ∧ d.q.L ≤ d.q.r.length

/-- p's test, with `adjust` setting its count of witnesses to `Kf` of the
default, leaks the same from the same candidate and tape. -/
theorem testP_ct {R : RoundImpl} (hR : RoundCall R) {adjust : Prog isa} (Kf : Nat → Nat)
    (hadj : ∀ {p : PP} {c u : Nat} {t : State}, TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits) t →
      WP isa adjust t (TCPre p p.bits c u (Kf (Spec.Ffdh.primeChecks p.bits))))
    (hct : RelCT isa (Two TC) adjust fun _ _ => True) :
    RelCT isa (Two TP) (test false adjust R.name R.code) (Two ME) := by
  unfold test
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (RelCT.seq (two_post ?_
    (Ψ := fun d => TC ⟨d.q, d.q.bits, d.c, d.u, Spec.Ffdh.primeChecks d.q.bits⟩)
    fun _ _ ⟨sv, h, hc, hu, hul, hL⟩ => WP.mono (pPrep_ok h hc hu hul hL) fun _ ht => ⟨sv, ht⟩)
    (RelCT.seq (two_post (two_map _ (fun _ _ h => h) hct)
      (Ψ := fun d => TC ⟨d.q, d.q.bits, d.c, d.u, Kf (Spec.Ffdh.primeChecks d.q.bits)⟩)
      fun _ _ ⟨sv, h⟩ => WP.mono (hadj h) fun _ ht => ⟨sv, ht⟩)
    (two_map _ (fun _ _ h => h) (testCore_ct hR))))
  exact two_map TQD.q (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct)

/-- p's test of its first witness. -/
theorem testP1_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two TP) (test false firstCheck R.name R.code) (Two ME) :=
  testP_ct hR (fun _ => 1) (fun h => firstCheck_ok h) (two_taint _ pins_TC (by taint_decide))

/-- p's test of its other witnesses. -/
theorem testPR_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two TP) (test false restChecks R.name R.code) (Two ME) :=
  testP_ct hR (· - 1) (fun h => restChecks_ok h (by unfold Spec.Ffdh.primeChecks; split <;> decide))
    (two_taint _ pins_TC (by taint_decide))

/-! ## The results -/

/-- Before `finish`: the working space, and `used`'s address in its header. -/
def FS (q : PP) (s : State) : Prop :=
  ∃ Z, Scr s q.B Z ∧ 40 ≤ Z ∧ s.gpr .s6 = q.B ∧ s.mem.readW (q.B + BitVec.ofNat 64 32) 64 = q.up

theorem pins_FS : Pins FS [.s6] := pins_s6 PP.B fun _ _ ⟨_, _, _, h, _⟩ => h

/-- With `used`'s address loaded. -/
def F3 (q : PP) (s : State) : Prop := s.gpr .s6 = q.B ∧ s.gpr .t3 = q.up

theorem pins_F3 : Pins F3 [.t3, .s6] := by
  rintro q s₁ s₂ ⟨a6, a3⟩ ⟨b6, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a6, b6]

theorem St.fs {p : PP} {s : State} (h : St p s) : FS p s := by
  have := h.dims.n
  exact ⟨p.Z, h.scr, by simp only [PP.Z]; omega, h.s6, h.args.usedP'⟩

theorem finish_ct {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2) : RelCT isa (Two FS) (.block (finish r)) fun _ _ => True := by
  have hd : RelCT isa (Two FS) (.block [ldh .t3 hUsedP]) (Two F3) :=
    two_post (two_taint _ pins_FS (by taint_decide)) fun q s ⟨Z, hs, hZ, h6, hu⟩ =>
      WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = q.up) (by
          simp only [ldh, hUsedP]
          brun [h6, hs.ld (d := 32) (n := 8) (by omega), hs.al8 (d := 32) (by omega) (by decide), hu])
          (by rfl) (by rfl))
        fun t ⟨t3, k⟩ => ⟨(k.gpr (by decide)).trans h6, t3⟩
  unfold finish
  rw [List.append_assoc]
  obtain rfl | rfl | rfl := hr
  all_goals exact RelCT.block_append (RelCT.seq hd (two_taint _ pins_F3 (by taint_decide)))

/-- A test's status: 0 without enough octets, 1 if it passed, 2 if not. -/
def statOf : Option (Bool × List Byte) → Nat
  | none => 0
  | some (b, _) => if b then 1 else 2

theorem statOf_le (r : Option (Bool × List Byte)) : statOf r ≤ 2 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp [statOf]

theorem MrEnd.stat {C : Nat} {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {s : State}
    (h : MrEnd p mb N C res s) : word s.mem p.B 160 = BitVec.ofNat 64 (statOf res) := by
  obtain ⟨_, hn, hs⟩ := h
  rcases res with _ | ⟨b, rest⟩
  · exact hn rfl
  · exact (hs b rest rfl).1

theorem pins_ME : Pins ME [.s6] := pins_s6 (fun a : MrD => a.q.B) fun _ _ ⟨_, h, _⟩ => h.st.s6

/-- With a test's status in `t3`. -/
def SL (a : MrD) (t : State) : Prop :=
  (∃ sv, MSt (a.q.with sv) a.mb a.N a.K t) ∧ t.gpr .t3 = BitVec.ofNat 64 (statOf a.res)

theorem pins_SL : Pins SL [.t3, .s6] := by
  rintro a s₁ s₂ ⟨⟨_, M₁⟩, a3⟩ ⟨⟨_, M₂⟩, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [M₁.st.s6, M₂.st.s6]; rfl

theorem statLoad_ct : RelCT isa (Two ME) (.block [ldh .t3 hStat]) (Two SL) :=
  two_post (two_taint _ pins_ME (by taint_decide)) fun _ _ ⟨sv, hE⟩ =>
    WP.mono (statLoad_ok hE.1) fun _ ⟨Mt, t3, _⟩ => ⟨⟨sv, Mt⟩, t3.trans hE.stat⟩

theorem finSL_ct {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2) {Φ : MrD → State → Prop}
    (h : ∀ a s, Φ a s → ∃ sv, MSt (a.q.with sv) a.mb a.N a.K s) :
    RelCT isa (Two Φ) (.block (finish r)) fun _ _ => True :=
  two_map MrD.q (fun a s hs => let ⟨_, M⟩ := h a s hs; M.st.fs) (finish_ct hr)

/-- After a failed test of q. -/
theorem qResult_ct : RelCT isa (Two ME) qResult fun _ _ => True := by
  unfold qResult
  refine RelCT.seq statLoad_ct (two_ite' (fun a => decide (statOf a.res = 0)) (fun a s h => ?_)
    (finSL_ct (.inl rfl) fun _ _ h => h.1.1) (finSL_ct (.inr (.inr rfl)) fun _ _ h => h.1.1))
  exact eval_zero_ofNat s .t3 (by have := statOf_le a.res; omega) h.2

/-- With a test's status less one in `t3`. -/
def SL1 (a : MrD) (t : State) : Prop :=
  (∃ sv, MSt (a.q.with sv) a.mb a.N a.K t) ∧ t.gpr .t3 = BitVec.ofNat 64 (statOf a.res) - BitVec.ofNat 64 1

/-- In a modulus's working space. -/
def MS (a : MrD) (t : State) : Prop := ∃ sv, MSt (a.q.with sv) a.mb a.N a.K t

theorem pins_MS {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → MS a s) : Pins Φ [.a7, .s5, .t0, .s6] :=
  pins_ph MrD.q MrD.mb fun a s hs => let ⟨sv, M⟩ := h a s hs; ⟨sv, _, M.st, M.ph⟩

theorem sub1_ct {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → SL a s) :
    RelCT isa (Two Φ) (.block [.addi .t3 .t3 (-1)]) (Two SL1) :=
  two_post (two_taint _ (pins_MS fun a s hs => (h a s hs).1) (by taint_decide)) fun a s hs => by
    obtain ⟨⟨sv, M⟩, h3⟩ := h a s hs
    exact WP.mono (sub1_ok M h3) fun t ⟨Mt, t3, _⟩ => ⟨⟨sv, Mt⟩, t3⟩

/-- With `out`, `out_len` and p's last octet's address loaded. -/
def W4 (a : MrD) (t : State) : Prop :=
  t.gpr .t3 = a.q.op ∧ t.gpr .t4 = BitVec.ofNat 64 a.q.L ∧ t.gpr .t5 = off a.q.B (256 + (a.q.L - 1))

theorem pins_W4 : Pins W4 [.t3, .t4, .t5] := by
  rintro a s₁ s₂ ⟨a3, a4, a5⟩ ⟨b3, b4, b5⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

theorem writeP_ct {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → MS a s) :
    RelCT isa (Two Φ) writeP (Two fun (a : MrD) => FS a.q) := by
  refine two_post ?_ fun a s hs => ?_
  · unfold writeP
    refine RelCT.seq (two_post (two_taint _ (pins_MS h) (by taint_decide)) (Ψ := W4) fun a s hs => ?_)
      (two_taint _ pins_W4 (by taint_decide))
    obtain ⟨sv, M⟩ := h a s hs
    have hdn := M.st.dims.n
    have hb1 := M.st.dims.b1
    have hLe : (a.q.with sv).L = ((a.q.with sv).bits + 7) / 8 := rfl
    have hZe : (a.q.with sv).Z = 8 * (a.q.with sv).n := rfl
    exact WP.mono (writeHead_ok M.st.scr M.st.s6 (M.ph.a7.trans (by rw [slot_zero])) M.st.args.out'
      M.st.args.len' (by omega) (by omega)) fun t ⟨⟨t5, t3, t4, _⟩, _⟩ => ⟨t3, t4, t5⟩
  · obtain ⟨sv, M⟩ := h a s hs
    have h := M.st
    have hdn := h.dims.n
    have hb1 := h.dims.b1
    have hnw := h.scr.nowrap
    have hLe : (a.q.with sv).L = ((a.q.with sv).bits + 7) / 8 := rfl
    have hZe : (a.q.with sv).Z = 8 * (a.q.with sv).n := rfl
    refine WP.mono (WP.rdwr (writeP_ok h.scr h.bufs.outW h.bufs.oNW h.s6 (M.ph.a7.trans (by rw [slot_zero]))
      h.args.out' h.args.len' (by omega) (by omega) h.bufs.sepO)) fun t₁ ⟨⟨⟨_, tout⟩, k₁⟩, _, _, sp₁⟩ => ?_
    have hws₁ : ∀ x, ofs (a.q.with sv).B x < (a.q.with sv).Z → t₁.mem x = s.mem x := fun x hx =>
      tout x (Or.inr (by
        by_contra hc'
        have := h.bufs.sepO x (by omega)
        omega))
    have E₁ := h.toE.frame hws₁ k₁ sp₁ (by decide)
    exact ⟨_, E₁.scr, by omega, E₁.s6, (word_of_ws hws₁ (d := 32) (by omega) hnw).trans h.args.usedP'⟩

/-- After p's test. -/
theorem pResult_ct : RelCT isa (Two ME) pResult fun _ _ => True := by
  unfold pResult
  refine RelCT.seq statLoad_ct (two_ite' (fun a => decide (statOf a.res = 0))
    (fun a s h => eval_zero_ofNat s .t3 (by have := statOf_le a.res; omega) h.2)
    (finSL_ct (.inl rfl) fun _ _ h => h.1.1) ?_)
  refine RelCT.seq (sub1_ct fun _ _ h => h.1) (two_ite' (fun a => decide (statOf a.res = 1)) (fun a s h => ?_)
    (RelCT.seq (writeP_ct fun _ _ h => h.1.1) (two_map MrD.q (fun _ _ h => h) (finish_ct (.inr (.inl rfl)))))
    (finSL_ct (.inr (.inr rfl)) fun _ _ h => h.1.1))
  rw [eval_zero, h.2]
  exact congrArg some (stat_one (by have := statOf_le a.res; omega))

/-! ## The tests -/

theorem MrEnd.of_mem {C : Nat} {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {s t : State}
    (h : MrEnd p mb N C res s) (M : MSt p mb N C t) (hm : t.mem = s.mem) : MrEnd p mb N C res t :=
  ⟨M, fun h' => by rw [hm]; exact h.2.1 h', fun b r h' => by rw [hm]; exact h.2.2 b r h'⟩

/-- The candidate's facts the tests carry. -/
def FX (d : TQD) : Prop :=
  d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧ d.q.L ≤ d.q.r.length ∧
    ((d.c - 1) / 2) % 2 = 1

/-- Before the tests. -/
def TS (d : TQD) (s : State) : Prop := TP d s ∧ ((d.c - 1) / 2) % 2 = 1

/-- After a test whose data are `E d`. -/
def TE (E : TQD → MrD) (d : TQD) (t : State) : Prop := ME (E d) t ∧ FX d

/-- The rest of the tape after a test's witnesses. -/
def restOf : Option (Bool × List Byte) → List Byte
  | none => []
  | some (_, r) => r

/-- The tape's offset after a test's witnesses. -/
def uAfter (res : Option (Bool × List Byte)) (q : PP) : Nat := q.r.length - (restOf res).length

theorem ME.passed {a : MrD} {t : State} (h : ME a t) (h1 : statOf a.res = 1) :
    ∃ sv, MSt (a.q.with sv) a.mb a.N a.K t ∧
      word t.mem a.q.B 152 = BitVec.ofNat 64 (uAfter a.res a.q) ∧ uAfter a.res a.q ≤ a.q.r.length := by
  obtain ⟨sv, M, -, hsome⟩ := h
  revert h1 hsome
  unfold uAfter
  generalize a.res = r
  intro h1 hsome
  rcases r with _ | ⟨_ | _, rest⟩
  · simp [statOf] at h1
  · simp [statOf] at h1
  · obtain ⟨-, u, hul, hr, hU⟩ := hsome true rest rfl
    have hul' : u ≤ a.q.r.length := hul
    have eu : a.q.r.length - (restOf (some (true, rest))).length = u := by
      subst hr; show a.q.r.length - (a.q.r.drop u).length = u; rw [List.length_drop]; omega
    exact ⟨sv, M, by rw [eu]; exact hU, by rw [eu]; exact hul'⟩

theorem pins_TE (E : TQD → MrD) {Φ : TQD → State → Prop} (h : ∀ d s, Φ d s → TE E d s) :
    Pins Φ [.a7, .s5, .t0, .s6] :=
  pins_ph (fun d => (E d).q) (fun d => (E d).mb) fun d s hs => let ⟨⟨sv, M, _⟩, _⟩ := h d s hs; ⟨sv, _, M.st, M.ph⟩

/-- After a test whose data are `E d`: `qResult` unless it passed, else
`cont`. -/
theorem stage_ct (E : TQD → MrD) {cont : Prog isa}
    (hc : RelCT isa (Two fun d t => TE E d t ∧ statOf (E d).res = 1) cont fun _ _ => True) :
    RelCT isa (Two (TE E)) (.seq (.block [ldh .t3 hStat, .addi .t3 .t3 (-1)]) (.ite (.zero .t3) cont qResult))
      fun _ _ => True := by
  have hs : RelCT isa (Two (TE E)) (.block [ldh .t3 hStat, .addi .t3 .t3 (-1)])
      (Two fun d t => isa.eval (.zero .t3) t = some (decide (statOf (E d).res = 1)) ∧ TE E d t) :=
    two_post (two_taint _ (pins_TE E fun _ _ h => h) (by taint_decide)) fun d _ ⟨⟨sv, hE⟩, hx⟩ =>
      WP.mono (stat1_ok hE.1 (v := statOf (E d).res) (by have := statOf_le (E d).res; omega) hE.stat)
        fun _ ⟨he, M, hm⟩ => ⟨he, ⟨sv, hE.of_mem M hm⟩, hx⟩
  exact RelCT.seq hs (two_ite' (fun d => decide (statOf (E d).res = 1)) (fun _ _ h => h.1)
    (two_mono (fun _ _ h => ⟨h.1.2, of_decide_eq_true h.2⟩) hc) (two_map E (fun _ _ h => h.1.2.1) qResult_ct))

/-- p's first witness. -/
def E1 (d : TQD) : MrD := mrOf ⟨d.q, d.q.bits, d.c, d.u, 1⟩

/-- q's test's data. -/
def d2 (d : TQD) : TQD := ⟨d.q, d.c, uAfter (E1 d).res d.q⟩

/-- q's witnesses. -/
def E2 (d : TQD) : MrD := mrOf ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, (d2 d).u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩

/-- The test of p's other witnesses' data. -/
def d3 (d : TQD) : TQD := ⟨d.q, d.c, uAfter (E2 d).res d.q⟩

/-- p's other witnesses. -/
def E3 (d : TQD) : MrD := mrOf ⟨d.q, d.q.bits, d.c, (d3 d).u, Spec.Ffdh.primeChecks d.q.bits - 1⟩

/-- p's other witnesses and the result leak the same. -/
theorem testRest_ct {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two fun d t => TE E2 d t ∧ statOf (E2 d).res = 1) (testRest R.name R.code) fun _ _ => True := by
  unfold testRest
  have hp : ∀ d t, TE E2 d t ∧ statOf (E2 d).res = 1 → TP (d3 d) t := fun d t ⟨⟨hE, hc, hL, _⟩, h1⟩ => by
    obtain ⟨sv, M, hU, hu⟩ := hE.passed h1
    exact ⟨sv, M.st, hc, hU, hu, hL⟩
  refine RelCT.seq (two_post ((two_map d3 hp (testPR_ct hR)).mono (fun _ _ h => h) fun _ _ _ => trivial)
    (Ψ := fun d => ME (E3 d)) fun d _ h => ?_) (two_map E3 (fun _ _ h => h) pResult_ct)
  obtain ⟨sv, st, hc, hU, hu, hL⟩ := hp d _ h
  exact WP.mono (testPR_ok hR st hc hU hu hL) fun _ ht => ⟨sv, ht⟩

/-- q, from p, its test and the rest leak the same. -/
theorem testQ_cts {R : RoundImpl} (hR : RoundCall R) :
    RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) (testQ R.name R.code) fun _ _ => True := by
  unfold testQ
  have hh : RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) halveQ
      (Two fun d t => TQ (d2 d) t ∧ FX d) :=
    two_post (two_taint _ (pins_TE E1 fun _ _ h => h.1) (by taint_decide)) fun d _ ⟨⟨hE, hx⟩, h1⟩ => by
      obtain ⟨sv, M, hU, hu⟩ := hE.passed h1
      exact WP.mono (halveQ_from M hx.1 hU) fun _ ⟨st, hq, hU'⟩ => ⟨⟨sv, st, hx.1, hq, hx.2.2, hU', hu⟩, hx⟩
  have hq : RelCT isa (Two fun d t => TQ (d2 d) t ∧ FX d) (test true (.block []) R.name R.code) (Two (TE E2)) :=
    two_post ((two_map d2 (fun _ _ h => h.1) (testQ_ct hR)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, h, hc, hq, hqo, hu, hul⟩, hx⟩ =>
        WP.mono (testQ_ok hR h hc hq hqo hu hul) fun _ ht => ⟨⟨sv, ht⟩, hx⟩
  exact RelCT.seq hh (RelCT.seq hq (stage_ct E2 (testRest_ct hR)))

/-- The tests leak the same from the same candidate and tape. -/
theorem tests_ct {R : RoundImpl} (hR : RoundCall R) : RelCT isa (Two TS) (tests R.name R.code) fun _ _ => True := by
  unfold tests
  have h1 : RelCT isa (Two TS) (test false firstCheck R.name R.code) (Two (TE E1)) :=
    two_post ((two_mono (fun _ _ h => h.1) (testP1_ct hR)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, h, hc, hu, hul, hL⟩, hqo⟩ =>
        WP.mono (testP1_ok hR h hc hu hul hL) fun _ ht => ⟨⟨sv, ht⟩, hc, hL, hqo⟩
  exact RelCT.seq h1 (stage_ct E1 (testQ_cts hR))

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
