module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTRes
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTRes

/-!
# An FFDH parameter candidate on PPC64LE: the tests in constant time

p's first witness, then a branch on its status, which its witnesses
decide; q, from p, and its test, from the offset in the tape where p's
left off (`d2`), then a branch on its status; p's other witnesses (`d3`),
then the result.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

theorem pins_r31 {α : Type} {Φ : α → State → Prop} (B : α → Addr) (h : ∀ a s, Φ a s → s.gpr .r31 = B a) :
    Pins Φ [.r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h a _ h₁, h a _ h₂]

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
    ∃ sv toc, MSt (a.q.with sv toc) a.mb a.N a.K t ∧
      word t.mem a.q.B 152 = BitVec.ofNat 64 (uAfter a.res a.q) ∧ uAfter a.res a.q ≤ a.q.r.length := by
  obtain ⟨sv, toc, M, -, hsome⟩ := h
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
    exact ⟨sv, toc, M, by rw [eu]; exact hU, by rw [eu]; exact hul'⟩

theorem pins_TE (E : TQD → MrD) {Φ : TQD → State → Prop} (h : ∀ d s, Φ d s → TE E d s) :
    Pins Φ [.r10, .r11, .r29, .r31] := by
  intro d s₁ s₂ h₁ h₂ r hr
  obtain ⟨⟨_, _, M₁, -⟩, -⟩ := h d s₁ h₁
  obtain ⟨⟨_, _, M₂, -⟩, -⟩ := h d s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [M₁.ph.r10, M₂.ph.r10]; rfl
  · rw [M₁.ph.r11, M₂.ph.r11]
  · rw [M₁.ph.r29, M₂.ph.r29]
  · rw [M₁.st.r31, M₂.st.r31]; rfl

/-- After a test whose data are `E d`: `qResult` unless it passed, else
`cont`. -/
theorem stage_ct (E : TQD → MrD) {cont : Prog isa}
    (hc : RelCT isa (Two fun d t => TE E d t ∧ statOf (E d).res = 1) cont fun _ _ => True) :
    RelCT isa (Two (TE E)) (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1]) (.ite (.zero .d .r3) cont qResult))
      fun _ _ => True := by
  have hs : RelCT isa (Two (TE E)) (.block [ldh .r3 hStat, .subi .r3 .r3 1])
      (Two fun d t => isa.eval (.zero .d .r3) t = some (decide (statOf (E d).res = 1)) ∧ TE E d t) :=
    two_post (two_taint _ (pins_TE E fun _ _ h => h) (by taint_decide)) fun d _ ⟨⟨sv, toc, hE⟩, hx⟩ =>
      WP.mono (stat1_ok hE.1 (v := statOf (E d).res) (by have := statOf_le (E d).res; omega) hE.stat)
        fun _ ⟨he, M, hm⟩ => ⟨he, ⟨sv, toc, hE.of_mem M hm⟩, hx⟩
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
theorem testRest_ct (R : RoundImpl) :
    RelCT isa (Two fun d t => TE E2 d t ∧ statOf (E2 d).res = 1) (testRest R.name R.code) fun _ _ => True := by
  unfold testRest
  have hp : ∀ d t, TE E2 d t ∧ statOf (E2 d).res = 1 → TP (d3 d) t := fun d t ⟨⟨hE, hc, hL, _⟩, h1⟩ => by
    obtain ⟨sv, toc, M, hU, hu⟩ := hE.passed h1
    exact ⟨sv, toc, M.st, hc, hU, hu, hL⟩
  refine RelCT.seq (two_post ((two_map d3 hp (testPR_ct R)).mono (fun _ _ h => h) fun _ _ _ => trivial)
    (Ψ := fun d => ME (E3 d)) fun d _ h => ?_) (two_map E3 (fun _ _ h => h) pResult_ct)
  obtain ⟨sv, toc, st, hc, hU, hu, hL⟩ := hp d _ h
  exact WP.mono (testPR_ok R st hc hU hu hL) fun _ ht => ⟨sv, toc, ht⟩

/-- q, from p, its test and the rest leak the same. -/
theorem testQ_cts (R : RoundImpl) :
    RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) (testQ R.name R.code) fun _ _ => True := by
  unfold testQ
  have hh : RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) halveQ
      (Two fun d t => TQ (d2 d) t ∧ FX d) :=
    two_post (two_taint _ (pins_TE E1 fun _ _ h => h.1) (by taint_decide)) fun d _ ⟨⟨hE, hx⟩, h1⟩ => by
      obtain ⟨sv, toc, M, hU, hu⟩ := hE.passed h1
      exact WP.mono (halveQ_from M hx.1 hU) fun _ ⟨st, hq, hU'⟩ => ⟨⟨sv, toc, st, hx.1, hq, hx.2.2, hU', hu⟩, hx⟩
  have hq : RelCT isa (Two fun d t => TQ (d2 d) t ∧ FX d) (test true (.block []) R.name R.code) (Two (TE E2)) :=
    two_post ((two_map d2 (fun _ _ h => h.1) (testQ_ct R)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, toc, h, hc, hq, hqo, hu, hul⟩, hx⟩ =>
        WP.mono (testQ_ok R h hc hq hqo hu hul) fun _ ht => ⟨⟨sv, toc, ht⟩, hx⟩
  exact RelCT.seq hh (RelCT.seq hq (stage_ct E2 (testRest_ct R)))

/-- The tests leak the same from the same candidate and tape. -/
theorem tests_ct (R : RoundImpl) : RelCT isa (Two TS) (tests R.name R.code) fun _ _ => True := by
  unfold tests
  have h1 : RelCT isa (Two TS) (test false firstCheck R.name R.code) (Two (TE E1)) :=
    two_post ((two_mono (fun _ _ h => h.1) (testP1_ct R)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, toc, h, hc, hu, hul, hL⟩, hqo⟩ =>
        WP.mono (testP1_ok R h hc hu hul hL) fun _ ht => ⟨⟨sv, toc, ht⟩, hc, hL, hqo⟩
  exact RelCT.seq h1 (stage_ct E1 (testQ_cts R))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
