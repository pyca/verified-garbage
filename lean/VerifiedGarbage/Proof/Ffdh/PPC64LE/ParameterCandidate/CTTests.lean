module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTRes
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTRes

/-!
# An FFDH parameter candidate on PPC64LE: the tests in constant time

q's test, then a branch on its status, which its witnesses decide; p's
test, from the offset in the tape where q's left off (`pD`), then its
result.
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

theorem MrEnd.of_mem {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {s t : State}
    (h : MrEnd p mb N res s) (M : MSt p mb N t) (hm : t.mem = s.mem) : MrEnd p mb N res t :=
  ⟨M, fun h' => by rw [hm]; exact h.2.1 h', fun b r h' => by rw [hm]; exact h.2.2 b r h'⟩

/-- Before the tests. -/
def TS (d : TQD) (s : State) : Prop := TQ d s ∧ d.q.L ≤ d.q.r.length

/-- q's witnesses. -/
def resQ (d : TQD) : Option (Bool × List Byte) :=
  checkWitnesses ((d.c - 1) / 2) (Spec.Ffdh.primeChecks (d.q.bits - 1)) (d.q.r.drop d.u)

/-- After q's test. -/
def TS1 (d : TQD) (t : State) : Prop :=
  (∃ sv toc, MrEnd (d.q.with sv toc) (d.q.bits - 1) ((d.c - 1) / 2) (resQ d) t) ∧
    d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧ d.q.L ≤ d.q.r.length

/-- With q's status, less one, tested. -/
def TS2 (d : TQD) (t : State) : Prop :=
  isa.eval (.zero .d .r3) t = some (decide (statOf (resQ d) = 1)) ∧ TS1 d t

/-- The rest of the tape after a test's witnesses. -/
def restOf : Option (Bool × List Byte) → List Byte
  | none => []
  | some (_, r) => r

/-- p's test's data. -/
def pD (d : TQD) : TQD := ⟨d.q, d.c, d.q.r.length - (restOf (resQ d)).length⟩

/-- q's result's data. -/
def qD (d : TQD) : MrD := ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, resQ d, 0, 0⟩

theorem tp_of {d : TQD} {s : State} (h : TS2 d s ∧ decide (statOf (resQ d) = 1) = true) : TP (pD d) s := by
  obtain ⟨⟨_, ⟨sv, toc, hE⟩, hc, hL⟩, h1⟩ := h
  obtain ⟨M, -, hsome⟩ := hE
  have e : (pD d).u = d.q.r.length - (restOf (resQ d)).length := rfl
  generalize resQ d = r at h1 hsome e
  rcases r with _ | ⟨_ | _, rest⟩
  · simp [statOf] at h1
  · simp [statOf] at h1
  · obtain ⟨-, u, hul, rfl, hU⟩ := hsome true _ rfl
    have hul' : u ≤ d.q.r.length := hul
    have eu : (pD d).u = u := by
      rw [e]; show d.q.r.length - (d.q.r.drop u).length = u; rw [List.length_drop]; omega
    exact ⟨sv, toc, M.st, hc, by rw [eu]; exact hU, by rw [eu]; exact hul, hL⟩

/-- The tests leak the same from the same candidate and tape. -/
theorem tests_ct (R : RoundImpl) : RelCT isa (Two TS) (tests R.name R.code) fun _ _ => True := by
  unfold tests
  have hq : RelCT isa (Two TS) (test true R.name R.code) (Two TS1) :=
    two_post ((two_mono (fun _ _ h => h.1) (testQ_ct R)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, toc, h, hc, hq, hqo, hu, hul⟩, hL⟩ =>
        WP.mono (testQ_ok R h hc hq hqo hu hul) fun _ ht => ⟨⟨sv, toc, ht⟩, hc, hL⟩
  have hs : RelCT isa (Two TS1) (.block [ldh .r3 hStat, .subi .r3 .r3 1]) (Two TS2) :=
    two_post (two_taint _ (pins_r31 (fun d : TQD => d.q.B) fun _ _ ⟨⟨_, _, hE⟩, _⟩ => hE.1.st.r31)
        (by taint_decide)) fun d _ ⟨⟨sv, toc, hE⟩, hc, hL⟩ =>
      WP.mono (stat1_ok hE.1 (v := statOf (resQ d)) (by have := statOf_le (resQ d); omega) hE.stat)
        fun _ ⟨he, M, hm⟩ => ⟨he, ⟨sv, toc, hE.of_mem M hm⟩, hc, hL⟩
  exact RelCT.seq hq (RelCT.seq hs (two_ite' (fun d => decide (statOf (resQ d) = 1)) (fun _ _ h => h.1)
    (RelCT.seq ((two_map pD (fun _ _ h => tp_of h) (testP_ct R))) pResult_ct)
    (two_map qD (fun _ _ h => h.1.2.1) qResult_ct)))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
