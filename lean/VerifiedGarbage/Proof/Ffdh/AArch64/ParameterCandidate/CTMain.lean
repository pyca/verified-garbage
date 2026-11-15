module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTPieces
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTTest
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Result
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Tests
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTPieces
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTTest
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Result
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Tests
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots

/-!
# An FFDH parameter candidate on AArch64: constant time of `main`

`main`'s stages (`Stg`, `Main.lean`), each piece from the stage before it
(`CTPieces.lean`, `CTTest.lean`), the branches on the flag so far
(`check_ct`: after the congruence, `p`'s sieve by the table's first words,
`q`'s oddness, `q`'s sieve and `p`'s whole sieve), which the public data
fixes, and the tests (`tests_ct`), whose branches the results of
Miller–Rabin fix.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The working space of `p`'s words. -/
abbrev PP.ws (p : PP) : WsP := ⟨p.B, p.Z, mW p.bits⟩

/-- Before `main`. -/
def M0 (p : PP) (s : State) : Prop :=
  PH p s ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L ∧ p.L ≤ p.r.length

/-! ## The tests -/

/-- The status `millerRabin` leaves. -/
def statF (res : Option (Bool × List Byte)) : Nat :=
  match res with
  | none => 0
  | some (b, _) => if b then 1 else 2

/-- The octets read after `millerRabin`. -/
def uOfRes (r : List Byte) (res : Option (Bool × List Byte)) : Nat :=
  match res with
  | none => 0
  | some (_, rest) => r.length - rest.length

theorem OutUp.mono' {s : State} {B : Addr} {Z : Nat} {op up : Addr} {k k' : Nat} (h : OutUp s B Z op up k)
    (hk : k' ≤ k) : OutUp s B Z op up k' :=
  ⟨h.upw, h.upZ, fun j hj => h.outw j (by omega_arith), fun j hj => h.outZ j (by omega_arith), fun j hj => h.ou j (by omega_arith)⟩

theorem te_stat {q : TQ} {s : State} (h : TE q s) :
    word s.mem q.p.B (8 * kStat) = BitVec.ofNat 64 (statF q.res) := by
  obtain ⟨_, s₀, he⟩ := h
  have st := MrEnd.stat he
  rcases hr : q.res with _ | ⟨b, rest⟩
  · exact st.1 hr
  · exact (st.2 b rest hr).1

theorem te_fix {q : TQ} {s : State} (h : TE q s) : MrFix q.p q.w q.N q.mb q.K s := by
  obtain ⟨_, s₀, he⟩ := h; exact he.1

/-- The result's public data after a test. -/
abbrev endFOf (q : TQ) : FQ := ⟨q.p.B, q.p.Z, q.w, q.p.op, q.p.up, mLen q.mb, statF q.res⟩

theorem te_endF {q : TQ} {s : State} (h : TE q s) : EndF (endFOf q) s := by
  have hd := h.1
  have fix := te_fix h
  have hmbb := hd.mbb
  refine ⟨fix.st.ws, fix.st.args.out, fix.len, fix.st.args.usedP, OutUp.mono' fix.st.ou (by simp only [mLen, PP.L]; omega_arith),
    te_stat h, ?_⟩
  show statF q.res < 4
  unfold statF; split <;> (try split) <;> decide

/-- Before the tests. -/
def TQd (p : PP) (s : State) : Prop := Stg p (cOf p) s ∧ ((cOf p - 1) / 2) % 2 = 1

/-- The first test's public data: `p`'s first witness. -/
abbrev d1 (p : PP) : TD := ⟨p, p.bits, cOf p, p.L, 1⟩

/-- The second's: `q`'s witnesses. -/
abbrev d2 (p : PP) : TD :=
  ⟨p, p.bits - 1, (cOf p - 1) / 2, uOfRes p.r (d1 p).tq.res, Spec.Ffdh.primeChecks (p.bits - 1)⟩

/-- The third's: `p`'s others. -/
abbrev d3 (p : PP) : TD := ⟨p, p.bits, cOf p, uOfRes p.r (d2 p).tq.res, Spec.Ffdh.primeChecks p.bits - 1⟩

/-- `q` is odd. -/
abbrev QOdd (p : PP) : Prop := ((cOf p - 1) / 2) % 2 = 1

/-- The Montgomery setup, the exponent and the witnesses of a test of
`N p` of `mb p` bits by `K p` witnesses from octet `u p`. -/
theorem tail_ct (M : Mont) (R : Kernel) (mb N u K : PP → Nat) :
    RelCT isa (Two fun p t => TT p (mb p) (N p) (u p) (K p) t ∧ QOdd p)
      (seqs (montPrep M.mm ++ expSetup ++ VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run))
      (Two fun p t => TE (⟨p, mb p, N p, u p, K p⟩ : TD).tq t ∧ QOdd p) :=
  two_post ((two_map (fun p => (⟨p, mb p, N p, u p, K p⟩ : TD)) (fun _ _ h => h.1) (testTail_ct M R)).mono
    (fun _ _ h => h) fun _ _ _ => trivial) fun _ s h =>
      WP.mono (testTail_ok M R h.1) fun _ he => ⟨⟨h.1.dims, s, he⟩, h.2⟩

/-- Before a test of `p` from octet `u p`. -/
def PStart (u : PP → Nat) (p : PP) (s : State) : Prop :=
  (∃ w, PSt p w s) ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u p) ∧ u p ≤ p.r.length ∧ p.L ≤ p.r.length ∧
    QOdd p

/-- A test of `p` from octet `u p`, its witness count changed by `adjust` to
`K p`, leaks the same in runs with the same public data. -/
theorem testP_ct (M : Mont) (R : Kernel) (u K : PP → Nat) {adjust : Prog isa} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) adjust hc).isSome = true)
    (hadj : ∀ p s, TT p p.bits (cOf p) (u p) (Spec.Ffdh.primeChecks p.bits) s →
      WP isa adjust s fun t => TT p p.bits (cOf p) (u p) (K p) t) :
    RelCT isa (Two (PStart u)) (seqs (test false [adjust] M.mm R.run))
      (Two fun p t => TE (⟨p, p.bits, cOf p, u p, K p⟩ : TD).tq t ∧ QOdd p) := by
  rw [test_false']
  refine ct_app' (by simp [phase]) (by simp) (Ψ := fun p t => TT p p.bits (cOf p) (u p)
    (Spec.Ffdh.primeChecks p.bits) t ∧ QOdd p) ?_ ?_
  · refine two_post (ct_app' (by simp [phase]) (by simp [shapeP, loadA]) (Ψ := fun p t => SP p t)
      (two_post (two_map id (fun _ _ h => h.1.choose_spec.ph) (phase_ct false)) fun p s h => ?_)
      (two_map id (fun _ _ h => h) shapeP_ct)) fun p s h => ?_
    · refine WP.mono (phase_ok h.1.choose_spec.ph false) fun t ht => ?_
      have hmb : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
      have st := ht.st
      rw [hmb] at st
      exact ⟨st, by have := ht.len; rw [hmb] at this; exact this, h.2.2.2.1⟩
    · exact WP.mono (pPhase_ok h.1.choose_spec.ph rfl h.2.1 h.2.2.1 h.2.2.2.1) fun t ⟨ht', _⟩ => ⟨ht', h.2.2.2.2⟩
  refine ct_app' (a := [adjust]) (by simp) (by simp [montPrep])
    (Ψ := fun p t => TT p p.bits (cOf p) (u p) (K p) t ∧ QOdd p) ?_
    (tail_ct M R (fun p => p.bits) cOf u K)
  rw [seqs_one]
  exact two_piece [.x0] (pins_ws' (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits)
    fun _ _ h => h.1.st.ws) ht fun p s h => WP.mono (hadj p s h.1) fun t ht => ⟨ht, h.2⟩

/-- Before the test of `q` from octet `u p`. -/
def QStart (u : PP → Nat) (p : PP) (s : State) : Prop :=
  PSt p (mW p.bits) s ∧ wv s.mem p.B (slot (mW p.bits) aN) (mW p.bits) = (cOf p - 1) / 2 ∧
    QOdd p ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (u p) ∧ u p ≤ p.r.length ∧ p.L ≤ p.r.length

theorem testQ_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two (QStart fun p => (d2 p).u)) (seqs (test true [] M.mm R.run))
      (Two fun p t => TE (d2 p).tq t ∧ QOdd p) := by
  rw [test_true]
  refine ct_app' (by simp [phase]) (by simp [montPrep])
    (Ψ := fun p t => TT p (d2 p).mb (d2 p).N (d2 p).u (d2 p).K t ∧ QOdd p)
    (two_post (two_map id (fun _ _ h => h.1.ph) (phase_ct true)) fun p s h =>
      WP.mono (qPhase_ok h.1 rfl h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun _ ⟨ht, _⟩ =>
        ⟨ht, h.2.2.1⟩)
    (tail_ct M R (fun p => (d2 p).mb) (fun p => (d2 p).N) (fun p => (d2 p).u) (fun p => (d2 p).K))

/-- After a test whose public data are `f p`: `qResult` unless it passed,
else `cont`. -/
theorem stage_ct (f : PP → TQ) {cont : Prog isa}
    (hc : RelCT isa (Two fun p t => (TE (f p) t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (f p).res = 1)) ∧ isa.eval (.zero .x .x3) t = some true) cont
      fun _ _ => True) :
    RelCT isa (Two fun p t => TE (f p) t ∧ QOdd p)
      (seqs [.block [ldh .x3 kStat, .subImm .x .x3 .x3 1], .ite (.zero .x .x3) cont qResult]) fun _ _ => True := by
  simp only [seqs]
  have pw : ∀ {Φ : PP → State → Prop}, (∀ p s, Φ p s → TE (f p) s) → Pins Φ [.x0] := fun h =>
    pins_ws' (fun p => (f p).p.B) (fun p => (f p).p.Z) (fun p => (f p).w) fun _ _ hx => (te_fix (h _ _ hx)).st.ws
  refine RelCT.seq (two_piece (Ψ := fun p t => (TE (f p) t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (f p).res = 1))) [.x0] (pw fun _ _ h => h.1) (by taint_decide)
      fun p s h => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_)
  · have fix := te_fix h.1
    refine WP.mono (stat1_ok fix.st.ws (v := statF (f p).res) (by unfold statF; split <;> (try split) <;> decide)
      (te_stat h.1)) fun t ⟨hz, hm, k⟩ => ⟨⟨?_, h.2⟩, hz⟩
    obtain ⟨⟨hd, s₀, he⟩, -⟩ := h
    have hEZ := hd.eZ
    exact ⟨hd, s₀, he.1.same hEZ hm k (by decide), by rw [hm]; exact he.2.1, fun b rest h' => by
      rw [hm]; exact he.2.2.1 b rest h', by rw [hm]; exact he.2.2.2.1, (he.2.2.2.2.trans k).mono (by decide)⟩
  · exact hc.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) h) fun _ _ h => h
  · exact two_map (fun p => endFOf (f p)) (fun _ _ h => te_endF h.1.1.1) qResult_ct

/-- A test that passed. -/
def PQ (q : TQ) (s : State) : Prop := TE q s ∧ isa.eval (.zero .x .x3) s = some true

theorem pq_res {q : TQ} {s : State} (h : PQ q s) (h3 : isa.eval (.zero .x .x3) s = some (decide (statF q.res = 1))) :
    ∃ rest, q.res = some (true, rest) := by
  have h2 := h.2
  rw [h3] at h2
  have h1 : statF q.res = 1 := by simpa using h2
  unfold statF at h1
  rcases hr : q.res with _ | ⟨b, rest⟩ <;> rw [hr] at h1
  · cases h1
  · cases b
    · cases h1
    · exact ⟨rest, rfl⟩

/-- What a test that passed leaves: the octets it read. -/
theorem te_passed {q : TQ} {s : State} (h : TE q s) (h3 : isa.eval (.zero .x .x3) s = some (decide (statF q.res = 1)))
    (ht : isa.eval (.zero .x .x3) s = some true) :
    MrFix q.p q.w q.N q.mb q.K s ∧ word s.mem q.p.B (8 * kUsed) = BitVec.ofNat 64 (uOfRes q.p.r q.res) ∧
      uOfRes q.p.r q.res ≤ q.p.r.length := by
  obtain ⟨rest, hr⟩ := pq_res ⟨h, ht⟩ h3
  obtain ⟨hd, s₀, he⟩ := h
  obtain ⟨u, hu, hrest, hU⟩ := (he.2.2.1 true rest hr).2
  have hu' : uOfRes q.p.r q.res = u := by
    rw [hr]; simp only [uOfRes]; rw [hrest, List.length_drop]; omega_arith
  exact ⟨he.1, by rw [hu']; exact hU, by rw [hu']; exact hu⟩

/-- `p`'s other witnesses, after `q` passed. -/
theorem testRest_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two fun p t => (TE (d2 p).tq t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (d2 p).tq.res = 1)) ∧ isa.eval (.zero .x .x3) t = some true)
      (testRest M.mm R.run) fun _ _ => True := by
  unfold testRest
  refine ct_app' (by simp [test, phase]) (by simp) (Ψ := fun p t => TE (d3 p).tq t ∧ QOdd p) ?_
    (by rw [seqs_one]; exact two_map (fun p => endFOf (d3 p).tq) (fun _ _ h => te_endF h.1) pResult_ct)
  refine two_map id (Φ' := PStart fun p => (d3 p).u) (fun p s h => ?_)
    (testP_ct M R (fun p => (d3 p).u) (fun p => (d3 p).K) (adjust := restChecks) (by taint_decide)
      fun p s h => WP.mono (restChecks_ok h (by unfold Spec.Ffdh.primeChecks; split <;> decide)) fun t ⟨ht, _⟩ => ht)
  obtain ⟨⟨hte, hqo⟩, h3, ht⟩ := h
  obtain ⟨fix, hU, hu⟩ := te_passed hte h3 ht
  exact ⟨⟨_, fix.st⟩, hU, hu, hte.1.hL, hqo⟩

/-- `q` and its test, after `p`'s first witness passed. -/
theorem testQS_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two fun p t => (TE (d1 p).tq t ∧ QOdd p) ∧
      isa.eval (.zero .x .x3) t = some (decide (statF (d1 p).tq.res = 1)) ∧ isa.eval (.zero .x .x3) t = some true)
      (testQ M.mm R.run) fun _ _ => True := by
  unfold testQ
  simp only [List.append_assoc]
  refine ct_app' (by simp [halveQ]) (by simp [test, phase]) (Ψ := QStart fun p => (d2 p).u) ?_ ?_
  · refine two_post (two_map PP.ws (fun _ _ h => (te_fix h.1.1).st.ws) halveQ_ct) fun p s h => ?_
    obtain ⟨⟨hte, hqo⟩, h3, ht⟩ := h
    obtain ⟨fix, hU, hu⟩ := te_passed hte h3 ht
    obtain ⟨_, hc⟩ := fix.ctx
    have hws := fix.st.ws
    have hn := hws.scr.nowrap
    have h256 := hws.h256
    have hb1 : 512 ≤ p.bits := fix.st.dims.b1
    obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits)
      (by omega_arith) (Spec.Rsa.os2ip (p.r.take p.L))
    refine WP.mono (halveQ_ok fix.st hc.n rfl) fun t ⟨st, hq, _, f, _⟩ => ⟨st, by
      rw [hq]; simp only [cOf] at hpo ⊢; omega_arith, hqo, ?_, hu, hte.1.hL⟩
    rw [f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega_arith)
      · exact .inr (by decide)) (by simp only [kUsed, sFn]; omega_arith)]
    exact hU
  exact ct_app' (by simp [test, phase]) (by simp) (Ψ := fun p t => TE (d2 p).tq t ∧ QOdd p) (testQ_ct M R)
    (stage_ct (fun p => (d2 p).tq) (testRest_ct M R))

/-- The tests leak the same in runs with the same public data. -/
theorem tests_ct (M : Mont) (R : Kernel) : RelCT isa (Two TQd) (tests M.mm R.run) fun _ _ => True :=
  ct_app' (by simp [test, phase]) (by simp) (Ψ := fun p t => TE (d1 p).tq t ∧ QOdd p)
    (two_map id (Φ' := PStart fun p => (d1 p).u) (fun p s h => ⟨⟨_, h.1.st⟩, h.1.used, h.1.hl, h.1.hl, h.2⟩)
      (testP_ct M R (fun p => (d1 p).u) (fun p => (d1 p).K) (adjust := firstCheck) (by taint_decide)
        fun p s h => WP.mono (firstCheck_ok h) fun t ⟨ht, _⟩ => ht))
    (stage_ct (fun p => (d1 p).tq) (testQS_ct M R))

/-! ## `main` -/

theorem main_eq (M : Mont) (R : Kernel) : main M.mm R.run = seqs ((phase false ++ shapeP) ++ (residue ++
    ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
      (seqs ([tableWrite] ++ (sieve true ++ ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
        (seqs (halveQ ++ ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
          (seqs (sieve false ++ ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
            (seqs (shapeP ++ (sieve false ++ ([.block [ldh .x5 fBad],
              .ite (.zero .x .x5) (tests M.mm R.run) (finUsed 2)] : List (Prog isa)))))
            (finUsed 2)] : List (Prog isa))))
          (finUsed 2)] : List (Prog isa))))
        (finUsed 2)] : List (Prog isa)))))
      (finUsed 2)] : List (Prog isa)))) := by
  simp only [main, mainQ, mainP, List.append_assoc]

/-- A check of the flag so far, `v p`, which the public data fixes: `cont`
when it is zero, else the candidate ends. `T` is what else the stage has
of the memory (the table, once it is written). -/
theorem check_ct (T : PP → Mem → Prop) (n : PP → Nat) (v : PP → BitVec 64) {cont : Prog isa}
    (hc : RelCT isa (Two fun p t => (StgF p (n p) (v p) t ∧ T p t.mem) ∧ v p = 0) cont fun _ _ => True) :
    RelCT isa (Two fun p t => StgF p (n p) (v p) t ∧ T p t.mem)
      (seqs [.block [ldh .x5 fBad], .ite (.zero .x .x5) cont (finUsed 2)]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p t => (StgF p (n p) (v p) t ∧ T p t.mem) ∧ t.gpr .x5 = v p) [.x0]
    (pins_ws' (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits) fun _ _ h => h.1.1.st.ws)
    (by taint_decide) fun p s h => WP.mono (stgFlag_ok h.1) fun t' ⟨⟨g, h5⟩, hm, _⟩ =>
      ⟨⟨g, by rw [hm]; exact h.2⟩, h5⟩)
    (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_)
  · refine hc.mono (fun _ _ h => two_mono (fun p t ⟨⟨hg, h5⟩, hz⟩ => ⟨hg, ?_⟩) h) fun _ _ h => h
    rw [eval_zero, h5] at hz
    simpa using hz
  · rw [finUsed_split]
    exact two_map (Φ' := UpF) (fun p : PP => (⟨p.B, p.Z, mW p.bits, p.op, p.up, p.L, 0⟩ : FQ))
      (fun p s h => ⟨h.1.1.1.1.st.ws, h.1.1.1.1.st.args.usedP⟩)
      (finStoreF_ct (fun _ _ h => h) 2 (.inr rfl) (by taint_decide) (by taint_decide))

/-- The table, as `check_ct`'s `T`. -/
abbrev tabOf (p : PP) (m : Mem) : Prop := TabOk m p.B (mW p.bits)

/-- `main` leaks the same in runs with the same public data. -/
theorem main_ct (M : Mont) (R : Kernel) : RelCT isa (Two M0) (main M.mm R.run) fun _ _ => True := by
  rw [main_eq]
  -- `p` and its working space.
  refine ct_app' (by simp [phase]) (by simp [residue]) (Ψ := fun p t => Stg p (cOf p) t)
    (two_post (ct_app' (by simp [phase]) (by simp [shapeP, loadA]) (Ψ := SP)
      (two_post (two_map id (fun _ _ h => h.1) (phase_ct false)) fun p s h => ?_) shapeP_ct)
      fun p s h => WP.mono (stgA_ok h.1 h.2.1 h.2.2) fun _ h => h.1) ?_
  · refine WP.mono (phase_ok h.1 false) fun t ht => ?_
    have hmb : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
    have st := ht.st
    rw [hmb] at st
    exact ⟨st, by have := ht.len; rw [hmb] at this; exact this, h.2.2⟩
  -- The congruence, rejected at once.
  refine ct_app' (by simp [residue]) (by simp) (Ψ := fun p t => StgF p (cOf p) (scr1 p.g (cOf p)) t ∧ True)
    (two_post (two_map PP.ws (fun _ _ h => h.st.ws) residue_ct) fun p s h =>
      WP.mono (stgB_ok h) fun _ h => ⟨h.1, trivial⟩) ?_
  refine check_ct (fun _ _ => True) cOf (fun p => scr1 p.g (cOf p)) ?_
  -- The table, and the sieve of `p` by its first words.
  refine ct_app' (a := [tableWrite]) (by simp) (by simp [sieve])
    (Ψ := fun p t => StgT p (cOf p) (scr1 p.g (cOf p)) t)
    (two_post (by rw [seqs_one]; exact two_map PP.ws (fun _ _ h => h.1.1.1.st.ws) tableWrite_ct)
      fun p s h => by rw [seqs_one]; exact WP.mono (stgTab_ok h.1.1) fun _ h => h.1) ?_
  refine ct_app' (by simp [sieve]) (by simp) (Ψ := fun p t => StgT p (cOf p) (scr2 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map (fun p : PP => (p.ws, cOf p))
      (fun _ _ h => ⟨h.1.1.st.ws, pTab h.1.1.st.dims, h.2, h.1.1.an⟩) (sieve_ct true))
      fun p s h => WP.mono (stgSieve_ok true h) fun _ h => h.1) ?_
  refine check_ct tabOf cOf (fun p => scr2 p.g (mW p.bits) (cOf p))
    (two_map id (Φ' := fun p t => StgT p (cOf p) (scr2 p.g (mW p.bits) (cOf p)) t) (fun _ _ h => h.1) ?_)
  -- `q`, rejected at once if it is even.
  refine ct_app' (by simp [halveQ]) (by simp)
    (Ψ := fun p t => StgT p (cOf p / 2) (scr3 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map PP.ws (fun _ _ h => h.1.1.st.ws) halveQ_ct) fun p s h =>
      WP.mono (stgHalve_ok h) fun _ h => h.1) ?_
  refine check_ct tabOf (fun p => cOf p / 2) (fun p => scr3 p.g (mW p.bits) (cOf p))
    (two_map id (Φ' := fun p t => StgT p (cOf p / 2) (scr3 p.g (mW p.bits) (cOf p)) t) (fun _ _ h => h.1) ?_)
  -- The sieve of `q`.
  refine ct_app' (by simp [sieve]) (by simp)
    (Ψ := fun p t => StgT p (cOf p / 2) (scr4 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map (fun p : PP => (p.ws, cOf p / 2))
      (fun _ _ h => ⟨h.1.1.st.ws, pTab h.1.1.st.dims, h.2, h.1.1.an⟩) (sieve_ct false))
      fun p s h => WP.mono (stgSieve_ok false h) fun _ h => h.1) ?_
  refine check_ct tabOf (fun p => cOf p / 2) (fun p => scr4 p.g (mW p.bits) (cOf p))
    (two_map id (Φ' := fun p t => StgT p (cOf p / 2) (scr4 p.g (mW p.bits) (cOf p)) t) (fun _ _ h => h.1) ?_)
  -- `p` again, and its whole sieve.
  refine ct_app' (by simp [shapeP, loadA]) (by simp [sieve])
    (Ψ := fun p t => StgT p (cOf p) (scr4 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map id (fun _ _ h => ⟨h.1.1.st, h.1.1.len, h.1.1.hl⟩) shapeP_ct) fun p s h =>
      WP.mono (stgShape_ok h) fun _ h => h.1) ?_
  refine ct_app' (by simp [sieve]) (by simp) (Ψ := fun p t => StgT p (cOf p) (scr5 p.g (mW p.bits) (cOf p)) t)
    (two_post (two_map (fun p : PP => (p.ws, cOf p))
      (fun _ _ h => ⟨h.1.1.st.ws, pTab h.1.1.st.dims, h.2, h.1.1.an⟩) (sieve_ct false))
      fun p s h => WP.mono (stgSieve_ok false h) fun _ h => h.1) ?_
  refine check_ct tabOf cOf (fun p => scr5 p.g (mW p.bits) (cOf p)) ?_
  -- The tests.
  exact (tests_ct M R).mono (fun _ _ h => two_mono (fun p t ⟨hg, hz⟩ =>
    ⟨hg.1.1, qOdd_of_shape hg.1.1.st.dims (scr5_zero.mp hz)⟩) h) fun _ _ h => h

end VG.Proof.Ffdh.AArch64.ParameterCandidate
