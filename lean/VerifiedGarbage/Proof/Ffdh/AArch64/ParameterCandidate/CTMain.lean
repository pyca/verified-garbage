module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTPieces
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTTest
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Main
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

`main`'s stages (`MS`, after each piece), each piece from the stage before
it (`CTPieces.lean`, `CTTest.lean`), the branch on the shape's flag, which
the public data fixes, and the tests (`tests_ct`), whose branches the
results of Miller–Rabin fix.
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

/-- The candidate. -/
abbrev cOf (p : PP) : Nat := Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))

/-- The working space of `p`'s words. -/
abbrev PP.ws (p : PP) : WsP := ⟨p.B, p.Z, mW p.bits⟩

/-- Before `main`. -/
def M0 (p : PP) (s : State) : Prop :=
  PH p s ∧ word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L ∧ p.L ≤ p.r.length

/-- Between `main`'s pieces, with `n` in `aN`. -/
structure MS (p : PP) (n : Nat) (s : State) : Prop where
  st : PSt p (mW p.bits) s
  an : wv s.mem p.B (slot (mW p.bits) aN) (mW p.bits) = n
  used : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L
  hl : p.L ≤ p.r.length

theorem MS.frm {p : PP} {n : Nat} {s t : State} (h : MS p n s) {rs : List (Nat × Nat)} (hws : Ws t p.B p.Z (mW p.bits))
    (hf : Frm p.B rs s.mem t.mem) (hp : ∀ r ∈ rs, PMut r) (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) {regs : List Reg}
    (k : Keep regs s t) (dN : ∀ r ∈ rs, slot (mW p.bits) aN + 8 * mW p.bits ≤ r.1 ∨ r.1 + r.2 ≤ slot (mW p.bits) aN)
    (dU : ∀ r ∈ rs, 8 * kUsed + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kUsed) : MS p n t := by
  have hn := h.st.ws.scr.nowrap
  have sN := h.st.ws.sl (show aN < 16 by decide)
  have h256 := h.st.ws.h256
  exact ⟨h.st.step hws hf hp hZ k, by rw [hf.wv_eq dN (by omega_arith)]; exact h.an,
    by rw [hf.word_eq dU (by simp only [kUsed, sFn]; omega_arith)]; exact h.used, h.hl⟩

theorem pTab {p : PP} (h : PDims p) : slot (mW p.bits) aTab + 2048 ≤ p.Z := by
  have := h.z
  have := h.b1
  simp only [slot, hdrBytes, aTab, mW, PP.L] at *
  omega_arith

/-- The residue's flag of the candidate. -/
abbrev rOf (p : PP) : BitVec 64 := resFlag p.g (BitVec.ofNat 64 (cOf p % resMod p.g))

/-- After the residue. -/
def C2 (p : PP) (s : State) : Prop := MS p (cOf p) s ∧ word s.mem p.B (8 * fBad) = rOf p

/-- After the table. -/
def C3 (p : PP) (s : State) : Prop := C2 p s ∧ TabOk s.mem p.B (mW p.bits)

/-- After the sieve of `p`. -/
def C4 (p : PP) (s : State) : Prop :=
  MS p (cOf p) s ∧ TabOk s.mem p.B (mW p.bits) ∧
    word s.mem p.B (8 * fBad) = rOf p ||| mask (anyPre (cOf p) (4 * trialN (mW p.bits)))

/-- After `q`. -/
def C5 (p : PP) (s : State) : Prop :=
  MS p (cOf p / 2) s ∧ TabOk s.mem p.B (mW p.bits) ∧
    word s.mem p.B (8 * fBad) = rOf p ||| mask (anyPre (cOf p) (4 * trialN (mW p.bits))) ||| evenFlag (cOf p / 2)

/-- After the sieve of `q`. -/
def C6 (p : PP) (s : State) : Prop :=
  MS p (cOf p / 2) s ∧ word s.mem p.B (8 * fBad) = shapeFlag p.g (mW p.bits) (cOf p)

theorem stA_ok {p : PP} {s : State} (h : M0 p s) : WP isa (seqs (phase false ++ shapeP)) s (MS p (cOf p)) :=
  WP.mono (pPhase_ok h.1 rfl h.2.1 h.2.2 h.2.2) fun _ ⟨ht, _⟩ => ⟨ht.st, ht.n, ht.used, h.2.2⟩

theorem stB_ok {p : PP} {s : State} (h : MS p (cOf p) s) : WP isa (seqs residue) s (C2 p) :=
  WP.mono (residue_ok h.st h.an) fun t ⟨st, hb, f, k⟩ =>
    ⟨h.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.st.ws.h256; simp only [fBad]; omega_arith) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega_arith))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)), hb⟩

theorem stC_ok {p : PP} {s : State} (h : C2 p s) : WP isa tableWrite s (C3 p) := by
  have hT := pTab h.1.st.dims
  have sN := h.1.st.ws.sl (show aN < 16 by decide)
  exact WP.mono (tableWrite_ok h.1.st hT) fun t ⟨st, tab, f, k⟩ =>
    ⟨⟨h.1.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hT) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, aN, aTab]; omega_arith))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega_arith)),
      by rw [f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, fBad]; omega_arith))
        (by simp only [fBad]; omega_arith)]; exact h.2⟩, tab⟩

theorem stD_ok {p : PP} {s : State} (h : C3 p s) : WP isa (seqs sieve) s (C4 p) := by
  have hT := pTab h.1.1.st.dims
  exact WP.mono (sieve_ok h.1.1.st hT h.2 h.1.1.an h.1.2) fun t ⟨st, hb, f, k⟩ =>
    ⟨h.1.1.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.1.1.st.ws.h256; simp only [fBad]; omega_arith) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega_arith))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)),
      h.2.frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [slot, hdrBytes, fBad]; omega_arith) (by
        have := h.1.1.st.ws.scr.nowrap; omega_arith), hb⟩

theorem stE_ok {p : PP} {s : State} (h : C4 p s) : WP isa (seqs halveQ) s (C5 p) := by
  have hT := pTab h.1.st.dims
  have sN := h.1.st.ws.sl (show aN < 16 by decide)
  exact WP.mono (halveQ_ok h.1.st h.1.an h.2.2) fun t ⟨st, hn, hb, f, k⟩ =>
    ⟨⟨st, hn, by
      rw [f.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega_arith)
        · exact .inr (by decide)) (by simp only [kUsed, sFn]; have := h.1.st.ws.h256; omega_arith)]
      exact h.1.used, h.1.hl⟩,
      h.2.1.frm f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [slot, hdrBytes, aN, aTab]; omega_arith
        · simp only [slot, hdrBytes, fBad]; omega_arith) (by have := h.1.st.ws.scr.nowrap; omega_arith), hb⟩

theorem stF_ok {p : PP} {s : State} (h : C5 p s) : WP isa (seqs sieve) s (C6 p) := by
  have hT := pTab h.1.st.dims
  exact WP.mono (sieve_ok h.1.st hT h.2.1 h.1.an h.2.2) fun t ⟨st, hb, f, k⟩ =>
    ⟨h.1.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.1.st.ws.h256; simp only [fBad]; omega_arith) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega_arith))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)), by rw [hb]; rfl⟩

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
def TQd (p : PP) (s : State) : Prop := MS p ((cOf p - 1) / 2) s ∧ ((cOf p - 1) / 2) % 2 = 1

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
      (seqs ([tableWrite] ++ (sieve ++ (halveQ ++ (sieve ++ ([.block [ldh .x5 fBad],
        .ite (.zero .x .x5) (tests M.mm R.run) (finUsed 2)] : List (Prog isa)))))))
      (finUsed 2)] : List (Prog isa)))) := by
  simp only [main, List.append_assoc]

theorem ms_ws {p : PP} {n : Nat} {s : State} (h : MS p n s) : WQ p.ws s := h.st.ws

/-- After the flag's load. -/
def C7 (p : PP) (s : State) : Prop := C6 p s ∧ s.gpr .x5 = shapeFlag p.g (mW p.bits) (cOf p)

theorem flag_ok {p : PP} {s : State} (h : C6 p s) : WP isa (.block [ldh .x5 fBad]) s (C7 p) := by
  have hw := h.1.st.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = shapeFlag p.g (mW p.bits) (cOf p) ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show fBad < 32 by decide), hw.scr.ld (d := 8 * fBad) (by simp only [fBad]; omega_arith),
      h.2]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h5, hm⟩, k⟩ => ⟨⟨?_, by rw [hm]; exact h.2⟩, h5⟩
  exact h.1.frm (rs := []) (hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide))
    (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k (by simp) (by simp)

/-- After the congruence's flag's load. -/
def C2R (p : PP) (s : State) : Prop := C2 p s ∧ s.gpr .x5 = rOf p

theorem flagR_ok {p : PP} {s : State} (h : C2 p s) : WP isa (.block [ldh .x5 fBad]) s (C2R p) := by
  have hw := h.1.st.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = rOf p ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show fBad < 32 by decide), hw.scr.ld (d := 8 * fBad) (by simp only [fBad]; omega_arith),
      h.2]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h5, hm⟩, k⟩ => ⟨⟨?_, by rw [hm]; exact h.2⟩, h5⟩
  exact h.1.frm (rs := []) (hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide))
    (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k (by simp) (by simp)

/-- `main` leaks the same in runs with the same public data. -/
theorem main_ct (M : Mont) (R : Kernel) : RelCT isa (Two M0) (main M.mm R.run) fun _ _ => True := by
  rw [main_eq]
  have ws : ∀ {Φ : PP → State → Prop}, (∀ p s, Φ p s → Ws s p.B p.Z (mW p.bits)) → Pins Φ [.x0] := fun h =>
    pins_ws' (fun p : PP => p.B) (fun p : PP => p.Z) (fun p : PP => mW p.bits) h
  -- `p` and its working space.
  refine ct_app' (by simp [phase]) (by simp [residue]) (Ψ := fun p t => MS p (cOf p) t)
    (two_post (ct_app' (by simp [phase]) (by simp [shapeP, loadA]) (Ψ := SP)
      (two_post (two_map id (fun _ _ h => h.1) (phase_ct false)) fun p s h => ?_) shapeP_ct)
      fun p s h => stA_ok h) ?_
  · refine WP.mono (phase_ok h.1 false) fun t ht => ?_
    have hmb : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
    have st := ht.st
    rw [hmb] at st
    exact ⟨st, by have := ht.len; rw [hmb] at this; exact this, h.2.2⟩
  -- The congruence, the table and the sieve of `p`.
  refine ct_app' (by simp [residue]) (by simp) (Ψ := C2)
    (two_post (two_map PP.ws (fun _ _ h => ms_ws h) residue_ct) fun p s h => stB_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := C2R) [.x0] (ws fun _ _ h => h.1.st.ws) (by taint_decide)
    fun p s h => flagR_ok h) (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_)
  rotate_left
  · rw [finUsed_split]
    exact two_map (Φ' := UpF) (fun p : PP => (⟨p.B, p.Z, mW p.bits, p.op, p.up, p.L, 0⟩ : FQ))
      (fun p s h => ⟨h.1.1.1.st.ws, h.1.1.1.st.args.usedP⟩)
      (finStoreF_ct (fun _ _ h => h) 2 (.inr rfl) (by taint_decide) (by taint_decide))
  refine two_map id (fun _ _ h => h.1.1) ?_
  refine ct_app' (a := [tableWrite]) (by simp) (by simp [sieve]) (Ψ := C3)
    (two_post (by rw [seqs_one]; exact two_map PP.ws (fun _ _ h => ms_ws h.1) tableWrite_ct)
      fun p s h => by rw [seqs_one]; exact stC_ok h) ?_
  refine ct_app' (by simp [sieve]) (by simp [halveQ]) (Ψ := C4)
    (two_post (two_map PP.ws (fun _ _ h => ⟨ms_ws h.1.1, pTab h.1.1.st.dims, h.2⟩) sieve_ct)
      fun p s h => stD_ok h) ?_
  -- `q` and its sieve.
  refine ct_app' (by simp [halveQ]) (by simp [sieve]) (Ψ := C5)
    (two_post (two_map PP.ws (fun _ _ h => ms_ws h.1) halveQ_ct) fun p s h => stE_ok h) ?_
  refine ct_app' (by simp [sieve]) (by simp) (Ψ := C6)
    (two_post (two_map PP.ws (fun _ _ h => ⟨ms_ws h.1, pTab h.1.st.dims, h.2.1⟩) sieve_ct)
      fun p s h => stF_ok h) ?_
  -- The flag.
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := C7) [.x0] (ws fun _ _ h => h.1.st.ws) (by taint_decide)
    fun p s h => flag_ok h) (two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_)
  · refine (tests_ct M R).mono (fun _ _ h => two_mono (fun p t ⟨⟨⟨hm, hb⟩, h5⟩, hz⟩ => ?_) h) fun _ _ h => h
    rw [eval_zero, h5] at hz
    have hz' : shapeFlag p.g (mW p.bits) (cOf p) = 0 := by simpa using hz
    have hb1 := hm.st.dims.b1
    have hb2 := hm.st.dims.b2
    have hsh := (shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 hm.st.dims.g).mp hz'
    have hqs : Spec.Ffdh.primeShape ((cOf p - 1) / 2) = true := by
      simp only [Bool.and_eq_true] at hsh; exact hsh.1.1.2
    have hqo : ((cOf p - 1) / 2) % 2 = 1 := by
      unfold Spec.Ffdh.primeShape at hqs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hqs
      exact hqs.1.2
    obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
      (Spec.Rsa.os2ip (p.r.take p.L))
    have hq : (cOf p - 1) / 2 = cOf p / 2 := by simp only [cOf] at hpo ⊢; omega_arith
    exact ⟨⟨hm.st, by rw [hq]; exact hm.an, hm.used, hm.hl⟩, hqo⟩
  · rw [finUsed_split]
    exact two_map (Φ' := UpF) (fun p : PP => (⟨p.B, p.Z, mW p.bits, p.op, p.up, p.L, 0⟩ : FQ))
      (fun p s h => ⟨h.1.1.1.st.ws, h.1.1.1.st.args.usedP⟩)
      (finStoreF_ct (fun _ _ h => h) 2 (.inr rfl) (by taint_decide) (by taint_decide))

end VG.Proof.Ffdh.AArch64.ParameterCandidate
