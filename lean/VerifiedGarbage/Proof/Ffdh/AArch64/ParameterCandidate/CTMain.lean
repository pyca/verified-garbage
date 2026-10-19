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
  exact ⟨h.st.step hws hf hp hZ k, by rw [hf.wv_eq dN (by omega)]; exact h.an,
    by rw [hf.word_eq dU (by simp only [kUsed, sFn]; omega)]; exact h.used, h.hl⟩

theorem pTab {p : PP} (h : PDims p) : slot (mW p.bits) aTab + 2048 ≤ p.Z := by
  have := h.z
  have := h.b1
  simp only [slot, hdrBytes, aTab, mW, PP.L] at *
  omega

/-- The residue's flag of the candidate. -/
abbrev rOf (p : PP) : BitVec 64 := resFlag p.g (BitVec.ofNat 64 (cOf p % resMod p.g))

/-- After the residue. -/
def C2 (p : PP) (s : State) : Prop := MS p (cOf p) s ∧ word s.mem p.B (8 * fBad) = rOf p

/-- After the table. -/
def C3 (p : PP) (s : State) : Prop := C2 p s ∧ TabOk s.mem p.B (mW p.bits)

/-- After the sieve of `p`. -/
def C4 (p : PP) (s : State) : Prop :=
  MS p (cOf p) s ∧ TabOk s.mem p.B (mW p.bits) ∧ word s.mem p.B (8 * fBad) = rOf p ||| mask (anyPre (cOf p) 53)

/-- After `q`. -/
def C5 (p : PP) (s : State) : Prop :=
  MS p (cOf p / 2) s ∧ TabOk s.mem p.B (mW p.bits) ∧
    word s.mem p.B (8 * fBad) = rOf p ||| mask (anyPre (cOf p) 53) ||| evenFlag (cOf p / 2)

/-- After the sieve of `q`. -/
def C6 (p : PP) (s : State) : Prop := MS p (cOf p / 2) s ∧ word s.mem p.B (8 * fBad) = shapeFlag p.g (cOf p)

theorem stA_ok {p : PP} {s : State} (h : M0 p s) : WP isa (seqs (phase false ++ shapeP)) s (MS p (cOf p)) :=
  WP.mono (pPhase_ok h.1 rfl h.2.1 h.2.2 h.2.2) fun _ ⟨ht, _⟩ => ⟨ht.st, ht.n, ht.used, h.2.2⟩

theorem stB_ok {p : PP} {s : State} (h : MS p (cOf p) s) : WP isa (seqs residue) s (C2 p) :=
  WP.mono (residue_ok h.st h.an) fun t ⟨st, hb, f, k⟩ =>
    ⟨h.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.st.ws.h256; simp only [fBad]; omega) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)), hb⟩

theorem stC_ok {p : PP} {s : State} (h : C2 p s) : WP isa tableWrite s (C3 p) := by
  have hT := pTab h.1.st.dims
  have sN := h.1.st.ws.sl (show aN < 16 by decide)
  exact WP.mono (tableWrite_ok h.1.st hT) fun t ⟨st, tab, f, k⟩ =>
    ⟨⟨h.1.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hT) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, aN, aTab]; omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega)),
      by rw [f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, fBad]; omega))
        (by simp only [fBad]; omega)]; exact h.2⟩, tab⟩

theorem stD_ok {p : PP} {s : State} (h : C3 p s) : WP isa (seqs sieve) s (C4 p) := by
  have hT := pTab h.1.1.st.dims
  exact WP.mono (sieve_ok h.1.1.st hT h.2 h.1.1.an h.1.2) fun t ⟨st, hb, f, k⟩ =>
    ⟨h.1.1.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.1.1.st.ws.h256; simp only [fBad]; omega) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)),
      h.2.frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [slot, hdrBytes, fBad]; omega) (by
        have := h.1.1.st.ws.scr.nowrap; omega), hb⟩

theorem stE_ok {p : PP} {s : State} (h : C4 p s) : WP isa (seqs halveQ) s (C5 p) := by
  have hT := pTab h.1.st.dims
  have sN := h.1.st.ws.sl (show aN < 16 by decide)
  exact WP.mono (halveQ_ok h.1.st h.1.an h.2.2) fun t ⟨st, hn, hb, f, k⟩ =>
    ⟨⟨st, hn, by
      rw [f.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega)
        · exact .inr (by decide)) (by simp only [kUsed, sFn]; have := h.1.st.ws.h256; omega)]
      exact h.1.used, h.1.hl⟩,
      h.2.1.frm f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [slot, hdrBytes, aN, aTab]; omega
        · simp only [slot, hdrBytes, fBad]; omega) (by have := h.1.st.ws.scr.nowrap; omega), hb⟩

theorem stF_ok {p : PP} {s : State} (h : C5 p s) : WP isa (seqs sieve) s (C6 p) := by
  have hT := pTab h.1.st.dims
  exact WP.mono (sieve_ok h.1.st hT h.2.1 h.1.an h.2.2) fun t ⟨st, hb, f, k⟩ =>
    ⟨h.1.frm st.ws f (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; have := h.1.st.ws.h256; simp only [fBad]; omega) k
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega))
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
  ⟨h.upw, h.upZ, fun j hj => h.outw j (by omega), fun j hj => h.outZ j (by omega), fun j hj => h.ou j (by omega)⟩

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
  refine ⟨fix.st.ws, fix.st.args.out, fix.len, fix.st.args.usedP, OutUp.mono' fix.st.ou (by simp only [mLen, PP.L]; omega),
    te_stat h, ?_⟩
  show statF q.res < 4
  unfold statF; split <;> (try split) <;> decide

/-- Before the tests. -/
def TQd (p : PP) (s : State) : Prop := MS p ((cOf p - 1) / 2) s ∧ ((cOf p - 1) / 2) % 2 = 1

theorem testQ_ct (M : Mont) (R : Kernel) : RelCT isa (Two TQd) (seqs (test true M.mm R.run)) (Two TE) := by
  rw [test_true]
  refine ct_app' (by simp [phase]) (by simp [montPrep])
    (Ψ := fun p t => TT p (p.bits - 1) ((cOf p - 1) / 2) p.L t)
    (two_post (two_map id (fun _ _ h => h.1.st.ph) (phase_ct true)) fun p s h =>
      WP.mono (qPhase_ok h.1.st rfl h.1.an h.2 h.1.used h.1.hl h.1.hl) fun _ ⟨ht, _⟩ => ht)
    (two_map (fun p : PP => (⟨p, p.bits - 1, (cOf p - 1) / 2, p.L⟩ : TD)) (fun _ _ h => h) (testTail_ct M R))

/-- The test of `p`, after `q` passed. -/
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

/-- The test of `p` leaks the same in runs with the same public data. -/
theorem testP_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two fun (q : TQ) s => TE q s ∧ isa.eval (.zero .x .x3) s = some (decide (statF q.res = 1)) ∧
      isa.eval (.zero .x .x3) s = some true) (seqs (test false M.mm R.run ++ [pResult])) fun _ _ => True := by
  rw [test_false']
  refine ct_app' (by simp [phase]) (by simp) (Ψ := TE) ?_
    (by rw [seqs_one]; exact two_map endFOf (fun _ _ h => te_endF h) pResult_ct)
  refine ct_app' (by simp [phase]) (by simp [montPrep])
    (Ψ := fun q t => TT q.p q.p.bits (cOf q.p) (uOfRes q.p.r q.res) t) ?_
    (two_map (fun q : TQ => (⟨q.p, q.p.bits, cOf q.p, uOfRes q.p.r q.res⟩ : TD)) (fun _ _ h => h) (testTail_ct M R))
  refine two_post (ct_app' (by simp [phase]) (by simp [shapeP, loadA]) (Ψ := fun q t => SP q.p t)
    (two_post (two_map (fun q : TQ => q.p) (fun _ _ h => (te_fix h.1).st.ph) (phase_ct false)) fun q s h => ?_)
    (two_map (fun q : TQ => q.p) (fun _ _ h => h) shapeP_ct)) fun q s ⟨h, h3, ht⟩ => ?_
  · have hL := h.1.1.hL
    refine WP.mono (phase_ok (te_fix h.1).st.ph false) fun t ht => ?_
    have hmb : q.p.mb false = q.p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
    have st := ht.st
    rw [hmb] at st
    exact ⟨st, by have := ht.len; rw [hmb] at this; exact this, hL⟩
  · obtain ⟨rest, hr⟩ := pq_res ⟨h, ht⟩ h3
    obtain ⟨hd, s₀, he⟩ := h
    obtain ⟨u, hu, hrest, hU⟩ := (he.2.2.1 true rest hr).2
    have hu' : uOfRes q.p.r q.res = u := by
      rw [hr]; simp only [uOfRes]; rw [hrest, List.length_drop]; omega
    refine WP.mono (pPhase_ok he.1.st.ph rfl (by rw [hu']; exact hU) (by rw [hu']; exact hu) hd.hL)
      fun t ⟨ht', _⟩ => ht'

/-- The tests leak the same in runs with the same public data. -/
theorem tests_ct (M : Mont) (R : Kernel) : RelCT isa (Two TQd) (tests M.mm R.run) fun _ _ => True := by
  unfold tests
  refine RelCT.seqs_append (by simp [test, phase]) (by simp) (RelCT.seq (testQ_ct M R) ?_)
  simp only [seqs]
  have pw : ∀ {Φ : TQ → State → Prop}, (∀ q s, Φ q s → TE q s) → Pins Φ [.x0] := fun h =>
    pins_ws' (fun q : TQ => q.p.B) (fun q : TQ => q.p.Z) (fun q : TQ => q.w) fun _ _ hx => (te_fix (h _ _ hx)).st.ws
  refine RelCT.seq (two_piece (Ψ := fun q t => TE q t ∧
      isa.eval (.zero .x .x3) t = some (decide (statF q.res = 1))) [.x0] (pw fun _ _ h => h) (by taint_decide)
      fun q s h => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_)
  · have fix := te_fix h
    refine WP.mono (stat1_ok fix.st.ws (v := statF q.res) (by unfold statF; split <;> (try split) <;> decide)
      (te_stat h)) fun t ⟨hz, hm, k⟩ => ⟨?_, hz⟩
    obtain ⟨hd, s₀, he⟩ := h
    have hEZ := hd.eZ
    exact ⟨hd, s₀, he.1.same hEZ hm k (by decide), by rw [hm]; exact he.2.1, fun b rest h' => by
      rw [hm]; exact he.2.2.1 b rest h', by rw [hm]; exact he.2.2.2.1, (he.2.2.2.2.trans k).mono (by decide)⟩
  · exact (testP_ct M R).mono (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) h) fun _ _ h => h
  · exact two_map endFOf (fun _ _ h => te_endF h.1.1) qResult_ct

/-! ## `main` -/

theorem main_eq (M : Mont) (R : Kernel) : main M.mm R.run = seqs ((phase false ++ shapeP) ++ (residue ++
    ([.block [ldh .x5 fBad], .ite (.zero .x .x5)
      (seqs ([tableWrite] ++ (sieve ++ (halveQ ++ (sieve ++ ([.block [ldh .x5 fBad],
        .ite (.zero .x .x5) (tests M.mm R.run) (finUsed 2)] : List (Prog isa)))))))
      (finUsed 2)] : List (Prog isa)))) := by
  simp only [main, List.append_assoc]

theorem ms_ws {p : PP} {n : Nat} {s : State} (h : MS p n s) : WQ p.ws s := h.st.ws

/-- After the flag's load. -/
def C7 (p : PP) (s : State) : Prop := C6 p s ∧ s.gpr .x5 = shapeFlag p.g (cOf p)

theorem flag_ok {p : PP} {s : State} (h : C6 p s) : WP isa (.block [ldh .x5 fBad]) s (C7 p) := by
  have hw := h.1.st.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = shapeFlag p.g (cOf p) ∧ t.mem = s.mem)
    (by brun [hw.x0, hdr_enc (show fBad < 32 by decide), hw.scr.ld (d := 8 * fBad) (by simp only [fBad]; omega),
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
    (by brun [hw.x0, hdr_enc (show fBad < 32 by decide), hw.scr.ld (d := 8 * fBad) (by simp only [fBad]; omega),
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
    have hz' : shapeFlag p.g (cOf p) = 0 := by simpa using hz
    have hb1 := hm.st.dims.b1
    have hb2 := hm.st.dims.b2
    have hsh := (shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 hm.st.dims.g).mp hz'
    have hqs : Spec.Ffdh.primeShape ((cOf p - 1) / 2) = true := by
      simp only [Bool.and_eq_true] at hsh; exact hsh.2
    have hqo : ((cOf p - 1) / 2) % 2 = 1 := by
      unfold Spec.Ffdh.primeShape at hqs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hqs
      exact hqs.1.2
    obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega)
      (Spec.Rsa.os2ip (p.r.take p.L))
    have hq : (cOf p - 1) / 2 = cOf p / 2 := by simp only [cOf] at hpo ⊢; omega
    exact ⟨⟨hm.st, by rw [hq]; exact hm.an, hm.used, hm.hl⟩, hqo⟩
  · rw [finUsed_split]
    exact two_map (Φ' := UpF) (fun p : PP => (⟨p.B, p.Z, mW p.bits, p.op, p.up, p.L, 0⟩ : FQ))
      (fun p s h => ⟨h.1.1.1.st.ws, h.1.1.1.st.args.usedP⟩)
      (finStoreF_ct (fun _ _ h => h) 2 (.inr rfl) (by taint_decide) (by taint_decide))

end VG.Proof.Ffdh.AArch64.ParameterCandidate
