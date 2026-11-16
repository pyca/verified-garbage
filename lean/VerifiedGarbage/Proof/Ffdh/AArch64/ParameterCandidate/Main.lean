module

import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Result
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Mr
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieved
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Tests
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Rsa.AArch64.Div

/-!
# An FFDH parameter candidate on AArch64: `main`

`tests_ok`: one witness of `p`, all of `q`'s, then `p`'s others
(`Proof.Ffdh.ParameterCandidate.sievedTests`); `main_ok`: `p`, its shape's checks, and the tests, as
`Spec.Ffdh.sievedParameterCandidate` (`PEnd`): the candidate ends at the first
of the shape's checks that fails (the congruence, `p`'s sieve by the
table's first words, `q`'s oddness, `q`'s sieve, then `p`'s whole sieve),
each a part of the flag so far (`scr1` to `scr5`, `ShapeOk.lean`), which
is then not zero, as the shape's flag (`shapeFlag`) then is. The checks'
pieces are the stages `stgA_ok` to `stgTests_ok`, each from the state
between two of them (`Stg`), which `CTMain.lean` runs too.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses onPass sievedTests sieved_eq)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- How the candidate ends, from `s`, for the specification's result. -/
def PEnd (s t : State) (p : PP) : Option (Option Nat × List Byte) → Prop
  | none => KEnd s t p.op p.up p.L 0 0 none
  | some (some c, rest) => KEnd s t p.op p.up p.L 1 (p.r.length - rest.length) (some c)
  | some (none, rest) => KEnd s t p.op p.up p.L 2 (p.r.length - rest.length) none

theorem PEnd.trans_pre {s₀ s t : State} {p : PP} {res : Option (Option Nat × List Byte)} (h : PEnd s t p res)
    (hout : outBytes s.mem p.op p.L = outBytes s₀.mem p.op p.L) (k₀ : Keep mmRegs s₀ s) : PEnd s₀ t p res := by
  rcases res with _ | ⟨_ | _, _⟩ <;> exact KEnd.trans_pre h hout (k₀.mono (by decide))

/-- `kStat` against 1. -/
theorem stat1_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {v : Nat} (hv : v < 2 ^ 63) (hS : word s.mem B (8 * kStat) = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 1]) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (v = 1)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hS' : s.mem.readW (B + BitVec.ofNat 64 (8 * kStat)) 64 = BitVec.ofNat 64 v := hS
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), h.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith),
      hS']) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ?_
  refine ⟨?_, hm, k⟩
  rw [eval_zero, h3, eq_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- After a test that ended with `res` from `t₁`: the end of the candidate
when it did not pass (`qResult`), else `cont`, from octet `u` of the tape. -/
theorem stage_ok {p : PP} {w N mb K : Nat} {s s₀ t₁ : State} {res : Option (Bool × List Byte)}
    {k : List Byte → Option (Option Nat × List Byte)} {cont : Prog isa}
    (e₁ : MrEnd p w N mb K s₀ res t₁) (hEZ : slot w aE + 8 * (w + 2) ≤ p.Z)
    (ho : outBytes t₁.mem p.op p.L = outBytes s.mem p.op p.L) (hk : Keep mmRegs s t₁)
    (hcont : ∀ u t₂, u ≤ p.r.length → res = some (true, p.r.drop u) → MrFix p w N mb K t₂ → t₂.mem = t₁.mem →
      Keep [.x3] t₁ t₂ → word t₂.mem p.B (8 * kUsed) = BitVec.ofNat 64 u →
      WP isa cont t₂ fun t => PEnd s t p (k (p.r.drop u))) :
    WP isa (seqs [.block [ldh .x3 kStat, .subImm .x .x3 .x3 1], .ite (.zero .x .x3) cont qResult]) t₁
      fun t => PEnd s t p (onPass res k) := by
  obtain stt := MrEnd.stat e₁
  obtain ⟨fix₁, -, hrest₁, -, -⟩ := e₁
  have ho₁ := fix₁.st.ou
  simp only [seqs]
  obtain hv : ∀ v, word t₁.mem p.B (8 * kStat) = BitVec.ofNat 64 v → v ≤ 2 →
      WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 1]) t₁ fun t =>
        isa.eval (.zero .x .x3) t = some (decide (v = 1)) ∧ MrFix p w N mb K t ∧ t.mem = t₁.mem ∧
          Keep [.x3] t₁ t :=
    fun v hS hv2 => WP.mono (stat1_ok fix₁.st.ws (by omega_arith) hS) fun t ⟨hz, hm, k⟩ =>
      ⟨hz, fix₁.same hEZ hm k (by decide), hm, k⟩
  obtain fail : ∀ {t₂ : State}, t₂.mem = t₁.mem → Keep [.x3] t₁ t₂ → (∀ rest, res ≠ some (true, rest)) →
      WP isa qResult t₂ fun t => PEnd s t p (onPass res k) := by
    intro t₂ hm kk hnp
    obtain ws₂ := fix₁.st.ws.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) kk (by decide)
    refine WP.mono (qResult_ok (c := 0) (L := p.L) (r := p.r) ws₂ (ho₁.congr kk.wr)
      (by rw [hm]; exact fix₁.st.args.usedP) hnp (by rw [hm]; exact stt.1)
      (fun b rest hr => by rw [hm]; exact stt.2 b rest hr)) fun t ht => ?_
    obtain hk₂ : Keep mmRegs s t₂ := (hk.trans kk).mono (by decide)
    obtain ho₂ : outBytes t₂.mem p.op p.L = outBytes s.mem p.op p.L := by rw [hm]; exact ho
    rcases res with _ | ⟨_ | _, rest⟩
    · exact PEnd.trans_pre (p := p) (res := none) ht ho₂ hk₂
    · exact PEnd.trans_pre (p := p) (res := some (none, rest)) ht ho₂ hk₂
    · exact absurd rfl (hnp rest)
  rcases hQ : res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (hv 0 (stt.1 hQ) (by decide)) fun t₂ ⟨hz, _, hm, kk⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    rw [← hQ]; exact fail hm kk (fun rest h' => by rw [hQ] at h'; cases h')
  · obtain ⟨hS, _⟩ := stt.2 b rest hQ
    refine WP.seq (WP.mono (hv (if b then 1 else 2) hS (by cases b <;> decide)) fun t₂ ⟨hz, fix₂, hm, kk⟩ => ?_)
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      rw [← hQ]; exact fail hm kk (fun rest' h' => by rw [hQ] at h'; cases h')
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      obtain ⟨u, hul, rfl, hUu⟩ := (hrest₁ true _ hQ).2
      exact hcont u t₂ hul hQ fix₂ hm kk (by rw [hm]; exact hUu)

/-- The tests, once the shape passed. -/
theorem tests_ok (M : Mont) (R : Kernel) {p : PP} {s : State} {c : Nat} (h : PSt p (mW p.bits) s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests M.mm R.run) s fun t => PEnd s t p (sievedTests c (p.r.drop p.L)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have h256 := h.ws.h256
  obtain hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_arith) _
  obtain hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_arith) _).1
  obtain ⟨hpo, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu hpo
  obtain hEZq := h.dims.eZ true
  obtain hmbq : p.mb true = p.bits - 1 := by simp only [PP.mb, ↓reduceIte]
  rw [hmbq] at hEZq
  obtain hEZp := h.dims.eZ false
  obtain hmbp : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
  rw [hmbp] at hEZp
  obtain hout : ∀ {t : State}, InScr p.B p.Z s.mem t.mem → outBytes t.mem p.op p.L = outBytes s.mem p.op p.L :=
    fun hi => outBytes_inScr hi h.ou.outZ
  unfold sievedTests
  rw [hbq, hbp]
  unfold tests
  refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
  -- `p`'s first witness.
  refine WP.mono (testP1_ok M R h hc hU hL hL) fun t₁ e₁ => ?_
  refine stage_ok e₁ hEZp (hout e₁.2.2.2.1) e₁.2.2.2.2 fun u₁ t₂ hu₁ _ fix₂ hm₂ k₂ hU₂ => ?_
  obtain isc₂ : InScr p.B p.Z s.mem t₂.mem := by rw [hm₂]; exact e₁.2.2.2.1
  obtain kk₂ : Keep mmRegs s t₂ := (e₁.2.2.2.2.trans k₂).mono (by decide)
  -- `q`, from `p` in `aN`.
  unfold testQ
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [halveQ]) (by simp [test, phase]) ?_
  obtain ⟨_, hc₂⟩ := fix₂.ctx
  have hws₂ := fix₂.st.ws
  have hn₂ := hws₂.scr.nowrap
  refine WP.mono (halveQ_ok fix₂.st hc₂.n rfl) fun t₃ ⟨st₃, hq₃, _, f₃, k₃⟩ => ?_
  obtain hq : (c - 1) / 2 = c / 2 := by omega_arith
  obtain hT₃ : slot (mW p.bits) aN + 8 * (mW p.bits + 2) ≤ p.Z := hws₂.sl (show aN < 16 by decide)
  obtain isc₃ : InScr p.B p.Z s.mem t₃.mem := isc₂.trans (InScr.of_frm f₃ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hT₃
    · simp only [fBad]; omega_arith)
  obtain hU₃ : word t₃.mem p.B (8 * kUsed) = BitVec.ofNat 64 u₁ := by
    rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega_arith)
      · exact .inr (by decide)) (by simp only [kUsed, sFn]; omega_arith)]
    exact hU₂
  refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
  refine WP.mono (testQ_ok M R st₃ hc (by rw [hq₃, hq]) hqo hU₃ hu₁ hL) fun t₄ e₄ => ?_
  obtain isc₄ : InScr p.B p.Z s.mem t₄.mem := isc₃.trans e₄.2.2.2.1
  obtain kk₄ : Keep mmRegs s t₄ := ((kk₂.trans k₃).trans e₄.2.2.2.2).mono (by decide)
  refine stage_ok e₄ hEZq (hout isc₄) kk₄ fun u₂ t₅ hu₂ _ fix₅ hm₅ k₅ hU₅ => ?_
  -- `p`'s other witnesses.
  unfold testRest
  refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
  refine WP.mono (testPR_ok M R fix₅.st hc hU₅ hu₂ hL) fun t₆ e₆ => ?_
  obtain stp := MrEnd.stat e₆
  obtain ⟨fix₆, -, -, isc₆, k₆⟩ := e₆
  rw [seqs_one]
  obtain hn₆ : wv t₆.mem p.B (slot (mW p.bits) aN) ((p.L + 7) / 8) = c := by
    obtain ⟨_, hc₆⟩ := fix₆.ctx
    refine wv_low hc₆.n (by simp only [PP.L, mW]; omega_arith)
      (Nat.lt_of_lt_of_le hcu (Nat.pow_le_pow_right (by decide) (by simp only [PP.L]; omega_arith)))
  refine WP.mono (pResult_ok (c := c) (r := p.r) fix₆.st.ws (by simp only [PP.L]; omega_arith)
    (by simp only [PP.L, mW]; omega_arith) hn₆ fix₆.st.ou fix₆.st.args.out fix₆.len fix₆.st.args.usedP fix₆.msk
    stp.1 stp.2) fun t ht => ?_
  obtain hk : Keep mmRegs s t₆ := ((kk₄.trans k₅).trans k₆).mono (by decide)
  obtain ho : outBytes t₆.mem p.op p.L = outBytes s.mem p.op p.L :=
    hout (isc₄.trans ((show InScr p.B p.Z t₄.mem t₅.mem by rw [hm₅]; exact InScr.refl _ _ _).trans isc₆))
  generalize checkWitnesses c (Spec.Ffdh.primeChecks p.bits - 1) (p.r.drop u₂) = resP at ht ⊢
  rcases resP with _ | ⟨_ | _, rest'⟩
  · exact PEnd.trans_pre (p := p) (res := none) ht ho hk
  · exact PEnd.trans_pre (p := p) (res := some (none, rest')) ht ho hk
  · exact PEnd.trans_pre (p := p) (res := some (some c, rest')) ht ho hk

/-- RSA's table survives changes below it. -/
theorem TabOk.frm {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (h : TabOk m B w)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, r.1 + r.2 ≤ slot w aTab) (hn : slot w aTab + 2048 ≤ 2 ^ 64) :
    TabOk m' B w := fun i hi => by
  rw [hf.word_eq (fun r hr => Or.inr (by have := hd r hr; omega_arith)) (by omega_arith)]; exact h i hi

/-! ## The shape's checks, stage by stage -/

/-- The candidate. -/
abbrev cOf (p : PP) : Nat := Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))

/-- RSA's table is in the working space. -/
theorem pTab {p : PP} (h : PDims p) : slot (mW p.bits) aTab + 2048 ≤ p.Z := by
  have := h.z
  have := h.b1
  simp only [slot, hdrBytes, aTab, mW, PP.L] at *
  omega_arith

/-- Between the shape's checks: `n` in `aN`, and the header's words that
`shapeP` and the candidate's end read. -/
structure Stg (p : PP) (n : Nat) (t : State) : Prop where
  st : PSt p (mW p.bits) t
  an : wv t.mem p.B (slot (mW p.bits) aN) (mW p.bits) = n
  used : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L
  len : word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.L
  top : word t.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1)
  hl : p.L ≤ p.r.length

/-- With the flag `v` so far. -/
def StgF (p : PP) (n : Nat) (v : BitVec 64) (t : State) : Prop := Stg p n t ∧ word t.mem p.B (8 * fBad) = v

/-- With the flag and RSA's table. -/
def StgT (p : PP) (n : Nat) (v : BitVec 64) (t : State) : Prop := StgF p n v t ∧ TabOk t.mem p.B (mW p.bits)

/-- What the shape's checks write: `aN`, the flag and the table. -/
def stgRanges (w : Nat) : List (Nat × Nat) := [(slot w aN, 8 * (w + 2)), (8 * fBad, 8), (slot w aTab, 2048)]

/-- A stage after a piece that writes in `stgRanges` alone and leaves `n'`
in `aN`. -/
theorem Stg.frm {p : PP} {n n' : Nat} {t t' : State} (h : Stg p n t) (st' : PSt p (mW p.bits) t')
    {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem) (hrs : ∀ r ∈ rs, r ∈ stgRanges (mW p.bits))
    (hn : wv t'.mem p.B (slot (mW p.bits) aN) (mW p.bits) = n') :
    Stg p n' t' ∧ InScr p.B p.Z t.mem t'.mem := by
  obtain hT := pTab h.st.dims
  have hn64 := h.st.ws.scr.nowrap
  have h256 := h.st.ws.h256
  obtain hd : ∀ r ∈ rs, ∀ k, k < 32 → k ≠ fBad → 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun r hr k hk hkb => by
    have := hrs r hr
    simp only [stgRanges, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact .inl (by simp only [slot, hdrBytes]; omega_arith)
    · simp only [fBad] at hkb ⊢; omega_arith
    · exact .inl (by simp only [slot, hdrBytes]; omega_arith)
  obtain hw : ∀ k, k < 32 → k ≠ fBad → word t'.mem p.B (8 * k) = word t.mem p.B (8 * k) := fun k hk hkb =>
    hf.word_eq (fun r hr => hd r hr k hk hkb) (by omega_arith)
  refine ⟨⟨st', hn, ?_, ?_, ?_, h.hl⟩, InScr.of_frm hf fun r hr => ?_⟩
  · rw [hw kUsed (by decide) (by decide)]; exact h.used
  · rw [hw sK (by decide) (by decide)]; exact h.len
  · rw [hw fTop (by decide) (by decide)]; exact h.top
  · have := hrs r hr
    simp only [stgRanges, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact h.st.ws.sl (show aN < 16 by decide)
    · simp only [fBad]; omega_arith
    · exact hT

/-- `p` and its working space. -/
theorem stgA_ok {p : PP} {s : State} (h : PH p s) (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L)
    (hL : p.L ≤ p.r.length) :
    WP isa (seqs (phase false ++ shapeP)) s fun t =>
      Stg p (cOf p) t ∧ InScr p.B p.Z s.mem t.mem ∧ Keep mmRegs s t :=
  WP.mono (pPhase_ok h rfl hU hL hL) fun _ ⟨ht, i, k⟩ => ⟨⟨ht.st, ht.n, ht.used, ht.len, ht.top, hL⟩, i, k⟩

/-- The generator's congruence. -/
theorem stgB_ok {p : PP} {t : State} (h : Stg p (cOf p) t) :
    WP isa (seqs residue) t fun t' =>
      StgF p (cOf p) (scr1 p.g (cOf p)) t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain sN := h.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.st.ws.scr.nowrap
  refine WP.mono (residue_ok h.st h.an) fun t' ⟨st', hr, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.frm (n' := cOf p) st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) (by
    rw [f.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega_arith)) (by omega_arith)]
    exact h.an)
  exact ⟨⟨g, hr⟩, i, k⟩

/-- The flag's load. -/
theorem stgFlag_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgF p n v t) :
    WP isa (.block [ldh .x5 fBad]) t fun t' =>
      (StgF p n v t' ∧ t'.gpr .x5 = v) ∧ t'.mem = t.mem ∧ Keep mmRegs t t' := by
  have hw := h.1.st.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x5] (Q := fun t' => t'.gpr .x5 = v ∧ t'.mem = t.mem)
    (by brun [hw.x0, hdr_enc (show fBad < 32 by decide), hw.scr.ld (d := 8 * fBad) (by simp only [fBad]; omega_arith),
      h.2]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h5, hm⟩, k⟩ => ?_
  obtain st' : PSt p (mW p.bits) t' := h.1.st.step (rs := []) (hw.congr' (rs := [])
    (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)) (by rw [hm]; exact Frm.refl _ _ _) (by simp)
    (by simp) k
  exact ⟨⟨⟨⟨st', by rw [hm]; exact h.1.an, by rw [hm]; exact h.1.used, by rw [hm]; exact h.1.len,
    by rw [hm]; exact h.1.top, h.1.hl⟩, by rw [hm]; exact h.2⟩, h5⟩, hm, k.mono (by decide)⟩

/-- RSA's table. -/
theorem stgTab_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgF p n v t) :
    WP isa tableWrite t fun t' => StgT p n v t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain hT := pTab h.1.st.dims
  obtain sN := h.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.st.ws.scr.nowrap
  refine WP.mono (tableWrite_ok h.1.st hT) fun t' ⟨st', tab, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.frm (n' := n) st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) (by
    rw [f.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, aN, aTab]; omega_arith))
      (by omega_arith)]
    exact h.1.an)
  refine ⟨⟨⟨g, ?_⟩, tab⟩, i, k⟩
  rw [f.word_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, fBad]; omega_arith))
    (by simp only [fBad]; omega_arith)]
  exact h.2

/-- A sieve of the number in `aN`. -/
theorem stgSieve_ok (first : Bool) {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgT p n v t) :
    WP isa (seqs (sieve first)) t fun t' =>
      StgT p n (v ||| mask (anyPre n (4 * sieveWords first (mW p.bits)))) t' ∧ InScr p.B p.Z t.mem t'.mem ∧
        Keep mmRegs t t' := by
  obtain hT := pTab h.1.1.st.dims
  obtain sN := h.1.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.1.st.ws.scr.nowrap
  refine WP.mono (sieve_ok first h.1.1.st hT h.2 h.1.1.an h.1.2) fun t' ⟨st', hb, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.1.frm (n' := n) st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) (by
    rw [f.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega_arith)) (by omega_arith)]
    exact h.1.1.an)
  exact ⟨⟨⟨g, hb⟩, h.2.frm f (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [slot, hdrBytes, fBad]; omega_arith) (by omega_arith)⟩, i, k⟩

/-- `q` in `aN`, and its oddness. -/
theorem stgHalve_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgT p n v t) :
    WP isa (seqs halveQ) t fun t' =>
      StgT p (n / 2) (v ||| evenFlag (n / 2)) t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain hT := pTab h.1.1.st.dims
  obtain sN := h.1.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.1.st.ws.scr.nowrap
  refine WP.mono (halveQ_ok h.1.1.st h.1.1.an h.1.2) fun t' ⟨st', hq, hb, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.1.frm st' f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [stgRanges]) hq
  exact ⟨⟨⟨g, hb⟩, h.2.frm f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [slot, hdrBytes, aN, aTab]; omega_arith
    · simp only [slot, hdrBytes, fBad]; omega_arith) (by omega_arith)⟩, i, k⟩

/-- `p` in `aN` again. -/
theorem stgShape_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgT p n v t) :
    WP isa (seqs shapeP) t fun t' =>
      StgT p (cOf p) v t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain hT := pTab h.1.1.st.dims
  obtain sN := h.1.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.1.st.ws.scr.nowrap
  refine WP.mono (shapeP_ok h.1.1.st h.1.1.len h.1.1.top h.1.1.hl) fun t' ⟨st', hc, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.1.frm st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) hc
  refine ⟨⟨⟨g, ?_⟩, h.2.frm f (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [slot, hdrBytes, aN, aTab]; omega_arith) (by omega_arith)⟩, i, k⟩
  rw [f.word_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, fBad]; omega_arith))
    (by simp only [fBad]; omega_arith)]
  exact h.1.2

/-- A candidate whose shape's flag is not zero ends. -/
theorem stgReject_ok {p : PP} {s t : State} {n : Nat} (h : Stg p n t)
    (hz : shapeFlag p.g (mW p.bits) (cOf p) ≠ 0) (i : InScr p.B p.Z s.mem t.mem) (k : Keep mmRegs s t) :
    WP isa (finUsed 2) t fun t' => PEnd s t' p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r) := by
  have hL := h.hl
  have h256 := h.st.ws.h256
  obtain hshape := Bool.eq_false_iff.mpr fun h' => hz
    ((shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) h.st.dims.b1 h.st.dims.b2 h.st.dims.g).mpr h')
  rw [sieved_eq hL, hshape]
  simp only [Bool.not_false, ↓reduceIte]
  refine WP.mono (finUsed_end (s := s) h.st.ws.scr h.st.ws.x0 (by omega_arith) (by decide) h.used
    h.st.args.usedP h.st.ou i k) fun t' ht => ?_
  show KEnd s t' p.op p.up p.L 2 (p.r.length - (p.r.drop ((p.bits + 7) / 8)).length) none
  rw [List.length_drop, show p.r.length - (p.r.length - (p.bits + 7) / 8) = p.L by simp only [PP.L] at hL ⊢; omega_arith]
  exact ht

/-- `q` is odd when the shape's flag is zero. -/
theorem qOdd_of_shape {p : PP} (hd : PDims p) (hz : shapeFlag p.g (mW p.bits) (cOf p) = 0) :
    ((cOf p - 1) / 2) % 2 = 1 := by
  obtain hsh := (shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) hd.b1 hd.b2 hd.g).mp hz
  obtain hqs : Spec.Ffdh.primeShape ((cOf p - 1) / 2) = true := by
    simp only [Bool.and_eq_true] at hsh; exact hsh.1.1.2
  unfold Spec.Ffdh.primeShape at hqs
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hqs
  exact hqs.1.2

/-- The tests, once the shape's flag is zero. -/
theorem stgTests_ok (M : Mont) (R : Kernel) {p : PP} {s t : State} {n : Nat} (hs : PH p s) (h : Stg p n t)
    (hz : shapeFlag p.g (mW p.bits) (cOf p) = 0) (i : InScr p.B p.Z s.mem t.mem) (k : Keep mmRegs s t) :
    WP isa (tests M.mm R.run) t fun t' => PEnd s t' p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r) := by
  have hL := h.hl
  obtain hshape := (shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) h.st.dims.b1 h.st.dims.b2 h.st.dims.g).mp hz
  rw [sieved_eq hL, hshape]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact WP.mono (tests_ok M R (c := cOf p) h.st rfl (qOdd_of_shape h.st.dims hz) h.used hL) fun t' ht =>
    PEnd.trans_pre ht (outBytes_inScr i hs.ou.outZ) k

/-- `main`: `p`, its shape, and the tests. -/
theorem main_ok (M : Mont) (R : Kernel) {p : PP} {s : State} (h : PH p s)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (main M.mm R.run) s fun t => PEnd s t p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r) := by
  obtain nz : ∀ {x : BitVec 64}, (x == 0) = false → x ≠ 0 := fun h => by simpa using h
  obtain ez : ∀ {x : BitVec 64}, (x == 0) = true → x = 0 := fun h => by simpa using h
  unfold main
  simp only [List.append_assoc]
  rw [← List.append_assoc]
  -- `p` and its working space.
  refine wp_seqs_append (by simp [phase]) (by simp [residue]) ?_
  refine WP.mono (stgA_ok h hU hL) fun t₁ ⟨g₁, i₁, k₁⟩ => ?_
  -- The generator's congruence, rejected at once.
  refine wp_seqs_append (by simp [residue]) (by simp) ?_
  refine WP.mono (stgB_ok g₁) fun t₂ ⟨g₂, i₂, k₂⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₂) fun t₃ ⟨⟨g₃, h5₃⟩, hm₃, k₃⟩ => ?_)
  obtain i₃ : InScr p.B p.Z s.mem t₃.mem := by rw [hm₃]; exact i₁.trans i₂
  obtain kk₃ : Keep mmRegs s t₃ := ((k₁.trans k₂).trans k₃).mono (by decide)
  refine WP.ite (scr1 p.g (cOf p) == 0) (by rw [eval_zero, h5₃]) (fun _ => ?_)
    (fun hb => stgReject_ok g₃.1 (shape_ne (.inl (nz hb))) i₃ kk₃)
  -- The table, and the sieve of `p` by its first words: a small factor is rejected before `q`.
  refine wp_seqs_append (a := [_]) (by simp) (by simp [sieve]) ?_
  rw [seqs_one]
  refine WP.mono (stgTab_ok g₃) fun t₄ ⟨g₄, i₄, k₄⟩ => ?_
  refine wp_seqs_append (by simp [sieve]) (by simp) ?_
  refine WP.mono (stgSieve_ok true g₄) fun t₅ ⟨g₅, i₅, k₅⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₅.1) fun t₆ ⟨⟨g₆, h5₆⟩, hm₆, k₆⟩ => ?_)
  obtain tab₆ : TabOk t₆.mem p.B (mW p.bits) := by rw [hm₆]; exact g₅.2
  obtain i₆ : InScr p.B p.Z s.mem t₆.mem := by rw [hm₆]; exact (i₃.trans i₄).trans i₅
  obtain kk₆ : Keep mmRegs s t₆ := (((kk₃.trans k₄).trans k₅).trans k₆).mono (by decide)
  refine WP.ite (scr2 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₆]) (fun _ => ?_)
    (fun hb => stgReject_ok g₆.1 (shape_ne (.inr (.inl (nz hb)))) i₆ kk₆)
  -- `q`, rejected at once if it is even.
  unfold mainQ
  refine wp_seqs_append (by simp [halveQ]) (by simp) ?_
  refine WP.mono (stgHalve_ok ⟨g₆, tab₆⟩) fun t₇ ⟨g₇, i₇, k₇⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₇.1) fun t₈ ⟨⟨g₈, h5₈⟩, hm₈, k₈⟩ => ?_)
  obtain tab₈ : TabOk t₈.mem p.B (mW p.bits) := by rw [hm₈]; exact g₇.2
  obtain i₈ : InScr p.B p.Z s.mem t₈.mem := by rw [hm₈]; exact i₆.trans i₇
  obtain kk₈ : Keep mmRegs s t₈ := ((kk₆.trans k₇).trans k₈).mono (by decide)
  refine WP.ite (scr3 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₈]) (fun _ => ?_)
    (fun hb => stgReject_ok g₈.1 (shape_ne (.inr (.inr (.inl (nz hb))))) i₈ kk₈)
  -- The sieve of `q`: a small factor is rejected before `p`'s whole sieve.
  refine wp_seqs_append (by simp [sieve]) (by simp) ?_
  refine WP.mono (stgSieve_ok false ⟨g₈, tab₈⟩) fun t₉ ⟨g₉, i₉, k₉⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₉.1) fun t₁₀ ⟨⟨g₁₀, h5₁₀⟩, hm₁₀, k₁₀⟩ => ?_)
  obtain tab₁₀ : TabOk t₁₀.mem p.B (mW p.bits) := by rw [hm₁₀]; exact g₉.2
  obtain i₁₀ : InScr p.B p.Z s.mem t₁₀.mem := by rw [hm₁₀]; exact i₈.trans i₉
  obtain kk₁₀ : Keep mmRegs s t₁₀ := ((kk₈.trans k₉).trans k₁₀).mono (by decide)
  refine WP.ite (scr4 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₁₀]) (fun _ => ?_)
    (fun hb => stgReject_ok g₁₀.1 (shape_ne (.inr (.inr (.inr (.inl (nz hb)))))) i₁₀ kk₁₀)
  -- `p` again, and its whole sieve.
  unfold mainP
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [shapeP, loadA]) (by simp [sieve]) ?_
  refine WP.mono (stgShape_ok ⟨g₁₀, tab₁₀⟩) fun t₁₁ ⟨g₁₁, i₁₁, k₁₁⟩ => ?_
  refine wp_seqs_append (by simp [sieve]) (by simp) ?_
  refine WP.mono (stgSieve_ok false g₁₁) fun t₁₂ ⟨g₁₂, i₁₂, k₁₂⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₁₂.1) fun t₁₃ ⟨⟨g₁₃, h5₁₃⟩, hm₁₃, k₁₃⟩ => ?_)
  obtain i₁₃ : InScr p.B p.Z s.mem t₁₃.mem := by rw [hm₁₃]; exact (i₁₀.trans i₁₁).trans i₁₂
  obtain kk₁₃ : Keep mmRegs s t₁₃ := (((kk₁₀.trans k₁₁).trans k₁₂).trans k₁₃).mono (by decide)
  refine WP.ite (scr5 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₁₃])
    (fun hb => stgTests_ok M R h g₁₃.1 (scr5_zero.mp (ez hb)) i₁₃ kk₁₃)
    (fun hb => stgReject_ok g₁₃.1 (shape_ne (.inr (.inr (.inr (.inr (nz hb)))))) i₁₃ kk₁₃)

end VG.Proof.Ffdh.AArch64.ParameterCandidate
