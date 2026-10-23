module

import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Result
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.ShapeOk
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
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

`tests_ok`: the tests of `q` and then `p` (`testsSpec`); `main_ok`: `p`,
its shape's checks, and the tests, as `checkedCandidate` (`PEnd`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses checkedCandidate)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- How the candidate ends, from `s`, for the specification's result. -/
def PEnd (s t : State) (p : PP) : Option (Option Nat × List Byte) → Prop
  | none => KEnd s t p.op p.up p.L 0 0 none
  | some (some c, rest) => KEnd s t p.op p.up p.L 1 (p.r.length - rest.length) (some c)
  | some (none, rest) => KEnd s t p.op p.up p.L 2 (p.r.length - rest.length) none

theorem PEnd.trans_pre {s₀ s t : State} {p : PP} {res : Option (Option Nat × List Byte)} (h : PEnd s t p res)
    (hout : outBytes s.mem p.op p.L = outBytes s₀.mem p.op p.L) (k₀ : Keep mmRegs s₀ s) : PEnd s₀ t p res := by
  rcases res with _ | ⟨_ | _, _⟩ <;> exact KEnd.trans_pre h hout (k₀.mono (by decide))

/-- The tests of `q` and then `p`, from the tape `r`. -/
def testsSpec (c : Nat) (r : List Byte) : Option (Option Nat × List Byte) := do
  let (qpass, r) ← checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength ((c - 1) / 2))) r
  if !qpass then return (none, r)
  let (ppass, r) ← checkWitnesses c (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength c)) r
  return (if ppass then some c else none, r)

/-- `kStat` against 1. -/
theorem stat1_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {v : Nat} (hv : v < 2 ^ 63) (hS : word s.mem B (8 * kStat) = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 1]) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (v = 1)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hS' : s.mem.readW (B + BitVec.ofNat 64 (8 * kStat)) 64 = BitVec.ofNat 64 v := hS
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), h.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega),
      hS']) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ?_
  refine ⟨?_, hm, k⟩
  rw [eval_zero, h3, eq_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact congrArg some (decide_eq_decide.mpr (by omega))

/-- The tests, once the shape passed. -/
theorem tests_ok (M : Mont) (R : Kernel) {p : PP} {s : State} {c : Nat} (h : PSt p (mW p.bits) s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (mW p.bits) aN) (mW p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests M.mm R.run) s fun t => PEnd s t p (testsSpec c (p.r.drop p.L)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have h256 := h.ws.h256
  have hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega) _
  have hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega) _).1
  obtain ⟨_, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu
  have hEZq := h.dims.eZ true
  have hmbq : p.mb true = p.bits - 1 := by simp only [PP.mb, ↓reduceIte]
  rw [hmbq] at hEZq
  unfold testsSpec
  rw [hbq, hbp]
  unfold tests
  refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
  refine WP.mono (testQ_ok M R h hc hq hqo hU hL hL) fun t₁ e₁ => ?_
  have stt := MrEnd.stat e₁
  obtain ⟨fix₁, -, hrest₁, isc₁, k₁⟩ := e₁
  have ho₁ := fix₁.st.ou
  have hout : ∀ {t : State}, InScr p.B p.Z s.mem t.mem → outBytes t.mem p.op p.L = outBytes s.mem p.op p.L :=
    fun hi => outBytes_inScr hi h.ou.outZ
  simp only [seqs]
  generalize checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop p.L) = resQ
    at stt hrest₁ ⊢
  have hv : ∀ v, word t₁.mem p.B (8 * kStat) = BitVec.ofNat 64 v → v ≤ 2 →
      WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 1]) t₁ fun t =>
        isa.eval (.zero .x .x3) t = some (decide (v = 1)) ∧ MrFix p (mW (p.bits - 1)) ((c - 1) / 2) (p.bits - 1)
          (Spec.Ffdh.primeChecks (p.bits - 1)) t ∧ t.mem = t₁.mem ∧ Keep [.x3] t₁ t :=
    fun v hS hv2 => WP.mono (stat1_ok fix₁.st.ws (by omega) hS) fun t ⟨hz, hm, k⟩ =>
      ⟨hz, fix₁.same hEZq hm k (by decide), hm, k⟩
  -- The end of a failed test of `q`.
  have qfail : ∀ {t₂ : State}, t₂.mem = t₁.mem → Keep [.x3] t₁ t₂ → (∀ rest, resQ ≠ some (true, rest)) →
      WP isa qResult t₂ fun t => PEnd s t p (do
        let (qpass, r) ← resQ
        if !qpass then return (none, r)
        let (ppass, r) ← checkWitnesses c (Spec.Ffdh.primeChecks p.bits) r
        return (if ppass then some c else none, r)) := by
    intro t₂ hm k hnp
    have ws₂ := fix₁.st.ws.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)
    refine WP.mono (qResult_ok (c := c) (L := p.L) (r := p.r) ws₂ (ho₁.congr k.wr)
      (by rw [hm]; exact fix₁.st.args.usedP) hnp (by rw [hm]; exact stt.1)
      (fun b rest hr => by rw [hm]; exact stt.2 b rest hr)) fun t ht => ?_
    have hk : Keep mmRegs s t₂ := (k₁.trans k).mono (by decide)
    have ho : outBytes t₂.mem p.op p.L = outBytes s.mem p.op p.L := by rw [hm]; exact hout isc₁
    rcases resQ with _ | ⟨_ | _, rest⟩
    · exact PEnd.trans_pre (p := p) (res := none) ht ho hk
    · exact PEnd.trans_pre (p := p) (res := some (none, rest)) ht ho hk
    · exact absurd rfl (hnp rest)
  rcases hQ : resQ with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (hv 0 (stt.1 hQ) (by decide)) fun t₂ ⟨hz, _, hm, k⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    rw [← hQ]; exact qfail hm k (fun rest h' => by rw [hQ] at h'; cases h')
  · obtain ⟨hS, _⟩ := stt.2 b rest hQ
    refine WP.seq (WP.mono (hv (if b then 1 else 2) hS (by cases b <;> decide)) fun t₂ ⟨hz, fix₂, hm, k⟩ => ?_)
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      rw [← hQ]; exact qfail hm k (fun rest' h' => by rw [hQ] at h'; cases h')
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      obtain ⟨u, hul, rfl, hUu⟩ := (hrest₁ true rest hQ).2
      refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
      refine WP.mono (testP_ok M R fix₂.st hc (by rw [hm]; exact hUu) hul hL) fun t₃ e₃ => ?_
      have stp := MrEnd.stat e₃
      obtain ⟨fix₃, -, -, isc₃, k₃⟩ := e₃
      rw [seqs_one]
      have hn₃ : wv t₃.mem p.B (slot (mW p.bits) aN) ((p.L + 7) / 8) = c := by
        obtain ⟨_, hc₃⟩ := fix₃.ctx
        refine wv_low hc₃.n (by simp only [PP.L, mW]; omega)
          (Nat.lt_of_lt_of_le hcu (Nat.pow_le_pow_right (by decide) (by simp only [PP.L]; omega)))
      refine WP.mono (pResult_ok (c := c) (r := p.r) fix₃.st.ws (by simp only [PP.L]; omega)
        (by simp only [PP.L, mW]; omega) hn₃ fix₃.st.ou fix₃.st.args.out fix₃.len fix₃.st.args.usedP fix₃.msk
        stp.1 stp.2) fun t ht => ?_
      have hk : Keep mmRegs s t₃ := ((k₁.trans k).trans k₃).mono (by decide)
      have ho : outBytes t₃.mem p.op p.L = outBytes s.mem p.op p.L :=
        hout (isc₁.trans ((show InScr p.B p.Z t₁.mem t₂.mem by rw [hm]; exact InScr.refl _ _ _).trans isc₃))
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
      generalize checkWitnesses c (Spec.Ffdh.primeChecks p.bits) (p.r.drop u) = resP at ht ⊢
      rcases resP with _ | ⟨_ | _, rest'⟩
      · exact PEnd.trans_pre (p := p) (res := none) ht ho hk
      · exact PEnd.trans_pre (p := p) (res := some (none, rest')) ht ho hk
      · exact PEnd.trans_pre (p := p) (res := some (some c, rest')) ht ho hk

theorem checked_eq {bits g : Nat} {r : List Byte} (h : (bits + 7) / 8 ≤ r.length) :
    checkedCandidate bits g r =
      if !(Spec.Ffdh.generationShape bits g (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
          Spec.Ffdh.primeShape (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
          Spec.Ffdh.primeShape ((Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2))
      then some (none, r.drop ((bits + 7) / 8))
      else testsSpec (Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))))
        (r.drop ((bits + 7) / 8)) := by
  simp only [checkedCandidate, VG.Proof.Ffdh.ParameterCandidate.draw_of_le h, bind, Option.bind]
  rfl

/-- RSA's table survives changes below it. -/
theorem TabOk.frm {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (h : TabOk m B w)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, r.1 + r.2 ≤ slot w aTab) (hn : slot w aTab + 2048 ≤ 2 ^ 64) :
    TabOk m' B w := fun i hi => by
  rw [hf.word_eq (fun r hr => Or.inr (by have := hd r hr; omega)) (by omega)]; exact h i hi

/-- `main`: `p`, its shape, and the tests. -/
theorem main_ok (M : Mont) (R : Kernel) {p : PP} {s : State} (h : PH p s)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (main M.mm R.run) s fun t => PEnd s t p (checkedCandidate p.bits p.g p.r) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hZ := h.dims.z
  have hn := h.scr.nowrap
  rw [checked_eq hL]
  generalize hc : Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take ((p.bits + 7) / 8))) = c
  have hc' : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) := hc.symm
  have hW1 : 8 ≤ mW p.bits := by simp only [mW]; omega_arith
  have hW2 : mW p.bits ≤ 128 := by simp only [mW]; omega_arith
  have hT : slot (mW p.bits) aTab + 2048 ≤ p.Z := by simp only [slot, hdrBytes, aTab, mW, PP.L] at hZ ⊢; omega_arith
  have sN : slot (mW p.bits) aN + 8 * (mW p.bits + 2) ≤ slot (mW p.bits) aTab := by
    simp only [slot, hdrBytes, aN, aTab]; omega_arith
  have hNZ : slot (mW p.bits) aN + 8 * (mW p.bits + 2) ≤ p.Z := by omega_arith
  have hBad : 8 * fBad + 8 ≤ 256 := by decide
  have hdrT : 256 ≤ slot (mW p.bits) aN := by simp only [slot, hdrBytes]; omega_arith
  unfold main
  simp only [List.append_assoc]
  -- `p` and its working space.
  refine wp_seqs_append (by simp [phase]) (by simp [shapeP, loadA]) ?_
  refine WP.mono (phase_ok h false) fun t₁ ht => ?_
  have hmb : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
  have st₁ := ht.st
  rw [hmb] at st₁
  have hlen : word t₁.mem p.B (8 * sK) = BitVec.ofNat 64 p.L := by have := ht.len; rw [hmb] at this; exact this
  have htop : word t₁.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1) := by
    have := ht.top; rw [hmb] at this; exact this
  have i₁ : InScr p.B p.Z s.mem t₁.mem := InScr.of_frm ht.frm fun r hr => by
    have := phaseRanges_kmut r hr; omega_arith
  have hU₁ : word t₁.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L := by
    rw [ht.frm.word_eq (fun r hr => by
      simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [kUsed, sK, fChecks, sW, sArr, sStride, Public.sMask, fTop, sFn] <;> omega_arith)
      (by simp only [kUsed, sFn]; omega_arith)]
    exact hU
  refine wp_seqs_append (by simp [shapeP, loadA]) (by simp [residue]) ?_
  refine WP.mono (shapeP_ok st₁ hlen htop hL) fun t₂ ⟨st₂, hn₂, f₂, k₂⟩ => ?_
  rw [← hc'] at hn₂
  -- The generator's congruence.
  refine wp_seqs_append (by simp [residue]) (by simp) ?_
  refine WP.mono (residue_ok st₂ hn₂) fun t₃₀ ⟨st₃₀, hr₃₀, f₃₀, k₃₀⟩ => ?_
  -- Its flag, rejected at once.
  have hs₃₀ := st₃₀.ws.scr
  refine WP.seq (WP.mono (WP.keep [.x5] (Q := fun t =>
      t.gpr .x5 = resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) ∧ t.mem = t₃₀.mem) (by
    brun [st₃₀.ws.x0, hdr_enc (show fBad < 32 by decide), hs₃₀.ld (d := 8 * fBad) (by omega_arith), hr₃₀])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h5r, hm₃⟩, k₃'⟩ => ?_)
  have st₃ : PSt p (mW p.bits) t₃ := st₃₀.step (rs := []) (st₃₀.ws.congr' (rs := [])
    (by rw [hm₃]; exact Frm.refl _ _ _) (by simp) k₃' (by decide)) (by rw [hm₃]; exact Frm.refl _ _ _)
    (by simp) (by simp) k₃'
  have hr₃ : word t₃.mem p.B (8 * fBad) = resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) := by
    rw [hm₃]; exact hr₃₀
  have f₃ : Frm p.B [(8 * fBad, 8)] t₂.mem t₃.mem := by rw [hm₃]; exact f₃₀
  have k₃ : Keep mmRegs t₂ t₃ := (k₃₀.trans k₃').mono (by decide)
  have e : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm p.B rs m m' → (∀ r ∈ rs, 8 * kUsed + 8 ≤ r.1 ∨
      r.1 + r.2 ≤ 8 * kUsed) → word m' p.B (8 * kUsed) = word m p.B (8 * kUsed) := fun f d =>
    f.word_eq d (by simp only [kUsed, sFn]; omega_arith)
  have hsh := shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 h.dims.g
  rw [← hc'] at hsh
  refine WP.ite (resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) == 0) (by rw [eval_zero, h5r])
    (fun hbr => ?_) (fun hbr => ?_)
  rotate_left
  · -- A rejected congruence.
    have hz : resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) ≠ 0 := by simpa using hbr
    have hz' : shapeFlag p.g c ≠ 0 := fun h0 => hz (by
      simp only [shapeFlag, VG.Proof.Rsa.AArch64.or_eq_zero] at h0; exact h0.1.1.1)
    have hshape : (Spec.Ffdh.generationShape p.bits p.g c && Spec.Ffdh.primeShape c &&
        Spec.Ffdh.primeShape ((c - 1) / 2)) = false := Bool.eq_false_iff.mpr fun h' => hz' (hsh.mpr h')
    rw [hshape]
    simp only [Bool.not_false, ↓reduceIte]
    have i₃ : InScr p.B p.Z s.mem t₃.mem := by
      refine i₁.trans ((InScr.of_frm f₂ ?_).trans (InScr.of_frm f₃ ?_))
      all_goals
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> omega_arith
    have hU₃ : word t₃.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L := by
      rw [e f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)),
        e f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [kUsed, sFn]; omega_arith))]
      exact hU₁
    have k₁₃ : Keep mmRegs s t₃ := ((ht.keep.trans k₂).trans k₃).mono (by decide)
    refine WP.mono (finUsed_end (s := s) st₃.ws.scr st₃.ws.x0 (by omega_arith) (by decide) hU₃
      st₃.args.usedP st₃.ou i₃ k₁₃) fun t ht => ?_
    show KEnd s t p.op p.up p.L 2 (p.r.length - (p.r.drop ((p.bits + 7) / 8)).length) none
    rw [List.length_drop, show p.r.length - (p.r.length - (p.bits + 7) / 8) = p.L by simp only [PP.L] at hL ⊢; omega_arith]
    exact ht
  have hn₃ : wv t₃.mem p.B (slot (mW p.bits) aN) (mW p.bits) = c := by
    rw [f₃.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith)) (by omega_arith)]; exact hn₂
  -- The table.
  refine wp_seqs_append (a := [_]) (by simp) (by simp [sieve]) ?_
  rw [seqs_one]
  refine WP.mono (tableWrite_ok st₃ hT) fun t₄ ⟨st₄, tab₄, f₄, k₄⟩ => ?_
  have dT : ∀ r ∈ [(slot (mW p.bits) aTab, 2048)], 8 * fBad + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * fBad := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by omega_arith)
  have hn₄ : wv t₄.mem p.B (slot (mW p.bits) aN) (mW p.bits) = c := by
    rw [f₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by omega_arith)) (by omega_arith)]; exact hn₃
  have hr₄ : word t₄.mem p.B (8 * fBad) = resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) := by
    rw [f₄.word_eq dT (by omega_arith)]; exact hr₃
  -- The sieve of `p`.
  refine wp_seqs_append (by simp [sieve]) (by simp [halveQ]) ?_
  refine WP.mono (sieve_ok st₄ hT tab₄ hn₄ hr₄) fun t₅ ⟨st₅, hb₅, f₅, k₅⟩ => ?_
  have hn₅ : wv t₅.mem p.B (slot (mW p.bits) aN) (mW p.bits) = c := by
    rw [f₅.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith)) (by omega_arith)]; exact hn₄
  have tab₅ := tab₄.frm f₅ (fun r hr => by rw [List.mem_singleton.mp hr]; omega_arith) (by omega_arith)
  -- `q`.
  refine wp_seqs_append (by simp [halveQ]) (by simp [sieve]) ?_
  refine WP.mono (halveQ_ok st₅ hn₅ hb₅) fun t₆ ⟨st₆, hn₆, hb₆, f₆, k₆⟩ => ?_
  have tab₆ := tab₅.frm f₆ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sN
    · omega_arith) (by omega_arith)
  -- The sieve of `q`.
  refine wp_seqs_append (by simp [sieve]) (by simp) ?_
  refine WP.mono (sieve_ok st₆ hT tab₆ hn₆ hb₆) fun t₇ ⟨st₇, hb₇, f₇, k₇⟩ => ?_
  have hn₇ : wv t₇.mem p.B (slot (mW p.bits) aN) (mW p.bits) = c / 2 := by
    rw [f₇.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith)) (by omega_arith)]; exact hn₆
  have hU₇ : word t₇.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L := by
    rw [e f₇ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)),
      e f₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inl (by simp only [kUsed, sFn]; omega_arith)
        · exact .inr (by decide)),
      e f₅ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)),
      e f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [kUsed, sFn]; omega_arith)),
      e f₃ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by decide)),
      e f₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [kUsed, sFn]; omega_arith))]
    exact hU₁
  have i₇ : InScr p.B p.Z s.mem t₇.mem := by
    refine i₁.trans ((InScr.of_frm f₂ ?_).trans ((InScr.of_frm f₃ ?_).trans ((InScr.of_frm f₄ ?_).trans
      ((InScr.of_frm f₅ ?_).trans ((InScr.of_frm f₆ ?_).trans (InScr.of_frm f₇ ?_))))))
    all_goals
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega_arith
  have k₁₇ : Keep mmRegs s t₇ :=
    ((((((ht.keep.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).mono (by decide)
  have hflag : word t₇.mem p.B (8 * fBad) = shapeFlag p.g c := by
    rw [hb₇]; simp only [shapeFlag]
  -- The flag.
  simp only [seqs]
  have hs₇ := st₇.ws.scr
  refine WP.seq (WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = shapeFlag p.g c ∧ t.mem = t₇.mem) (by
    brun [st₇.ws.x0, hdr_enc (show fBad < 32 by decide), hs₇.ld (d := 8 * fBad) (by omega_arith), hflag])
    (by decide) (by decide) (by decide +kernel)) fun t₈ ⟨⟨h5, hm₈⟩, k₈⟩ => ?_)
  have i₈ : InScr p.B p.Z s.mem t₈.mem := by rw [hm₈]; exact i₇
  have k₁₈ : Keep mmRegs s t₈ := (k₁₇.trans k₈).mono (by decide)
  have st₈ : PSt p (mW p.bits) t₈ := st₇.step (rs := []) (st₇.ws.congr' (rs := [])
    (by rw [hm₈]; exact Frm.refl _ _ _) (by simp) k₈ (by decide)) (by rw [hm₈]; exact Frm.refl _ _ _) (by simp)
    (by simp) k₈
  refine WP.ite (shapeFlag p.g c == 0) (by rw [eval_zero, h5]) (fun hb => ?_) (fun hb => ?_)
  · -- The tests.
    have hz : shapeFlag p.g c = 0 := by simpa using hb
    have hshape := hsh.mp hz
    rw [hshape]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hqs : Spec.Ffdh.primeShape ((c - 1) / 2) = true := by
      simp only [Bool.and_eq_true] at hshape; exact hshape.2
    have hqo : ((c - 1) / 2) % 2 = 1 := by
      unfold Spec.Ffdh.primeShape at hqs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hqs
      exact hqs.1.2
    obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
      (Spec.Rsa.os2ip (p.r.take p.L))
    rw [← hc'] at hpo
    have hq8 : wv t₈.mem p.B (slot (mW p.bits) aN) (mW p.bits) = (c - 1) / 2 := by
      rw [hm₈, hn₇]; omega_arith
    refine WP.mono (tests_ok M R st₈ hc' hq8 hqo (by rw [hm₈]; exact hU₇) hL) fun t ht => ?_
    exact PEnd.trans_pre ht (outBytes_inScr i₈ h.ou.outZ) k₁₈
  · -- A rejected shape.
    have hz : shapeFlag p.g c ≠ 0 := by simpa using hb
    have hshape : (Spec.Ffdh.generationShape p.bits p.g c && Spec.Ffdh.primeShape c &&
        Spec.Ffdh.primeShape ((c - 1) / 2)) = false := Bool.eq_false_iff.mpr fun h' => hz (hsh.mpr h')
    rw [hshape]
    simp only [Bool.not_false, ↓reduceIte]
    refine WP.mono (finUsed_end (s := s) st₈.ws.scr st₈.ws.x0 (by omega_arith) (by decide) (by rw [hm₈]; exact hU₇)
      st₈.args.usedP st₈.ou i₈ k₁₈) fun t ht => ?_
    show KEnd s t p.op p.up p.L 2 (p.r.length - (p.r.drop ((p.bits + 7) / 8)).length) none
    rw [List.length_drop, show p.r.length - (p.r.length - (p.bits + 7) / 8) = p.L by simp only [PP.L] at hL ⊢; omega_arith]
    exact ht

end VG.Proof.Ffdh.AArch64.ParameterCandidate
