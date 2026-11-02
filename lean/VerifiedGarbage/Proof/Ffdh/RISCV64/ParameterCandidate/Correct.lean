module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Tests
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# An FFDH parameter candidate on RISC-V: correctness

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{Main,Correct}.lean`):
`main_ok`, p from the tape, its shape and the tests, against
`checkedCandidate`; `code_correct`, `code` meets `pcContract`'s
postcondition and keeps what the calling convention preserves, for a round
whose call meets `RoundCall`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_zero_ofNat)
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (geFlag_ok)
open VG.Proof.Ffdh.ParameterCandidate (checkedCandidate checked_eq testsSpec)

/-- `main`: p, its shape, and the tests. -/
theorem main_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {s : State} (h : St p s)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (main R.name R.code) s (CEnd p (checkedCandidate p.bits p.g p.r)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  rw [checked_eq hL]
  generalize hc : Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take ((p.bits + 7) / 8))) = c
  have hc' : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) := hc.symm
  have hsh := shape_iff (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 h.dims.g
  obtain ⟨ho, hl, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc'] at hsh ho hl hcu
  -- A rejected shape.
  have reject : ∀ {t : State}, St p t → word t.mem p.B 152 = BitVec.ofNat 64 p.L →
      (Spec.Ffdh.generationShape p.bits p.g c && Spec.Ffdh.primeShape c &&
        Spec.Ffdh.primeShape ((c - 1) / 2)) = false →
      WP isa (.block (finish 2)) t (CEnd p (if !(Spec.Ffdh.generationShape p.bits p.g c &&
        Spec.Ffdh.primeShape c && Spec.Ffdh.primeShape ((c - 1) / 2)) then some (none, p.r.drop p.L)
        else testsSpec c (p.r.drop p.L))) := fun st hu hf => by
    rw [hf]
    simp only [Bool.not_false, ↓reduceIte]
    refine finEnd st (r := 2) (v := p.L) (Or.inr rfl) rfl rfl ?_ hu
    simp only [usedOf, List.length_drop, Nat.reduceEqDiff, ↓reduceIte]
    omega_arith
  unfold main
  refine WP.assoc (WP.seq (WP.mono (mainA_ok h hU hL) fun t₂ ⟨st₂, ph₂, hU₂, hn₂⟩ => ?_))
  rw [← hc'] at hn₂
  refine WP.seq (WP.mono (residue_mb st₂ ph₂ hU₂ hn₂) fun t₃ M₃ => ?_)
  refine WP.seq (WP.mono M₃.badLoad fun t₄ ⟨M₄, t5⟩ => ?_)
  refine WP.ite (word t₃.mem p.B 200 == 0) (by rw [eval_zero, t5]) (fun hz => ?_) (fun hz => ?_)
  rotate_left
  · -- The congruence fails.
    refine reject M₄.st M₄.u (Bool.eq_false_iff.mpr fun ht => ?_)
    have h0 : word t₃.mem p.B 200 = 0#64 := M₃.bad.mpr (hsh.mpr ht).1
    simp [h0] at hz
  refine WP.seq (WP.mono M₄.sieve fun t₅ M₅ => ?_)
  refine WP.seq (WP.mono M₅.halve fun t₆ M₆ => ?_)
  refine WP.seq (WP.mono M₆.sieve fun t₇ M₇ => ?_)
  refine WP.seq (WP.mono M₇.badLoad fun t₈ ⟨M₈, t5'⟩ => ?_)
  have hall : word t₇.mem p.B (8 * hBad) = 0#64 ↔
      goodRes p.g c ∧ (∀ d ∈ oddPrimes256, c % d ≠ 0) ∧ c / 2 % 2 = 1 ∧ ∀ d ∈ oddPrimes256, c / 2 % d ≠ 0 :=
    M₇.bad.trans ⟨fun ⟨⟨⟨a, b⟩, c'⟩, d⟩ => ⟨a, b, c', d⟩, fun ⟨a, b, c', d⟩ => ⟨⟨⟨a, b⟩, c'⟩, d⟩⟩
  refine WP.ite (word t₇.mem p.B 200 == 0) (by rw [eval_zero, t5']) (fun hz' => ?_) (fun hz' => ?_)
  · -- The shape passes: the tests.
    have hshape := hsh.mp (hall.mp (beq_iff_eq.mp hz'))
    rw [hshape]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hq : (c - 1) / 2 = c / 2 := by omega_arith
    obtain ⟨_, _, hqo, _⟩ := hall.mp (beq_iff_eq.mp hz')
    rw [hc'] at hq hqo ⊢
    refine tests_ok hR M₈.st rfl ?_ (by rw [hq]; exact hqo) M₈.u hL
    rw [hq, ← hc']; exact M₈.n
  · refine reject M₈.st M₈.u (Bool.eq_false_iff.mpr fun ht => ?_)
    have h0 : word t₇.mem p.B 200 = 0#64 := hall.mpr (hsh.mpr ht)
    simp [h0] at hz'

theorem checked_short {bits g : Nat} {r : List Byte} (h : r.length < (bits + 7) / 8) :
    checkedCandidate bits g r = none := by
  have : (r.take ((bits + 7) / 8)).length ≠ (bits + 7) / 8 := by rw [List.length_take]; omega
  simp only [checkedCandidate, Spec.RsaKeyGen.draw, this, ↓reduceIte, bind, Option.bind]

/-- The tape's length and `out_len`. -/
theorem lenLoad_ok {p : PP} {t : State} (h : St p t) :
    WP isa (.block [ldh .t3 hRandLen, ldh .t4 hLen]) t fun u => ((u.gpr .t3 = BitVec.ofNat 64 p.r.length ∧
      u.gpr .t4 = BitVec.ofNat 64 p.L ∧ u.mem = t.mem) ∧ Keep [.t3, .t4] t u) ∧ u.sp = t.sp := by
  refine WP.rdwr (WP.keep [.t3, .t4] ?_ (by rfl) (by rfl)) |>.mono fun u ⟨a, _, _, b⟩ => ⟨a, b⟩
  simp only [ldh, hRandLen, hLen]
  brun [h.s6, h.ld (d := 144) (by decide), h.ld (d := 24) (by decide), h.al (d := 144) (by decide) (by decide),
    h.al (d := 24) (by decide) (by decide), h.args.rlen', h.args.len']

/-- The length check's flag. -/
theorem lenChk_ok {p : PP} {t : State} (h : St p t) (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.block (([ldh .t3 hRandLen, ldh .t4 hLen] : List Instr) ++ geFlag .t5 .t3 .t4)) t fun v =>
      isa.eval (.zero .t5) v = some (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) ∧ St p v ∧
        word v.mem p.B 152 = BitVec.ofNat 64 p.L := by
  have hrl := h.dims.rl
  have hb2 := h.dims.b2
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (lenLoad_ok h) fun u ⟨⟨⟨a3, a4, am⟩, ka⟩, asp⟩ => ?_
  refine WP.mono (WP.rdwr (geFlag_ok a3 a4 hrl (by omega))) fun v ⟨⟨⟨a5, vm⟩, kv⟩, _, _, vsp⟩ => ?_
  have hm : v.mem = t.mem := vm.trans am
  exact ⟨eval_zero_ofNat v .t5 (by split <;> decide) a5,
    h.step (by rw [hm]; exact Frm.refl _ _ _) (ka.trans kv) (vsp.trans asp), by rw [hm]; exact hU⟩

/-- The length check, then `main` or the status 0. -/
theorem body_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {t : State} (h : St p t)
    (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.seq (.block (([ldh .t3 hRandLen, ldh .t4 hLen] : List Instr) ++ geFlag .t5 .t3 .t4))
      (.ite (.zero .t5) (.block (finish 0)) (main R.name R.code))) t
      (CEnd p (checkedCandidate p.bits p.g p.r)) := by
  refine WP.seq (WP.mono (lenChk_ok h hU) fun v ⟨he, st, hUv⟩ => ?_)
  refine WP.ite (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) he (fun hb => ?_) (fun hb => ?_)
  · have hs : p.r.length < p.L := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_left (by omega)] at hb; exact absurd hb (by decide)
    rw [checked_short (by omega)]
    exact finEnd st (r := 0) (Or.inl rfl) rfl rfl rfl hUv
  · have hl : p.L ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega)])
    exact main_ok hR st hUv hl

theorem preserved_cases : ∀ r ∈ preserved, ∃ i < 13, saved i = r := by decide

theorem a0_cases : ∀ i < 13, Reg.a0 ≠ saved i := by decide

theorem small_setWidth {k : Nat} (hk : k < 2 ^ 32) : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem status_le (res : Option (Option Nat × Spec.RsaKeyGen.Rand)) : Proof.Ffdh.candidateStatus res ≤ 2 := by
  rcases res with _ | ⟨_ | _, _⟩ <;> simp [Proof.Ffdh.candidateStatus]

/-- `vg_ffdh_parameter_candidate`, for a round whose call meets `RoundCall`. -/
theorem code_correct {R : RoundImpl} (hR : RoundCall R) (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (code R.name R.code) s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa (code R.name R.code) s fun t => abiPreserved s t ∧ pcPost s t
  have hpre := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -⟩ := h
  have hLe : (s.gpr .a1).toNat = (ppOf s).L := hL
  have hlen : (ppOf s).r.length = (s.gpr .a6).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold code
  refine wp_then (front_ok s hpre) fun t ⟨st, hU⟩ => ?_
  refine wp_then (body_ok hR st hU) fun u hu => ?_
  obtain ⟨E, u3, uo, uu⟩ := hu
  refine WP.mono (exit_ok E) fun w ⟨wr, wm, wsp, wo⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := preserved_cases r hr
    rw [wr i hi]; rfl
  · rw [wsp, E.sp]; rfl
  · rw [show Reg.ra = saved 12 from rfl, wr 12 (by decide)]; rfl
  · have hres : pcResult s = checkedCandidate (ppOf s).bits (ppOf s).g (ppOf s).r :=
      (VG.Proof.Ffdh.ParameterCandidate.checkedCandidate_eq _ _ _).symm
    simp only [pcPost]
    rw [hres, wm, wo .a0 (by decide) a0_cases, u3, hLe]
    refine ⟨small_setWidth (by have := status_le (checkedCandidate (ppOf s).bits (ppOf s).g (ppOf s).r); omega),
      ?_, ?_⟩
    · refine uo.trans ?_
      generalize checkedCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      refine congrArg (· :: []) (uu.trans ?_)
      rw [← hlen]
      generalize checkedCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
