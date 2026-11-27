module

public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.CT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTChain
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Tests
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop

-- separate module: the candidate builds in parallel with the controller

/-!
# An FFDH parameter candidate on RISC-V: correctness and constant time

`main_ok`, p from the tape, its shape (the congruence, RSA's trial
division of p and q, q's parity) and the tests, against
`Spec.Ffdh.sievedParameterCandidate`; `front_tab`, the table where the state
names it after the front; `code_correct`, `code` meets `pcContract`'s
postcondition and keeps what the calling convention preserves.

## The tests in constant time

Two runs are related by `Two Φ`, both satisfying `Φ a` for the same public
data `a`, whatever the registers they save on entry (`PP.with`). Each piece
is checked by the taint analysis from the registers the predicate pins:
what a piece loads from memory (the tape's address and length, a count) is
pinned by the next predicate. The branches are on what the public data
decides: a witness's range and its round's result, a test's status, the
tape's length.

## Constant time

`main_ct`, p's congruence branches on the generator, pinned once loaded, the
shape checks on `hBad`, which the candidate decides (`MB`); trial division
(`trialSieve_ct`) loops while the entry tested, a function of the candidate
and of how many are left, does not divide it, from the table's address,
which the contract makes public (`taintSym`); the tests are `tests_ct`;
`code_ct`, two runs with the same public arguments and tape (`qOf`) leak the
same, whatever the registers they save. The entry loads
`scratch_len` from the stack, pinned once loaded; `zeroOut` and the length
check load `out`, `out_len` and the tape's length from the header, pinned
once loaded; the exit loads `scratch_len` from the header to find the save
area.

## Verified for any round

`candidate_correct` and `candidate_ct`, for any implementation of the
round, against the internal contract
`Proof.Ffdh.sievedParameterCandidateContract` under `abi.withConsts` with RSA's table of trial division (`pc_pre`, `pc_post`,
`pc_pub`), with the 96 bytes of stack below `sp` its frame uses
(`candidate_stack`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_zero_ofNat)
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (geFlag_ok)
open VG.Proof.Ffdh.ParameterCandidate (sievedTests sieved_eq)

/-- The sieved specification's shape checks. -/
abbrev shapeOk (p : PP) (c : Nat) : Bool :=
  Spec.Ffdh.generationShape p.bits p.g c && Spec.Ffdh.primeShape c && Spec.Ffdh.primeShape ((c - 1) / 2) &&
    !Spec.RsaKeyGen.obviouslyComposite p.bits c && !Spec.RsaKeyGen.obviouslyComposite p.bits ((c - 1) / 2)

/-- A rejected shape. -/
theorem reject_ok {p : PP} {c : Nat} {t : State} (st : St p t) (hL : p.L ≤ p.r.length)
    (hu : word t.mem p.B 152 = BitVec.ofNat 64 p.L)
    (hf : shapeOk p c = false) :
    WP isa (.block (finish 2)) t
      (CEnd p (if !shapeOk p c then some (none, p.r.drop p.L) else sievedTests c (p.r.drop p.L))) := by
  have hb1 := st.dims.b1
  have hb2 := st.dims.b2
  rw [hf]
  simp only [Bool.not_false, ↓reduceIte]
  refine finEnd st (r := 2) (v := p.L) (Or.inr rfl) rfl rfl ?_ hu
  simp only [usedOf, List.length_drop, Nat.reduceEqDiff, ↓reduceIte]
  omega_arith

/-- `mainQ`, with p in array 0: q's shape, and the tests. -/
theorem mainQ_ok {R : RoundImpl} {p : PP} {T : Addr} {c : Nat} {s : State}
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) (hL : p.L ≤ p.r.length)
    (h : MB p T c (goodRes p.g c ∧ VG.Proof.RsaKeyGen.trialPrefix c (trialN p.bits) = false) s)
    (hp : goodRes p.g c ∧ VG.Proof.RsaKeyGen.trialPrefix c (trialN p.bits) = false) :
    WP isa (mainQ R.name R.code) s
      (CEnd p (if !shapeOk p c then some (none, p.r.drop p.L) else sievedTests c (p.r.drop p.L))) := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hsh := sieved_shape_iff (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 h.st.dims.g
  obtain ⟨ho, -⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hsh ho
  unfold mainQ
  refine WP.seq (WP.mono h.halve fun t₁ M₁ => ?_)
  refine WP.seq (WP.mono (trialSieve_ok M₁) fun t₂ M₂ => ?_)
  refine WP.seq (WP.mono M₂.badLoad fun t₃ ⟨M₃, t5⟩ => ?_)
  refine WP.ite (word t₂.mem p.B 200 == 0) (by rw [eval_zero, t5]) (fun hz => ?_) (fun hz => ?_)
  · obtain ⟨⟨_, hqo⟩, hqt⟩ := M₂.bad.mp (beq_iff_eq.mp hz)
    rw [show shapeOk p c = true from hsh.mp ⟨hp.1, hp.2, hqo, hqt⟩]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hq : (c - 1) / 2 = c / 2 := by omega_arith
    rw [hc] at hq hqo ⊢
    exact tests_ok M₃.st rfl (by rw [hq]; exact hqo) M₃.u hL
  · refine reject_ok M₃.st hL M₃.u (Bool.eq_false_iff.mpr fun ht' => ?_)
    obtain ⟨a, b, d, e⟩ := hsh.mpr ht'
    have h0 : word t₂.mem p.B 200 = 0#64 := M₂.bad.mpr ⟨⟨⟨a, b⟩, d⟩, e⟩
    simp [h0] at hz

/-- `main`: p, its shape, and the tests. -/
theorem main_ok {R : RoundImpl} {p : PP} {T : Addr} {s : State} (h : St p s)
    (ht : TabIn p.B p.Z T s) (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (main R.name R.code) s (CEnd p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  rw [sieved_eq hL]
  generalize hc : Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take ((p.bits + 7) / 8))) = c
  have hc' : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) := hc.symm
  have hsh := sieved_shape_iff (x := Spec.Rsa.os2ip (p.r.take p.L)) hb1 hb2 h.dims.g
  rw [← hc'] at hsh
  unfold main
  refine WP.assoc (WP.seq (WP.mono_syms (mainA_ok h hU hL) fun t₂ ⟨st₂, ph₂, hU₂, hn₂, hr₂, f₂, rd₂⟩ sy₂ => ?_))
  rw [← hc'] at hn₂
  refine WP.seq (WP.mono (residue_mb st₂ ph₂ (ht.step sy₂ f₂ hr₂ rd₂) hU₂ hn₂) fun t₃ M₃ => ?_)
  refine WP.seq (WP.mono M₃.badLoad fun t₄ ⟨M₄, t5⟩ => ?_)
  refine WP.ite (word t₃.mem p.B 200 == 0) (by rw [eval_zero, t5]) (fun hz => ?_) (fun hz => ?_)
  · refine WP.seq (WP.mono (trialSieve_ok M₄) fun t₅ M₅ => ?_)
    refine WP.seq (WP.mono M₅.badLoad fun t₆ ⟨M₆, t6⟩ => ?_)
    refine WP.ite (word t₅.mem p.B 200 == 0) (by rw [eval_zero, t6]) (fun hz' => ?_) (fun hz' => ?_)
    · exact mainQ_ok hc' hL M₆ (M₅.bad.mp (beq_iff_eq.mp hz'))
    · refine reject_ok M₆.st hL M₆.u (Bool.eq_false_iff.mpr fun ht' => ?_)
      obtain ⟨a, b, -⟩ := hsh.mpr ht'
      have h0 : word t₅.mem p.B 200 = 0#64 := M₅.bad.mpr ⟨a, b⟩
      simp [h0] at hz'
  · refine reject_ok M₄.st hL M₄.u (Bool.eq_false_iff.mpr fun ht' => ?_)
    have h0 : word t₃.mem p.B 200 = 0#64 := M₃.bad.mpr (hsh.mpr ht').1
    simp [h0] at hz

theorem sieved_short {bits g : Nat} {r : List Byte} (h : r.length < (bits + 7) / 8) :
    Spec.Ffdh.sievedParameterCandidate bits g r = none := by
  have : (r.take ((bits + 7) / 8)).length ≠ (bits + 7) / 8 := by rw [List.length_take]; omega
  simp only [Spec.Ffdh.sievedParameterCandidate, Spec.RsaKeyGen.draw, this, ↓reduceIte, bind, Option.bind]

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
        word v.mem p.B 152 = BitVec.ofNat 64 p.L ∧ v.mem = t.mem ∧ v.rd = t.rd := by
  have hrl := h.dims.rl
  have hb2 := h.dims.b2
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (lenLoad_ok h) fun u ⟨⟨⟨a3, a4, am⟩, ka⟩, asp⟩ => ?_
  refine WP.mono (WP.rdwr (geFlag_ok a3 a4 hrl (by omega))) fun v ⟨⟨⟨a5, vm⟩, kv⟩, _, _, vsp⟩ => ?_
  have hm : v.mem = t.mem := vm.trans am
  exact ⟨eval_zero_ofNat v .t5 (by split <;> decide) a5,
    h.step (by rw [hm]; exact Frm.refl _ _ _) (ka.trans kv) (vsp.trans asp), by rw [hm]; exact hU, hm,
    (ka.trans kv).2.1⟩

/-- The length check, then `main` or the status 0. -/
theorem body_ok {R : RoundImpl} {p : PP} {T : Addr} {t : State} (h : St p t)
    (ht : TabIn p.B p.Z T t) (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.seq (.block (([ldh .t3 hRandLen, ldh .t4 hLen] : List Instr) ++ geFlag .t5 .t3 .t4))
      (.ite (.zero .t5) (.block (finish 0)) (main R.name R.code))) t
      (CEnd p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r)) := by
  refine WP.seq (WP.mono_syms (lenChk_ok h hU) fun v ⟨he, st, hUv, vm, vrd⟩ sy => ?_)
  refine WP.ite (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) he (fun hb => ?_) (fun hb => ?_)
  · have hs : p.r.length < p.L := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_left (by omega)] at hb; exact absurd hb (by decide)
    rw [sieved_short (by omega)]
    exact finEnd st (r := 0) (Or.inl rfl) rfl rfl rfl hUv
  · have hl : p.L ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega)])
    exact main_ok st (ht.step sy (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vrd) hUv hl

theorem preserved_cases : ∀ r ∈ preserved, ∃ i < 13, saved i = r := by decide

theorem a0_cases : ∀ i < 13, Reg.a0 ≠ saved i := by decide

theorem small_setWidth {k : Nat} (hk : k < 2 ^ 32) : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem status_le (res : Option (Option Nat × Spec.RsaKeyGen.Rand)) : Proof.Ffdh.candidateStatus res ≤ 2 := by
  rcases res with _ | ⟨_ | _, _⟩ <;> simp [Proof.Ffdh.candidateStatus]

/-- The front, and the table where the state names it. -/
theorem front_tab (s : State) (h : pcPre s) :
    WP isa (.seq (.block entry) zeroOut) s fun t => St (ppOf s) t ∧
      word t.mem (ppOf s).B 152 = BitVec.ofNat 64 (ppOf s).L ∧
      TabIn (ppOf s).B (ppOf s).Z (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) t := by
  have hpre := h
  obtain ⟨-, -, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htab⟩ := h
  refine WP.mono_syms (front_ok s hpre) fun t ⟨st, hU, fr, trd⟩ sy => ⟨st, hU, ?_⟩
  obtain ⟨tfit, tal, tat, tdO, tdS⟩ := htab
  refine ⟨by rw [sy], fun i hi => ?_, by rw [trd, hrd]; simp, tfit, tal, ?_⟩
  · rw [fr.readW (r := tabR s) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [Nat.mul_comm]; exact tdS
      · exact tdO) (by decide)]
    exact tat i hi
  · show (tabR s).Disjoint ⟨s.gpr .a7, 8 * (stackArg s 0).toNat⟩
    rw [Nat.mul_comm]; exact tdS

/-- `vg_ffdh_parameter_candidate_sieved`. -/
theorem code_correct {R : RoundImpl} (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (code R.name R.code) s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa (code R.name R.code) s fun t => abiPreserved s t ∧ pcPost s t
  have hpre := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, -⟩ := h
  have hLe : (s.gpr .a1).toNat = (ppOf s).L := hL
  have hlen : (ppOf s).r.length = (s.gpr .a6).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold code
  refine WP.assoc (WP.seq (WP.mono (front_tab s hpre) fun t ⟨st, hU, ht⟩ => ?_))
  refine WP.assoc (WP.seq (WP.mono (body_ok st ht hU) fun u hu => ?_))
  obtain ⟨E, u3, uo, uu⟩ := hu
  refine WP.mono (exit_ok E) fun w ⟨wr, wm, wsp, wo⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := preserved_cases r hr
    rw [wr i hi]; rfl
  · rw [wsp, E.sp]; rfl
  · rw [show Reg.ra = saved 12 from rfl, wr 12 (by decide)]; rfl
  · have hres : pcResult s = Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r := rfl
    simp only [pcPost]
    rw [hres, wm, wo .a0 (by decide) a0_cases, u3, hLe]
    refine ⟨small_setWidth (by have := status_le (Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r); omega),
      ?_, ?_⟩
    · refine uo.trans ?_
      generalize Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      refine congrArg (· :: []) (uu.trans ?_)
      rw [← hlen]
      generalize Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl

end VG.Proof.Ffdh.RISCV64.ParameterCandidate

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.Taint VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_nonzero eval_zero_ofNat eval_nonzero_ofNat)
open VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (RoundImpl A)
open VG.Proof.Ffdh.RISCV64.KeyGeneration (two_map two_ite)
open VG.Proof.MillerRabin.RISCV64.Search (RcD RC roundCall_ok roundCall_ct)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.Bignum.RISCV64.Precompute (loadN)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-! ## Relating two runs -/

theorem two_mono {α : Type} {Φ Φ' : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a s, Φ a s → Φ' a s) (hct : RelCT isa (Two Φ') c Q) : RelCT isa (Two Φ) c Q :=
  two_map id h hct

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

theorem round_ct {R : RoundImpl} :
    RelCT isa (Two fun d s => (DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
      decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) (VG.Impl.MillerRabin.RISCV64.Search.round R.name R.code) fun _ _ => True := by
  have hrc : ∀ d s, ((DMd d s ∧ decide (wA d.mb d.q.r d.u < 2) = false) ∧
      decide (¬ wA d.mb d.q.r d.u < d.N - 1) = false) → RC (rcOf d) s := by
    rintro d s ⟨⟨⟨sv, h, _⟩, h2⟩, hN⟩
    simp only [decide_eq_false_iff_not, Decidable.not_not] at h2 hN
    exact h.rc (by show wA d.mb d.q.r d.u < d.N; omega)
  unfold VG.Impl.MillerRabin.RISCV64.Search.round
  refine RelCT.seq (two_post (two_map rcOf hrc (roundCall_ct R)) (Ψ := DR) fun d s h => ?_) ?_
  · exact WP.mono (roundCall_ok R (hrc d s h).1 (hrc d s h).2.1 (hrc d s h).2.2.1 (hrc d s h).2.2.2.1 (hrc d s h).2.2.2.2.1 (hrc d s h).2.2.2.2.2) fun t ht => ⟨ht.a0, ht.prep.env.s6⟩
  refine two_ite' (fun d => decide ((if Proof.MillerRabin.Round.round d.N (wA d.mb d.q.r d.u) then 1 else 0) = 0))
    (fun d s h => eval_zero_ofNat s .a0 (by split <;> decide) h.1)
    (two_taint _ (pins_s6 (fun d : DrawD => d.q.B) fun _ _ h => h.1.2) (by taint_decide))
    (two_taint _ (pins_s6 (fun d : DrawD => d.q.B) fun _ _ h => h.1.2) (by taint_decide))

theorem drawBranch_ct {R : RoundImpl} :
    RelCT isa (Two DMd) (drawBranch R.name R.code) fun _ _ => True := by
  unfold drawBranch
  refine two_ite' (fun d => decide (wA d.mb d.q.r d.u < 2)) (fun d s ⟨sv, h, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z3]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) ?_
  refine two_ite' (fun d => decide (¬ wA d.mb d.q.r d.u < d.N - 1)) (fun d s ⟨⟨sv, h, _⟩, _⟩ => by
      rw [eval_zero, beq_zero_of_iff h.z4]; rfl)
    (two_taint _ (pins_nil _) (by taint_decide)) round_ct

/-- A draw leaks the same from the same public data. -/
theorem draw_ct {R : RoundImpl} : RelCT isa (Two DI) (draw R.name R.code) fun _ _ => True := by
  rw [draw_eq]
  exact RelCT.seq (RelCT.seq drawHead_ct drawLoad_ct)
    (RelCT.assoc (RelCT.assoc (RelCT.seq drawMid_ct drawBranch_ct)))

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

theorem mrBody_ct {R : RoundImpl} : RelCT isa (Two MI)
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
    refine two_post (two_map (fun a : MrD => (⟨a.q, a.mb, a.N, a.u, a.i, a.K⟩ : DrawD)) hd draw_ct) fun a s h => ?_
    obtain ⟨sv, M, hu, hroom, hI, hS, hi⟩ := hd a s h
    exact WP.mono (draw_ok M hu hroom hI hS hi) fun t ht => ht.1.st.s6

/-- Before the witness loop. -/
def MI0 (a : MrD) (s : State) : Prop :=
  (∃ sv, MSt (a.q.with sv) a.mb a.N a.K s ∧ word s.mem a.q.B 152 = BitVec.ofNat 64 a.u) ∧
    a.u ≤ a.q.r.length ∧ a.i = 0 ∧ a.res = checkWitnesses a.N a.K (a.q.r.drop a.u) ∧
    Spec.RsaKeyGen.bitLength (a.N - 1) = a.mb

theorem pins_MI0 : Pins MI0 [.a7, .s5, .t0, .s6] :=
  pins_ph MrD.q MrD.mb fun _ _ ⟨⟨sv, M, _⟩, _⟩ => ⟨sv, _, M.st, M.ph⟩

/-- The witness loop leaks the same in runs testing the same modulus from the
same tape. -/
theorem millerRabin_ct {R : RoundImpl} :
    RelCT isa (Two MI0) (millerRabin R.name R.code) (Two ME) := by
  unfold millerRabin
  refine RelCT.seq (two_post (two_taint _ pins_MI0 (by taint_decide)) (Ψ := MI) fun a s h => ?_)
    (two_loopD (fun a => a.q.r.length + 1 - a.u) mrNext (fun a => mrGo a.q.r a.mb a.N a.i a.u a.K) mrBody_ct
      fun a s h => ?_)
  · obtain ⟨⟨sv, M, hu⟩, hul, hi, hres, hbl⟩ := h
    refine WP.mono (mrInit_ok M hu hul) fun t ht => ⟨⟨sv, ?_⟩, hbl⟩
    rw [hi, hres]; exact ht
  · obtain ⟨⟨sv, hs⟩, hbl⟩ := h
    have hm1 := hs.m.mb1
    refine WP.mono (mrIter_ok hbl hs) fun t ⟨he, hend, hgo⟩ =>
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

theorem testCore_ct {R : RoundImpl} :
    RelCT isa (Two TC) (.seq montPrep (millerRabin R.name R.code)) (Two ME) :=
  RelCT.seq (two_post (two_taint _ pins_TC (by taint_decide)) (Ψ := fun d => MI0 (mrOf d)) fun _ _ ⟨sv, h⟩ =>
      WP.mono (montPrep_mst h.st h.ph h.mb1 h.mb2 h.n h.odd h.n3) fun _ ⟨M, _, h152⟩ =>
        ⟨⟨sv, M, h152.trans h.used⟩, h.ul, rfl, rfl, h.bl⟩)
    (two_map mrOf (fun _ _ h => h) millerRabin_ct)

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
theorem testQ_ct {R : RoundImpl} :
    RelCT isa (Two TQ) (test true (.block []) R.name R.code) (Two ME) := by
  unfold test
  simp only [↓reduceIte]
  refine RelCT.assoc (RelCT.seq (two_post ?_
    (Ψ := fun d => TC ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, d.u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩)
    fun _ _ ⟨sv, h, hc, hq, hqo, hu, hul⟩ => WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht => ⟨sv, ht⟩)
    (RelCT.seq (two_post (two_map _ (fun _ _ h => h) (two_taint _ pins_TC (by taint_decide)))
      (Ψ := fun d => TC ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, d.u, Spec.Ffdh.primeChecks (d.q.bits - 1)⟩)
      fun _ _ h => WP.block_nil_iff.mpr h)
    (two_map _ (fun _ _ h => h) testCore_ct)))
  exact two_map TQD.q (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩)
    (RelCT.seq (phasePA_ct true) (two_taint _ (pins_PA true) (by taint_decide)))

/-- Before p's test. -/
def TP (d : TQD) (s : State) : Prop :=
  ∃ sv, St (d.q.with sv) s ∧ d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧
    word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧ d.u ≤ d.q.r.length ∧ d.q.L ≤ d.q.r.length

/-- p's test, with `adjust` setting its count of witnesses to `Kf` of the
default, leaks the same from the same candidate and tape. -/
theorem testP_ct {R : RoundImpl} {adjust : Prog isa} (Kf : Nat → Nat)
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
    (two_map _ (fun _ _ h => h) testCore_ct)))
  exact two_map TQD.q (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct)

/-- p's test of its first witness. -/
theorem testP1_ct {R : RoundImpl} :
    RelCT isa (Two TP) (test false firstCheck R.name R.code) (Two ME) :=
  testP_ct (fun _ => 1) (fun h => firstCheck_ok h) (two_taint _ pins_TC (by taint_decide))

/-- p's test of its other witnesses. -/
theorem testPR_ct {R : RoundImpl} :
    RelCT isa (Two TP) (test false restChecks R.name R.code) (Two ME) :=
  testP_ct (· - 1) (fun h => restChecks_ok h (by unfold Spec.Ffdh.primeChecks; split <;> decide))
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
theorem testRest_ct {R : RoundImpl} :
    RelCT isa (Two fun d t => TE E2 d t ∧ statOf (E2 d).res = 1) (testRest R.name R.code) fun _ _ => True := by
  unfold testRest
  have hp : ∀ d t, TE E2 d t ∧ statOf (E2 d).res = 1 → TP (d3 d) t := fun d t ⟨⟨hE, hc, hL, _⟩, h1⟩ => by
    obtain ⟨sv, M, hU, hu⟩ := hE.passed h1
    exact ⟨sv, M.st, hc, hU, hu, hL⟩
  refine RelCT.seq (two_post ((two_map d3 hp testPR_ct).mono (fun _ _ h => h) fun _ _ _ => trivial)
    (Ψ := fun d => ME (E3 d)) fun d _ h => ?_) (two_map E3 (fun _ _ h => h) pResult_ct)
  obtain ⟨sv, st, hc, hU, hu, hL⟩ := hp d _ h
  exact WP.mono (testPR_ok st hc hU hu hL) fun _ ht => ⟨sv, ht⟩

/-- q, from p, its test and the rest leak the same. -/
theorem testQ_cts {R : RoundImpl} :
    RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) (testQ R.name R.code) fun _ _ => True := by
  unfold testQ
  have hh : RelCT isa (Two fun d t => TE E1 d t ∧ statOf (E1 d).res = 1) halveQ
      (Two fun d t => TQ (d2 d) t ∧ FX d) :=
    two_post (two_taint _ (pins_TE E1 fun _ _ h => h.1) (by taint_decide)) fun d _ ⟨⟨hE, hx⟩, h1⟩ => by
      obtain ⟨sv, M, hU, hu⟩ := hE.passed h1
      exact WP.mono (halveQ_from M hx.1 hU) fun _ ⟨st, hq, hU'⟩ => ⟨⟨sv, st, hx.1, hq, hx.2.2, hU', hu⟩, hx⟩
  have hq : RelCT isa (Two fun d t => TQ (d2 d) t ∧ FX d) (test true (.block []) R.name R.code) (Two (TE E2)) :=
    two_post ((two_map d2 (fun _ _ h => h.1) testQ_ct).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, h, hc, hq, hqo, hu, hul⟩, hx⟩ =>
        WP.mono (testQ_ok h hc hq hqo hu hul) fun _ ht => ⟨⟨sv, ht⟩, hx⟩
  exact RelCT.seq hh (RelCT.seq hq (stage_ct E2 testRest_ct))

/-- The tests leak the same from the same candidate and tape. -/
theorem tests_ct {R : RoundImpl} : RelCT isa (Two TS) (tests R.name R.code) fun _ _ => True := by
  unfold tests
  have h1 : RelCT isa (Two TS) (test false firstCheck R.name R.code) (Two (TE E1)) :=
    two_post ((two_mono (fun _ _ h => h.1) testP1_ct).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun _ _ ⟨⟨sv, h, hc, hu, hul, hL⟩, hqo⟩ =>
        WP.mono (testP1_ok h hc hu hul hL) fun _ ht => ⟨⟨sv, ht⟩, hc, hL, hqo⟩
  exact RelCT.seq h1 (stage_ct E1 testQ_cts)

end VG.Proof.Ffdh.RISCV64.ParameterCandidate

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64 VG.RISCV64.Taint VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_zero_ofNat)
open VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.Ffdh.RISCV64.KeyGeneration (two_map two_ite)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-! ## `main` -/

/-- The candidate from the tape. -/
def candOf (q : PP) : Nat := Spec.Ffdh.candidateOf q.bits (Spec.Rsa.os2ip (q.r.take q.L))

/-- Code the taint analysis with the table's address public proves constant
time, from states a predicate relates. -/
theorem two_taint_sym {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ →
      s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s₂.syms VG.Impl.RsaKeyGen.TrialTable32.symbol)
    {hc : VG.Taint.Hint T}
    (h : (VG.Taint.check (taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) (fun _ _ ⟨a, h₁, h₂, hsp⟩ =>
    ⟨⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (mem_ofRegs.mp hr)⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂⟩) h

/-- Before `main`: the arguments and tape, and the table's address. -/
def MnI (a : PP × Addr) (s : State) : Prop :=
  ∃ sv, St (a.1.with sv) s ∧ TabIn a.1.B a.1.Z a.2 s ∧ word s.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    a.1.L ≤ a.1.r.length

/-- With p in array 0. -/
def MnA (a : PP × Addr) (t : State) : Prop :=
  (∃ sv, St (a.1.with sv) t ∧ TabIn a.1.B a.1.Z a.2 t ∧ Ph (a.1.with sv) a.1.bits
    (Spec.Ffdh.primeChecks a.1.bits) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    wv t.mem a.1.B (slot (wOf a.1.bits) 0) (wOf a.1.bits) = candOf a.1) ∧ a.1.L ≤ a.1.r.length

/-- In p's working space, `hBad` zero iff `B q`. -/
def MnB (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (t : State) : Prop :=
  (∃ sv, MB (a.1.with sv) a.2 (x a.1) (B a.1) t) ∧ a.1.L ≤ a.1.r.length

theorem pins_MnB {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : Pins Φ [.a7, .s5, .t0, .s6] :=
  pins_ph Prod.fst (fun a => a.1.bits) fun a s hs => let ⟨⟨sv, M⟩, _⟩ := h a s hs; ⟨sv, _, M.st, M.ph⟩

theorem mainA_ct : RelCT isa (Two MnI) (.seq (phase false) shapeP) (Two MnA) :=
  two_post (two_map Prod.fst (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct))
    fun _ _ ⟨sv, h, ht, hU, hL⟩ => WP.mono_syms (mainA_ok h hU hL) fun _ ⟨a, b, c, d, hr, f, rd⟩ sy =>
      ⟨⟨sv, a, ht.step sy f hr rd, b, c, d⟩, hL⟩

/-- After the congruence's first block. -/
def RH (a : PP × Addr) (t : State) : Prop :=
  (t.gpr .t3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2 ∧ (a.1.g = 2 ∨ a.1.g = 5)) ∧
    t.gpr .a7 = off a.1.B (slot (wOf a.1.bits) 0) ∧ t.gpr .t0 = BitVec.ofNat 64 (wOf a.1.bits) ∧ t.gpr .s6 = a.1.B

theorem pins_RH {Φ : PP × Addr → State → Prop} (h : ∀ a s, Φ a s → RH a s) : Pins Φ [.a7, .t0, .s6] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, a7, a0, a6⟩ := h a s₁ h₁
  obtain ⟨_, b7, b0, b6⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a7, b7]
  · rw [a0, b0]
  · rw [a6, b6]

theorem pins_MnA : Pins MnA [.s6] := pins_s6 (fun a : PP × Addr => a.1.B) fun _ _ ⟨⟨_, h, _⟩, _⟩ => h.s6

theorem residue_ct : RelCT isa (Two MnA) residue (Two (MnB candOf fun q => goodRes q.g (candOf q))) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, h, ht, hp, hU, hn⟩, hL⟩ =>
    WP.mono (residue_mb h hp ht hU hn) fun _ M => ⟨⟨sv, M⟩, hL⟩
  unfold residue
  refine RelCT.seq (two_post (two_taint _ pins_MnA (by taint_decide)) (Ψ := RH)
    fun a s ⟨⟨sv, h, _, hp, _⟩, _⟩ => ?_) (two_ite' (fun a => decide (a.1.g = 2)) (fun a s h => ?_)
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide))
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide)))
  · refine WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2) ?_
      (by rfl) (by rfl)) fun t ⟨t3, k⟩ => ⟨⟨t3, h.dims.g⟩, (k.gpr (by decide)).trans hp.a7,
        (k.gpr (by decide)).trans hp.t0, (k.gpr (by decide)).trans h.s6⟩
    simp only [ldh, hGen]
    brun [h.s6, h.ld (d := 128) (by decide), h.al (d := 128) (by decide) (by decide), h.args.gen']
    rfl
  · obtain ⟨⟨h3, hg⟩, _⟩ := h
    rw [eval_zero, h3]
    rcases hg with hg | hg <;> rw [hg] <;> decide

theorem badLoad_ct {x : PP → Nat} {B : PP → Prop} [∀ q, Decidable (B q)] :
    RelCT isa (Two (MnB x B)) (.block [ldh .t3 hBad])
      (Two fun a t => MnB x B a t ∧ isa.eval (.zero .t3) t = some (decide (B a.1))) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, M⟩, hL⟩ =>
    WP.mono M.badLoad fun _ ⟨M', t5⟩ => ⟨⟨⟨sv, M'⟩, hL⟩,
      (by rw [eval_zero, t5]; exact congrArg some (beq_zero_of_iff M.bad))⟩

theorem finMnB_ct {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : RelCT isa (Two Φ) (.block (finish 2)) fun _ _ => True :=
  two_map Prod.fst (fun a s hs => let ⟨⟨_, M⟩, _⟩ := h a s hs; M.st.fs) (finish_ct (.inr (.inr rfl)))

theorem halve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) halveQ (Two (MnB (fun q => x q / 2) fun q => B q ∧ x q / 2 % 2 = 1)) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, M⟩, hL⟩ =>
    WP.mono M.halve fun _ M' => ⟨⟨sv, M'⟩, hL⟩

/-! ## Trial division -/

/-- With the count of entries in `hTrialN`. -/
def MnC (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (u : State) : Prop :=
  MnB x B a u ∧ u.mem.readW (a.1.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (trialN a.1.bits)

/-- With the table's address and the count in `s9` and `s10`. -/
def MnT (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (v : State) : Prop :=
  ∃ u, MnC x B a u ∧ ((v.gpr .s9 = a.2 ∧ v.gpr .s10 = BitVec.ofNat 64 (trialN a.1.bits) ∧ v.mem = u.mem) ∧
    Keep [.s9, .s10] u v) ∧ v.sp = u.sp

/-- In the loop, `d.2` entries left. -/
def MnL (x : PP → Nat) (B : PP → Prop) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnT x B d.1 v ∧ VG.Proof.RsaKeyGen.RISCV64.Trial.TInv v d.1.2 (x d.1.1) (trialN d.1.1.bits) d.2 w

/-- After the loop. -/
def MnE (x : PP → Nat) (B : PP → Prop) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnT x B d.1 v ∧ Keep VG.Proof.RsaKeyGen.RISCV64.Trial.entryRegs v w

theorem MnT.base {x : PP → Nat} {B : PP → Prop} {a : PP × Addr} {v : State} (h : MnT x B a v) :
    v.gpr .a7 = off a.1.B (slot (wOf a.1.bits) 0) ∧ v.gpr .t0 = BitVec.ofNat 64 (wOf a.1.bits) ∧
      v.gpr .s6 = a.1.B := by
  obtain ⟨u, ⟨⟨⟨_, M⟩, _⟩, _⟩, ⟨-, kv⟩, -⟩ := h
  exact ⟨(kv.gpr (by decide)).trans M.ph.a7, (kv.gpr (by decide)).trans M.ph.t0,
    (kv.gpr (by decide)).trans M.st.s6⟩

theorem pins_MnL {x : PP → Nat} {B : PP → Prop} : Pins (MnL x B) [.a7, .t0, .s9] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, k₁, hm₁, hk₁, ⟨a9, -⟩, kv₁⟩ ⟨v₂, hv₂, k₂, hm₂, hk₂, ⟨b9, -⟩, kv₂⟩ r hr
  obtain ⟨a7, a0, -⟩ := hv₁.base
  obtain ⟨b7, b0, -⟩ := hv₂.base
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [kv₁.gpr (by decide), kv₂.gpr (by decide), a7, b7]
  · rw [kv₁.gpr (by decide), kv₂.gpr (by decide), a0, b0]
  · rw [a9, b9, show k₁ = k₂ by omega]

theorem pins_MnE {x : PP → Nat} {B : PP → Prop} : Pins (MnE x B) [.s6] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, kv₁⟩ ⟨v₂, hv₂, kv₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [kv₁.gpr (by decide), kv₂.gpr (by decide), hv₁.base.2.2, hv₂.base.2.2]

theorem MnT.init {x : PP → Nat} {B : PP → Prop} {a : PP × Addr} {v : State} (h : MnT x B a v) :
    MnL x B (a, trialN a.1.bits) v := by
  obtain ⟨u, -, ⟨⟨v9, v10, -⟩, -⟩, -⟩ := id h
  have hN : 1 ≤ trialN a.1.bits := by unfold trialN; split <;> decide
  refine ⟨v, h, 0, ?_, ?_, ?_⟩
  · dsimp only; omega
  · dsimp only; omega
  exact ⟨⟨by rw [v9, Nat.mul_zero, BitVec.add_zero], by rw [v10, Nat.sub_zero], rfl, rfl⟩, Keep.refl _ _⟩

/-- The go-on condition of the loop, `d.2` entries left. -/
def trialGo (x : PP → Nat) (d : (PP × Addr) × Nat) : Bool :=
  decide (x d.1.1 % VG.Impl.RsaKeyGen.tabEntry (trialN d.1.1.bits - d.2) ≠ 0 ∧
    trialN d.1.1.bits - d.2 + 1 ≠ trialN d.1.1.bits)

theorem MnL.step {x : PP → Nat} {B : PP → Prop} {d : (PP × Addr) × Nat} {w : State} (h : MnL x B d w) :
    WP isa VG.Impl.RsaKeyGen.RISCV64.Trial.entry w fun t =>
      isa.eval (.nonzero .s10) t = some (trialGo x d) ∧ (trialGo x d = false → MnE x B d t) ∧
        (trialGo x d = true → d.2 - 1 < d.2 ∧ MnL x B (d.1, d.2 - 1) t) := by
  obtain ⟨v, hv, hI⟩ := h
  obtain ⟨u, ⟨⟨⟨sv, M⟩, _⟩, _⟩, ⟨⟨_, _, vm⟩, kv⟩, _⟩ := id hv
  obtain ⟨vs, v7, v0, vc, w1, w2, hZ, ho, _, n2, htab⟩ := M.loopArgs vm kv
  refine WP.mono (VG.Proof.RsaKeyGen.RISCV64.Trial.step_ok vs v7 v0 vc w1 w2 hZ ho n2 htab hI)
    fun t ⟨e, f, g⟩ => ⟨e, fun hg => ⟨v, hv, (f (by rw [e, ← hg]; rfl)).2⟩, fun hg => ?_⟩
  obtain ⟨hm, hI'⟩ := g (by rw [e, ← hg]; rfl)
  exact ⟨by omega, v, hv, hI'⟩

theorem trialLoop_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnT x B)) VG.Impl.RsaKeyGen.RISCV64.Trial.loop (Two (MnE x B)) :=
  two_map (fun a => (a, trialN a.1.bits)) (fun _ _ h => h.init)
    (two_loopD (Φ := MnL x B) (Ψ := MnE x B) Prod.snd (fun d => (d.1, d.2 - 1)) (trialGo x)
      (two_taint _ pins_MnL (by taint_decide)) fun _ _ h => h.step)

/-- Trial division leaks the same from the same candidate and table. -/
theorem trialSieve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) trialSieve
      (Two (MnB x fun q => B q ∧ VG.Proof.RsaKeyGen.trialPrefix (x q) (trialN q.bits) = false)) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, M⟩, hL⟩ => WP.mono (trialSieve_ok M) fun _ M' => ⟨⟨sv, M'⟩, hL⟩
  unfold trialSieve VG.Impl.RsaKeyGen.RISCV64.Trial.trial
  refine RelCT.seq (two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) (Ψ := MnC x B)
    fun _ _ ⟨⟨sv, M⟩, hL⟩ => WP.mono M.count fun _ ⟨M', h208⟩ => ⟨⟨⟨sv, M'⟩, hL⟩, h208⟩) ?_
  refine RelCT.seq (RelCT.seq (two_post (two_taint_sym _ (pins_MnB fun _ _ h => h.1)
      (fun _ _ _ ⟨⟨⟨_, M₁⟩, _⟩, _⟩ ⟨⟨⟨_, M₂⟩, _⟩, _⟩ => M₁.tab.sym.trans M₂.tab.sym.symm) (by taint_decide))
    (Ψ := MnT x B) fun _ u hu => ?_) trialLoop_ct) (two_taint _ pins_MnE (by taint_decide))
  obtain ⟨⟨⟨sv, M⟩, hL⟩, h208⟩ := hu
  exact WP.mono (M.trialA h208) fun v hv => ⟨u, ⟨⟨⟨sv, M⟩, hL⟩, h208⟩, hv⟩

/-! ## The shape checks and the tests -/

/-- p's shape checks. -/
def okP (q : PP) : Prop :=
  goodRes q.g (candOf q) ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q) (trialN q.bits) = false

instance (q : PP) : Decidable (okP q) := by unfold okP; infer_instance

/-- p's shape checks, then q's. -/
def allOk (q : PP) : Prop :=
  (okP q ∧ candOf q / 2 % 2 = 1) ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q / 2) (trialN q.bits) = false

instance (q : PP) : Decidable (allOk q) := by unfold allOk; infer_instance

theorem ts_of {a : PP × Addr} {s : State} (h : MnB (fun q => candOf q / 2) allOk a s) (ha : allOk a.1) :
    TS ⟨a.1, candOf a.1, a.1.L⟩ s := by
  obtain ⟨⟨sv, M⟩, hL⟩ := h
  have hb1 : 512 ≤ a.1.bits := M.st.dims.b1
  obtain ⟨ho, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := a.1.bits) (by omega)
    (Spec.Rsa.os2ip (a.1.r.take a.1.L))
  have hq : (candOf a.1 - 1) / 2 = candOf a.1 / 2 := by unfold candOf; omega
  exact ⟨⟨sv, M.st, rfl, M.u, hL, hL⟩, by rw [hq]; exact ha.1.2⟩

/-- `main` leaks the same from the same arguments, tape and table. -/
theorem main_ct {R : RoundImpl} : RelCT isa (Two MnI) (main R.name R.code) fun _ _ => True := by
  unfold main
  refine RelCT.assoc (RelCT.seq mainA_ct (RelCT.seq residue_ct (RelCT.seq badLoad_ct
    (two_ite' (fun a => decide (goodRes a.1.g (candOf a.1))) (fun _ _ h => h.2) ?_
      (finMnB_ct fun _ _ h => h.1.1)))))
  refine RelCT.seq (two_mono (fun _ _ h => h.1.1) trialSieve_ct) (RelCT.seq (badLoad_ct (B := okP))
    (two_ite' (fun a => decide (okP a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1)))
  refine RelCT.seq (two_mono (fun _ _ h => h.1.1) halve_ct) (RelCT.seq trialSieve_ct
    (RelCT.seq (badLoad_ct (B := allOk)) (two_ite' (fun a => decide (allOk a.1)) (fun _ _ h => h.2) ?_
      (finMnB_ct fun _ _ h => h.1.1))))
  exact two_map (fun a => (⟨a.1, candOf a.1, a.1.L⟩ : TQD))
    (fun _ _ ⟨⟨h, _⟩, ha⟩ => ts_of h (of_decide_eq_true ha)) tests_ct

/-! ## The candidate -/

/-- A run's public data: its arguments and tape, without the registers it
saves. -/
def qOf (s : State) : PP := (ppOf s).with fun _ => 0

/-- On entry. -/
def CI (q : PP) (s : State) : Prop := pcPre s ∧ qOf s = q

/-- `scratch_len` from the stack. -/
theorem entryL_ok {s : State} (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (hal : s.sp.toNat % 8 = 0) :
    WP isa (.block [.addSp .t3 0, .load .d .t3 .t3 0]) s fun t => t.gpr .t3 = stackArg s 0 ∧ Keep [.t3] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [stackArgAddr, stackArg, Nat.mul_zero, BitVec.add_zero] at hargs ⊢
  brun [exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, add_ofNat_zero, hargs, hal]

/-- The entry: the header's `out` and `out_len`. -/
theorem entry_ok (s : State) (h : pcPre s) :
    WP isa (.block entry) s fun t => Scr t (s.gpr .a7) (8 * (stackArg s 0).toNat) ∧ t.gpr .s6 = s.gpr .a7 ∧
      word t.mem (s.gpr .a7) 16 = s.gpr .a0 ∧ word t.mem (s.gpr .a7) 24 = s.gpr .a1 := by
  obtain ⟨hsp, hsp16, hspT, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nwS, -, alS, hb1, hb2, hL, hg,
    hsw⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  have hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat64 _).symm
  have h80 : 104 ≤ 8 * (stackArg s 0).toNat := by omega
  have hscr : Scr s (s.gpr .a7) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega) alS
  have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryA_ok rfl hn hargs (by omega) h80) fun tA ⟨⟨a4, _, _⟩, ka⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a4 h80 (by omega) (fun i hi => by
    rw [ka.2.2]; exact hscr.st (by omega)) fun i hi => hscr.al8 (by omega) (by omega)) fun tS hS => ?_
  have hS7 : tS.gpr .a7 = s.gpr .a7 := by rw [hS.gpr, ka.gpr (by decide)]
  refine WP.mono (header_ok (s := tS) hS7 (fun d hd => by
    rw [hS.wr, ka.2.2]; exact hscr.st (d := d) (by omega)) fun d hd h8 => hscr.al8 (by omega) h8)
    fun t₁ ⟨⟨c6, _, cm⟩, kc⟩ => ?_
  have gS : ∀ r, r ∉ ([.t3, .t4] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr hr
  obtain ⟨-, w16, w24, -⟩ := hdrW_words tS.mem (s.gpr .a7) (tS.gpr .t3)
    (tS.gpr .a0) (tS.gpr .a1) (tS.gpr .a2) (tS.gpr .a3) ((tS.gpr .a4 <<< 32) >>> 32) (tS.gpr .a5) (tS.gpr .a6)
  rw [← cm] at w16 w24
  have hwr₁ : t₁.wr = s.wr := by rw [kc.2.2, hS.wr, ka.2.2]
  exact ⟨hscr.congr hwr₁, c6, w16.trans (gS _ (by decide)), w24.trans (gS _ (by decide))⟩

/-- After `scratch_len`'s load. -/
def EL (q : PP) (t : State) : Prop := t.gpr .a7 = q.B ∧ t.gpr .t3 = BitVec.ofNat 64 q.n

theorem pins_EL : Pins EL [.a7, .t3] := by
  rintro q s₁ s₂ ⟨a7, a3⟩ ⟨b7, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a7, b7]
  · rw [a3, b3]

/-- After the entry. -/
def Z0 (q : PP) (t : State) : Prop :=
  ∃ Z, Scr t q.B Z ∧ 32 ≤ Z ∧ t.gpr .s6 = q.B ∧ t.mem.readW (q.B + BitVec.ofNat 64 16) 64 = q.op ∧
    t.mem.readW (q.B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 q.L

theorem entry_ct : RelCT isa (Two CI) (.block entry) (Two Z0) := by
  refine two_post ?_ fun q s ⟨h, hq⟩ => ?_
  · rw [show entry = [.addSp .t3 0, .load .d .t3 .t3 0] ++ entry.drop 2 from rfl]
    refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_nil _) (by taint_decide)) (Ψ := EL)
      fun q s ⟨h, hq⟩ => ?_) (two_taint _ pins_EL (by taint_decide)))
    subst hq
    have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
      ⟨⟨stackArgAddr s 0, 8⟩, by rw [h.2.2.2.1]; simp, by simp [Region.Contains]⟩
    exact WP.mono (entryL_ok hargs (by have := h.2.1; omega)) fun t ⟨t3, k⟩ =>
      ⟨k.gpr (by decide), t3.trans (ofNat_toNat64 _).symm⟩
  · subst hq
    have h' := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb1, -, hL, -, hsw⟩ := h'
    have hL' : (s.gpr .a1).toNat = (qOf s).L := hL
    simp only [Spec.Rsa.scratchWords] at hsw
    refine WP.mono (entry_ok s h) fun t ⟨hs, h6, w16, w24⟩ => ⟨_, hs, by omega, h6, w16, ?_⟩
    rw [← hL']; exact w24.trans (ofNat_toNat64 _).symm

/-- With `out` and `out_len` loaded. -/
def Z1 (q : PP) (t : State) : Prop := t.gpr .t3 = q.op ∧ t.gpr .t4 = BitVec.ofNat 64 q.L

theorem pins_Z1 : Pins Z1 [.t3, .t4] := by
  rintro q s₁ s₂ ⟨a3, a4⟩ ⟨b3, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a4, b4]

theorem zeroOut_ct : RelCT isa (Two Z0) zeroOut fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_post (two_taint _ (pins_s6 PP.B fun _ _ ⟨_, _, _, h6, _⟩ => h6) (by taint_decide))
    (Ψ := Z1) fun q s ⟨Z, hs, hZ, h6, hO, hL⟩ => ?_) (two_taint _ pins_Z1 (by taint_decide))
  exact WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun s₂ => s₂.gpr .t3 = q.op ∧ s₂.gpr .t4 = BitVec.ofNat 64 q.L)
    (by simp only [ldh, hOut, hLen]
        brun [h6, hO, hL, hs.ld (d := 16) (n := 8) (by omega), hs.ld (d := 24) (n := 8) (by omega),
          hs.al8 (d := 16) (by omega) (by decide), hs.al8 (d := 24) (by omega) (by decide),
          exec_li (show imm12 0 by decide)])
    (by rfl) (by rfl)) fun _ ⟨h, _⟩ => h

/-- On entry, with the table's address. -/
def CIT (a : PP × Addr) (s : State) : Prop := CI a.1 s ∧ s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = a.2

/-- After the front. -/
def BI (a : PP × Addr) (t : State) : Prop :=
  ∃ sv, St (a.1.with sv) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧ TabIn a.1.B a.1.Z a.2 t

theorem front_ct : RelCT isa (Two CIT) (.seq (.block entry) zeroOut) (Two BI) :=
  two_post (two_map Prod.fst (fun _ _ h => h.1) (RelCT.seq entry_ct zeroOut_ct)) fun a s ⟨⟨h, hq⟩, hy⟩ => by
    obtain ⟨q, T⟩ := a
    dsimp only at hq hy
    subst hq hy
    exact WP.mono (front_tab s h) fun _ ⟨st, hU, ht⟩ => ⟨_, st, hU, ht⟩

/-- With the tape's length and `out_len` loaded. -/
def L34 (q : PP) (t : State) : Prop :=
  t.gpr .t3 = BitVec.ofNat 64 q.r.length ∧ t.gpr .t4 = BitVec.ofNat 64 q.L

theorem pins_L34 : Pins L34 [.t3, .t4] := by
  rintro q s₁ s₂ ⟨a3, a4⟩ ⟨b3, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a4, b4]

/-- After the length check. -/
def LC (a : PP × Addr) (t : State) : Prop :=
  isa.eval (.zero .t5) t = some (decide ((if a.1.L ≤ a.1.r.length then 1 else 0) = 0)) ∧
    ∃ sv, St (a.1.with sv) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧ TabIn a.1.B a.1.Z a.2 t

theorem lenChk_ct :
    RelCT isa (Two BI) (.block (([ldh .t3 hRandLen, ldh .t4 hLen] : List Instr) ++ geFlag .t5 .t3 .t4)) (Two LC) :=
  two_post (two_map (Φ' := fun q t => ∃ sv, St (q.with sv) t) Prod.fst (fun _ _ ⟨sv, h, _⟩ => ⟨sv, h⟩)
      (RelCT.block_append (RelCT.seq (two_post
      (two_taint _ (pins_s6 PP.B fun _ _ ⟨_, h⟩ => h.s6) (by taint_decide)) (Ψ := L34)
      fun _ _ ⟨_, h⟩ => WP.mono (lenLoad_ok h) fun _ ⟨⟨⟨a3, a4, _⟩, _⟩, _⟩ => ⟨a3, a4⟩)
      (two_taint _ pins_L34 (by taint_decide)))))
    fun _ _ ⟨sv, h, hU, ht⟩ => WP.mono_syms (lenChk_ok h hU) fun _ ⟨he, st, hU', vm, vrd⟩ sy =>
      ⟨he, sv, st, hU', ht.step sy (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vrd⟩

/-- Before the exit. -/
def XE (q : PP) (t : State) : Prop := ∃ sv, ESt (q.with sv) t

theorem body_ct {R : RoundImpl} : RelCT isa (Two BI)
    (.seq (.block (([ldh .t3 hRandLen, ldh .t4 hLen] : List Instr) ++ geFlag .t5 .t3 .t4))
      (.ite (.zero .t5) (.block (finish 0)) (main R.name R.code))) (Two fun (a : PP × Addr) => XE a.1) := by
  refine two_post (RelCT.seq lenChk_ct (two_ite'
    (fun a : PP × Addr => decide ((if a.1.L ≤ a.1.r.length then 1 else 0) = 0))
    (fun _ _ h => h.1) ?_ ?_)) fun _ _ ⟨sv, h, hU, ht⟩ => WP.mono (body_ok h ht hU) fun _ ht => ⟨sv, ht.1⟩
  · exact two_map Prod.fst (fun _ _ ⟨⟨_, _, h, _⟩, _⟩ => h.fs) (finish_ct (.inl rfl))
  · refine two_mono (fun q _ ⟨⟨_, sv, h, hU, ht⟩, hb⟩ => ⟨sv, h, ht, hU, ?_⟩) main_ct
    by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega)])

/-- With the save area's word count loaded. -/
def X1 (q : PP) (t : State) : Prop := t.gpr .t3 = BitVec.ofNat 64 q.n ∧ t.gpr .s6 = q.B

theorem pins_X1 : Pins X1 [.t3, .s6] := by
  rintro q s₁ s₂ ⟨a3, a6⟩ ⟨b3, b6⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a6, b6]

theorem exit_ct : RelCT isa (Two XE) (.block exit) fun _ _ => True := by
  rw [show exit = [ldh .t3 hWsLen] ++ exit.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_s6 PP.B fun _ _ ⟨_, h⟩ => h.s6)
    (by taint_decide)) (Ψ := X1) fun q t ⟨sv, h⟩ => ?_) (two_taint _ pins_X1 (by taint_decide)))
  have hdn := h.dims.n
  have hZe : (q.with sv).Z = 8 * (q.with sv).n := rfl
  have l0 : InRegions (t.rd ++ t.wr) (q.B + BitVec.ofNat 64 0) 8 := h.scr.ld (d := 0) (by omega)
  have a0 : (q.B + BitVec.ofNat 64 0).toNat % 8 = 0 := h.scr.al8 (d := 0) (by omega) (by decide)
  exact WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 (q.with sv).n)
    (by simp only [ldh, hWsLen]; brun [show t.gpr .s6 = q.B from h.s6, l0, a0, show t.mem.readW (q.B + BitVec.ofNat 64 0) 64 =
      BitVec.ofNat 64 (q.with sv).n from h.len]) (by rfl) (by rfl)) fun _ ⟨u3, k⟩ =>
    ⟨u3, (k.gpr (by decide)).trans h.s6⟩

/-- `vg_ffdh_parameter_candidate_sieved` leaks the same from the same public
arguments and tape. -/
theorem code_rel {R : RoundImpl} : RelCT isa (Two CIT) (code R.name R.code) fun _ _ => True := by
  unfold code
  exact RelCT.assoc (RelCT.seq front_ct (RelCT.assoc (RelCT.seq body_ct (two_map Prod.fst (fun _ _ h => h)
    exit_ct))))

theorem qOf_pub {s t : State} (h : pcPub s t) : qOf s = qOf t := by
  obtain ⟨hsp, hr, h0, -, h2, h3, h4, h5, -, h7, hst, -⟩ := h
  have hr' : pcRand s = pcRand t :=
    (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hr
  simp only [qOf, PP.with, ppOf, hsp, h0, h2, h3, h4, h5, h7, hst, hr']

/-- `vg_ffdh_parameter_candidate_sieved` in constant time. -/
theorem code_ct {R : RoundImpl} :
    ConstantTime isa pcContract.pre pcContract.pub (code R.name R.code) :=
  RelCT.constantTime (code_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨(qOf s, s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol), ⟨⟨hs, rfl⟩, rfl⟩,
      ⟨⟨ht, (qOf_pub hp).symm⟩, hp.2.2.2.2.2.2.2.2.2.2.2.symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.RISCV64.ParameterCandidate

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

open VG VG.RISCV64
open VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Impl.MillerRabin.RISCV64.Search (roundCall millerRabin draw round)
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

/-- The candidate calling the round `v`. -/
abbrev candCode (v : RoundImpl) : Prog isa := code v.name v.code

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- The candidate uses the stack its round does. -/
theorem candidate_stack (v : RoundImpl) : sdepth (candCode v) ≤ 96 := by
  simp only [candCode, code, main, mainQ, tests, testQ, testRest, test, millerRabin, draw, round, roundCall, pResult,
    qResult, ite_true,
    ite_false, Bool.false_eq_true, sdepth]
  simp (disch := decide) only [sdepth_of_noFrames, Nat.max_zero, Nat.zero_max, Nat.max_self]
  exact v.stack

/-! ## The internal contract, under `abi.withConsts` -/

/-- RSA's table of trial division. -/
abbrev tables : List (String × List (BitVec 64)) := VG.Impl.RsaKeyGen.TrialTable32.consts

/-- The candidate's internal contract, as its caller states it. -/
abbrev candContract : Contract isa := Proof.Ffdh.sievedParameterCandidateContract (abi.withConsts tables) 96

/-- `pcPre` without the table. -/
def pcBase (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
  let used : Region := ⟨s.gpr .a2, 8⟩
  let rand : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
  let scr : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  let below : Region := ⟨s.sp - BitVec.ofNat 64 96, 96⟩
  96 ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    s.rd = [rand, args] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rand ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rand ∧ used.Disjoint scr ∧ used.Disjoint args ∧
    rand.Disjoint scr ∧ scr.Disjoint args ∧
    below.Disjoint out ∧ below.Disjoint used ∧ below.Disjoint rand ∧ below.Disjoint scr ∧ below.Disjoint args ∧
    (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ (s.gpr .a7).toNat % 8 = 0 ∧
    512 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 8192 ∧
    (s.gpr .a1).toNat = ((s.gpr .a3).toNat + 7) / 8 ∧
    (((s.gpr .a4).setWidth 32).toNat = 2 ∨ ((s.gpr .a4).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .a1).toNat ≤ (stackArg s 0).toNat

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem pc_base (s : State) (h : (Proof.Ffdh.sievedParameterCandidateContract abi 96).pre s) : pcBase s := by
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackBelow, pcBase, stackArgs_one, List.append_eq] at h
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackBelow, pcBase, stackArgs_one, List.append_eq] at h
  sig_split h
  sig_reduce [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackBelow, pcBase, stackArgs_one, List.append_eq]
  sig_and_intros
  sig_close
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

private theorem tables_eq' :
    tables = [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] := rfl

private theorem packed_length' : VG.Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

theorem pc_pre (s : State) (h : candContract.pre s) : pcPre s := by
  unfold candContract Proof.Ffdh.sievedParameterCandidateContract at h
  rw [tables_eq'] at h
  obtain ⟨h₁, hc⟩ := pre_consts.mp h
  obtain ⟨a1, a2, a3, hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, q1, q2, q3, q4, q5, n1, n2, n3, n4, al1, al2,
    b1, b2, hL, hg, hsw⟩ := pc_base _ h₁
  have hrd' : (stripConsts _ s).rd = [⟨s.gpr .a5, (s.gpr .a6).toNat⟩, ⟨stackArgAddr s 0, 8⟩] := hrd
  have hwr' : s.wr = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩, ⟨s.gpr .a2, 8⟩, ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩] := hwr
  have hreg : constRegs [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] s =
      [tabR s] := by
    rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, packed_length']
  have hrd₂ : s.rd = [⟨s.gpr .a5, (s.gpr .a6).toNat⟩, ⟨stackArgAddr s 0, 8⟩, tabR s] := by
    rw [← List.take_append_drop (s.rd.length -
      [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)].length) s.rd, hc.1, hreg]
    change (stripConsts _ s).rd ++ _ = _
    rw [hrd']; rfl
  have hm := List.mem_singleton_self (VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)
  have hfit := hc.fit hm
  have hal := hc.aligned hm
  rw [packed_length'] at hfit
  have hw := hc.wr1
  rw [packed_length'] at hw
  refine ⟨a1, a2, a3, hrd₂, hwr', d1, d2, d3, d4, d5, d6, d7, d8, d9, q1, q2, q3, q4, q5, n1, n2, n3, n4, al1,
    al2, b1, b2, hL, hg, hsw, hfit, by omega, fun i hi => ?_, hw _ (by rw [hwr']; simp),
    hw _ (by rw [hwr']; simp)⟩
  have e := hc.readW hm (by rw [packed_length']; exact hi)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [packed_length']; exact hi), Option.getD_some,
    Proof.RsaKeyGen.TrialTable32.packed_entry hi] at e
  exact e

theorem pc_post₀ : ∀ s t, True → pcPost s t → (Proof.Ffdh.sievedParameterCandidateContract abi 96).post s t := by
  sig_implies_post [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    pcPost, pcResult, pcRand, stackArgs_one, List.append_eq]

theorem pc_post (s t : State) (h : pcPost s t) : candContract.post s t := by
  unfold candContract Proof.Ffdh.sievedParameterCandidateContract
  rw [tables_eq']
  exact post_consts.mpr (pc_post₀ s t trivial h)

theorem pc_pub (s t : State) (h : candContract.pub s t) : pcPub s t := by
  unfold candContract Proof.Ffdh.sievedParameterCandidateContract at h
  rw [tables_eq'] at h
  obtain ⟨hp, hsy⟩ := pub_consts.mp h
  sig_pub [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argRegs,
    stackArgs_one, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l⟩ := hp
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, hsy _ (List.mem_singleton_self _)⟩

/-- `vg_ffdh_parameter_candidate_sieved` meets its internal contract, for any
implementation of the round. -/
theorem candidate_correct (v : RoundImpl) (s : State) (h : candContract.pre s) :
    ∃ t s', Exec isa (candCode v) s t s' ∧ abiPreserved s s' ∧ candContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := code_correct s (pc_pre s h)
  exact ⟨t, s', he, ha, pc_post s s' hp⟩

/-- And in constant time. -/
theorem candidate_ct (v : RoundImpl) : ConstantTime isa candContract.pre candContract.pub (candCode v) :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    code_ct s₁ s₂ t₁ t₂ s₁' s₂' (pc_pre _ h₁) (pc_pre _ h₂) (pc_pub _ _ hp) e₁ e₂

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
