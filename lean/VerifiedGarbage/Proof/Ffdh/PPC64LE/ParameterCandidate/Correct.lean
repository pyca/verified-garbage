module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Front
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Exit
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# An FFDH parameter candidate on PPC64LE: correctness

`code_correct`: `code` meets `pcContract`'s postcondition and keeps what the
calling convention preserves, for any implementation of the round.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkedCandidate)

theorem checked_short {bits g : Nat} {r : List Byte} (h : r.length < (bits + 7) / 8) :
    checkedCandidate bits g r = none := by
  have : (r.take ((bits + 7) / 8)).length ≠ (bits + 7) / 8 := by rw [List.length_take]; omega
  simp only [checkedCandidate, Spec.RsaKeyGen.draw, this, ↓reduceIte, bind, Option.bind]

/-- The tape's length and `out_len`. -/
theorem lenLoad_ok {p : PP} {t : State} (h : St p t) :
    WP isa (.block [ldh .r3 hRandLen, ldh .r4 hLen]) t fun u => (u.gpr .r3 = BitVec.ofNat 64 p.r.length ∧
      u.gpr .r4 = BitVec.ofNat 64 p.L ∧ u.mem = t.mem) ∧ Keep [.r3, .r4] t u := by
  refine WP.keep [.r3, .r4] ?_ (by decide)
  simp only [ldh, hRandLen, hLen]
  prun [h.r31, h.ld (d := 144) (by decide), h.ld (d := 24) (by decide), h.args.rlen', h.args.len']

/-- The length check's flag. -/
theorem lenChk_ok {p : PP} {t : State} (h : St p t) (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4)) t fun v =>
      isa.eval (.zero .d .r5) v = some (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) ∧ St p v ∧
        word v.mem p.B 152 = BitVec.ofNat 64 p.L := by
  have hrl := h.dims.rl
  have hb2 := h.dims.b2
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (lenLoad_ok h) fun u ⟨⟨a3, a4, am⟩, ka⟩ => ?_
  refine WP.mono (geFlag_ok a3 a4 hrl (by omega)) fun v ⟨⟨a5, vm⟩, kv⟩ => ?_
  have hm : v.mem = t.mem := vm.trans am
  exact ⟨eval_zero_ofNat v .r5 (by split <;> decide) a5, h.step (by rw [hm]; exact Frm.refl _ _ _) (ka.trans kv),
    by rw [hm]; exact hU⟩

/-- The length check, then `main` or the status 0. -/
theorem body_ok (R : RoundImpl) {p : PP} {t : State} (h : St p t)
    (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4))
      (.ite (.zero .d .r5) (.block (finish 0)) (main R.name R.code))) t
      (CEnd p (checkedCandidate p.bits p.g p.r)) := by
  refine WP.seq (WP.mono (lenChk_ok h hU) fun v ⟨he, st, hUv⟩ => ?_)
  refine WP.ite (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) he (fun hb => ?_) (fun hb => ?_)
  · have hs : p.r.length < p.L := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_left (by omega)] at hb; exact absurd hb (by decide)
    rw [checked_short (by omega)]
    exact finEnd st (r := 0) (Or.inl rfl) rfl rfl rfl hUv
  · have hl : p.L ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega)])
    exact main_ok R st hUv hl

theorem preserved_cases : ∀ r ∈ preserved,
    r = .r2 ∨ ∃ i < 18, Impl.Ffdh.PPC64LE.ParameterCandidate.saved i = r := by decide

theorem r2_cases : ∀ i < 18, Reg.r2 ≠ Impl.Ffdh.PPC64LE.ParameterCandidate.saved i := by decide

theorem r3_cases : ∀ i < 18, Reg.r3 ≠ Impl.Ffdh.PPC64LE.ParameterCandidate.saved i := by decide

theorem small_setWidth {k : Nat} (hk : k < 2 ^ 32) : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem status_le (res : Option (Option Nat × Spec.RsaKeyGen.Rand)) : Proof.Ffdh.candidateStatus res ≤ 2 := by
  rcases res with _ | ⟨_ | _, _⟩ <;> simp [Proof.Ffdh.candidateStatus]

/-- `vg_ffdh_parameter_candidate`, for any implementation of the round. -/
theorem code_correct (R : RoundImpl) (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (code R.name R.code) s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa (code R.name R.code) s fun t => abiPreserved s t ∧ pcPost s t
  have hpre := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -⟩ := h
  have hLe : (s.gpr .r4).toNat = (ppOf s).L := hL
  have hlen : (ppOf s).r.length = (s.gpr .r9).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold code
  refine wp_then (front_ok s hpre) fun t ⟨st, hU, _⟩ => ?_
  refine wp_then (body_ok R st hU) fun u hu => ?_
  obtain ⟨E, u3, uo, uu⟩ := hu
  refine WP.mono (exit_ok E) fun w ⟨wr, wlr, wm, wsp, wo⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [wo .r2 (by decide) (by decide) r2_cases, E.r2]; rfl
    · rw [wr i hi]; simp [ppOf, hi]
  · rw [wsp, E.sp]; rfl
  · rw [wlr]; simp [ppOf]
  · have hres : pcResult s = checkedCandidate (ppOf s).bits (ppOf s).g (ppOf s).r :=
      (VG.Proof.Ffdh.ParameterCandidate.checkedCandidate_eq _ _ _).symm
    simp only [pcPost]
    rw [hres, wm, wo .r3 (by decide) (by decide) r3_cases, u3, hLe]
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

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
