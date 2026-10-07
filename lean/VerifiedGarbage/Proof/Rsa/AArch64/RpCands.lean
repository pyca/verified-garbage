import VerifiedGarbage.Proof.Rsa.AArch64.RpCand

/-!
# `vg_rsa_recover_primes` on AArch64: the candidates

`candLoop`: the candidates `g = 2, 3, …` until one finds `y` or 100 are
tried: `recoverPrimes.go`'s result and the number of tries
(`candLoop_ok`), `ok` in `sC3` and `y` in Montgomery form.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (powMod recoverStep recoverPrimes recoverTries)
open VG.Proof.Rsa (pqOf)

/-- The candidates `c` and on, from `s₀`. -/
structure CandI (s₀ : State) (B : Addr) (w N t r c : Nat) (u : State) : Prop where
  frm : Frm B (rg w candJs candHs) s₀.mem u.mem
  keep : Keep mmRegs s₀ u
  cand : word u.mem B (8 * sCand) = BitVec.ofNat 64 c
  go : recoverPrimes.go N t r recoverTries = recoverPrimes.go N t r (recoverTries - c)

theorem eval_mask (s : State) {b : Bool} (h : s.gpr .x15 = mask b) :
    isa.eval (.nonzero .x .x15) s = some b := by
  rw [eval_nonzero, ne_zero_iff, h]
  cases b <;> rfl

/-- `candLoop`: `recoverPrimes.go`'s result `(res.map (pqOf N), cnt)`. -/
theorem candLoop_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (hc : Cst s B Z w minv N el r t) :
    WP isa (candLoop M.mm) s fun u => ∃ res : Option Nat, ∃ cnt : Nat,
      recoverPrimes.go N t r recoverTries = (res.map (pqOf N), cnt) ∧
      word u.mem B (8 * sCand) = BitVec.ofNat 64 cnt ∧ word u.mem B (8 * sC3) = mask res.isSome ∧
      (∀ y, res = some y → wv u.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N ∧ y * y % N = 1) ∧
      Frm B (rg w candJs candHs) s.mem u.mem ∧ Keep mmRegs s u := by
  have h256 := hc.ws.h256
  have hn := hc.ws.scr.nowrap
  unfold candLoop
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u => u.mem = s.mem.writeW (off B (8 * sCand))
      (BitVec.ofNat 64 0)) (by
    brun [hc.ws.x0, hdr_enc (show sCand < 32 by decide),
      hc.ws.scr.st (d := 8 * sCand) (by simp only [sCand, sFn]; omega)]
    rfl) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨m₁, k₁⟩ => ?_)
  have hf₁ : Frm B (rg w candJs candHs) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sCand, sFn]; omega)) _ _ (by decide)
  refine WP.loop (M := isa) (fun n u => ∃ c, n = recoverTries - c ∧ c < recoverTries ∧ CandI s B w N t r c u)
    ?_ (recoverTries - 0) s₁ ⟨0, rfl, by decide, hf₁, k₁.mono (by decide), by rw [m₁, word_writeW_self], rfl⟩
  rintro n u ⟨c, rfl, hc100, hI⟩
  have hcu : Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) cand_hs hI.keep (by decide)
  refine WP.mono (candBody_ok M hcu hI.cand hc100) fun u' ⟨h15, hf, k, hcand, hc3, hy⟩ => ?_
  have hev := eval_mask u' h15
  have hgo := VG.Proof.Rsa.go_eq N t r hc100
  have hfr : Frm B (rg w candJs candHs) s.mem u'.mem := (hI.frm.rg_trans hf).rg_mono (by decide) (by decide)
  have hk : Keep mmRegs s u' := (hI.keep.trans k).mono (by decide)
  cases hres : recoverStep N t r (c + 2) with
  | some y =>
    rw [hres] at hev hc3 hgo
    refine .inl ⟨by rw [hev]; simp, some y, c + 1, ?_, hcand, hc3, fun y' hy' => ?_, hfr, hk⟩
    · rw [hI.go, hgo]; rfl
    · cases hy'; exact ⟨(hy y hres).1, (hy y hres).2, VG.Proof.Rsa.recoverStep_some hres⟩
  | none =>
    rw [hres] at hev hc3 hgo
    by_cases hlast : c + 1 < recoverTries
    · have hlast' : c + 1 < 100 := hlast
      refine .inr ⟨by rw [hev]; simp [hlast'], recoverTries - (c + 1), by omega, c + 1, rfl, hlast,
        hfr, hk, hcand, by rw [hI.go, hgo]⟩
    · have hlast' : ¬ c + 1 < 100 := hlast
      refine .inl ⟨by rw [hev]; simp [hlast'], none, c + 1, ?_, hcand, hc3, (fun y' hy' => by cases hy'),
        hfr, hk⟩
      rw [hI.go, hgo, show c + 1 = recoverTries by unfold recoverTries at *; omega, VG.Proof.Rsa.go_last]
      rfl

end VG.Proof.Rsa.AArch64
