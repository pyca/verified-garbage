import VerifiedGarbage.Proof.Rsa.X86_64.RpCand

/-!
# `vg_rsa_recover_primes` on x86-64: the candidates

`candLoop`: the candidates `g = 2, 3, …` until one finds `y` or 100 are
tried: `recoverPrimes.go`'s result and the number of tries
(`candLoop_ok`), `ok` in `sC3` and `y` in Montgomery form.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (powMod recoverStep recoverPrimes recoverTries)

/-- The candidates `c` and on, from `s₀`. -/
structure CandI (s₀ : State) (B : Addr) (w N t r c : Nat) (u : State) : Prop where
  frm : Frm B (rg w candJs candHs) s₀.mem u.mem
  keep : Keep mmRegs s₀ u
  cand : word u.mem B (8 * sCand) = BitVec.ofNat 64 c
  go : recoverPrimes.go N t r recoverTries = recoverPrimes.go N t r (recoverTries - c)

/-- `candLoop`: `recoverPrimes.go`'s result `(res.map (pqOf N), cnt)`. -/
theorem candLoop_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t : Nat}
    (hc : Cst s B Z w minv N el r t) :
    WP isa (candLoop M.mm) s fun u => ∃ res : Option Nat, ∃ cnt : Nat,
      recoverPrimes.go N t r recoverTries = (res.map (pqOf N), cnt) ∧
      word u.mem B (8 * sCand) = BitVec.ofNat 64 cnt ∧ word u.mem B (8 * sC3) = mask res.isSome ∧
      (∀ y, res = some y → wv u.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N ∧ y * y % N = 1) ∧
      Frm B (rg w candJs candHs) s.mem u.mem ∧ Keep mmRegs s u := by
  have h256 := hc.ws.h256
  unfold candLoop
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (off B (8 * sCand))
      (BitVec.ofNat 64 0)) (by
    xrun [State.ea, hdr, hc.ws.rdi, hdrOff,
      hc.ws.scr.st (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega)]
    rfl) rfl) fun s₁ ⟨m₁, k₁⟩ => ?_)
  have hf₁ : Frm B (rg w candJs candHs) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega))
      _ _ (by decide)
  refine WP.loop (M := isa) (fun n u => ∃ c, n = recoverTries - c ∧ c < recoverTries ∧ CandI s B w N t r c u)
    ?_ (recoverTries - 0) s₁ ⟨0, rfl, by decide, hf₁, k₁.mono (by decide), by rw [m₁, word_writeW_self], rfl⟩
  rintro n u ⟨c, rfl, hc100, hI⟩
  have hcu : Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) cand_hs hI.keep (by decide)
  refine WP.mono (candBody_ok M hcu hI.cand hc100) fun u' ⟨hz, hf, k, hcand, hc3, hy⟩ => ?_
  have hgo := VG.Proof.Rsa.go_eq N t r hc100
  have hfr : Frm B (rg w candJs candHs) s.mem u'.mem := (hI.frm.rg_trans hf).rg_mono (by decide) (by decide)
  have hk : Keep mmRegs s u' := (hI.keep.trans k).mono (by decide)
  cases hres : recoverStep N t r (c + 2) with
  | some y =>
    rw [hres] at hz hc3 hgo
    refine .inl ⟨by simp [eval, hz], some y, c + 1, ?_, hcand, hc3, fun y' hy' => ?_, hfr, hk⟩
    · rw [hI.go, hgo]; rfl
    · cases hy'; exact ⟨(hy y hres).1, (hy y hres).2, VG.Proof.Rsa.recoverStep_some hres⟩
  | none =>
    rw [hres] at hz hc3 hgo
    by_cases hlast : c + 1 < recoverTries
    · have hlast' : c + 1 < 100 := hlast
      refine .inr ⟨by simp [eval, hz, hlast'], recoverTries - (c + 1), by omega, c + 1, rfl, hlast,
        hfr, hk, hcand, by rw [hI.go, hgo]⟩
    · have hlast' : ¬ c + 1 < 100 := hlast
      refine .inl ⟨by simp [eval, hz, hlast'], none, c + 1, ?_, hcand, hc3, (fun y' hy' => by cases hy'),
        hfr, hk⟩
      rw [hI.go, hgo, show c + 1 = recoverTries by unfold recoverTries at *; omega, VG.Proof.Rsa.go_last]
      rfl

end VG.Proof.Rsa.X86_64
