import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base

/-!
# A candidate on AArch64: what Miller–Rabin keeps

`MrCtx`: the working space, `-c⁻¹` (in `sMinv`), `c`, the witness
`b R mod c` in `aB`, `R mod c` and `c − R mod c`; `MrCtx.of_frm` keeps it
across changes elsewhere.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne)

/-- What Miller–Rabin keeps: the working space, `-c⁻¹`, `c`, the witness
`b R mod c` in `aB`, `R mod c` and `c − R mod c`. -/
structure MrCtx (t : State) (B : Addr) (Z w : Nat) (c bm : Nat) : Prop where
  ws : Ws t B Z w
  inv : ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0
  n : wv t.mem B (slot w aN) w = c
  b : wv t.mem B (slot w aB) w = bm
  r1 : wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % c
  rm1 : wv t.mem B (slot w aRm1) w = c - 2 ^ (64 * w) % c

/-- The Montgomery context of `MrCtx`. -/
theorem MrCtx.good {t : State} {B : Addr} {Z w c bm : Nat} (h : MrCtx t B Z w c bm) :
    Good t B Z w (word t.mem B (8 * sMinv)) ∧ slot w 8 ≤ Z :=
  h.ws.good

/-- `MrCtx` survives changes away from what it keeps. -/
theorem MrCtx.of_frm {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, KMut r)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (dB : ∀ r ∈ rs, slot w aB + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aB)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1) :
    MrCtx t B Z w c bm := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hw := hc.ws.w1
  have e : ∀ {j : Nat}, j < 16 → slot w j + 8 * w ≤ Z := fun hj => by
    have := slot_lt (w := w) hj; omega
  have eB := e (show aB < 16 by decide)
  have e1 := e (show aR1 < 16 by decide)
  have em := e (show aRm1 < 16 by decide)
  have eN := e (show aN < 16 by decide)
  refine ⟨hc.ws.congr' hf hm k hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by have := dN r hr; omega) (by omega),
      hf.word_eq (d := 8 * sMinv) dI (by simp only [sMinv] at *; have := hc.ws.h256; omega)]
    exact hc.inv
  · rw [hf.wv_eq dN (by omega)]; exact hc.n
  · rw [hf.wv_eq dB (by omega)]; exact hc.b
  · rw [hf.wv_eq d1 (by omega)]; exact hc.r1
  · rw [hf.wv_eq dm (by omega)]; exact hc.rm1

end VG.Proof.RsaKeyGen.AArch64
