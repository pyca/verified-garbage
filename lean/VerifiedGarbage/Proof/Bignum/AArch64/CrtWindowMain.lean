module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBack
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
import VerifiedGarbage.Proof.Bignum.AArch64.CrtQ
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
public import VerifiedGarbage.Proof.Bignum.CrtPRanges
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Bignum.AArch64.CrtWindowP`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowQ`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowPow`, which this module and modules that import it used -/

section

/-! ### `Bignum.CrtWindowFrameWide`, which this module and modules that import it used -/

section

/-! Frames for prime workspaces with 32-entry exponentiation tables. -/

@[expose] public section
namespace VG.Proof.Bignum.CrtWindowFive
open VG VG.Impl.Bignum VG.Proof.Bignum

/-- What code in a prime's workspace may change, at `B`: all but its link,
`w_X`, `-X⁻¹` and its arrays' bases. -/
def xRange32 (o wx : Nat) : Nat × Nat := (o + 8 * 17, slot wx 8 + tabBytes32 wx - 8 * 17)

theorem to_x32 {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8) (ho : o + slot wx 8 ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange32 o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  refine (Frm.rebase h (by omega_using [ho, h256]) fun r hr' => by have := hr r hr'; omega_using [ho, this]).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange32]
  omega_using [this]

/-- `to_x32` for changes that reach the table. -/
theorem to_xT32 {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes32 wx) (ho : o + (slot wx 8 + tabBytes32 wx) ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange32 o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  refine (Frm.rebase h (by omega_using [ho, h256]) fun r hr' => by have := hr r hr'; omega_using [ho, this]).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange32]
  omega_using [this]

/-- The words of the modulus' header and arrays, below `o`, past code in
the prime's workspace. -/
theorem x_below32 {B : Addr} {o wx : Nat} {m m' : Mem} (h : Frm B [xRange32 o wx] m m') {d : Nat}
    (hd : d + 8 ≤ o) (ho : o < 2 ^ 64) : word m' B d = word m B d :=
  h.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange32]; omega_using [hd]) (by omega_using [hd, ho])


end VG.Proof.Bignum.CrtWindowFive

end

end

/-!
# RSA with the CRT on AArch64: `c^d mod X`

In a prime's phase, from `c G mod n` in the modulus' `Y` and `R_X mod X` in
the prime's: `c R_X mod X` by `redc`, then `Y := Y^d` (`powPhase_ok`):
`c^d R_X mod X` if `X` divides `n`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (xRange32 tabBytes32 to_x32 to_xT32 x_below32)
open VG.Proof.MlKem.AArch64 (Keep)

/-- The prime's `-X⁻¹`, `X` and 1 past a change within `CrtWindowFive.crtExpRanges`. -/
theorem XVals.of_exp {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat}
    (h : XVals s B o wx mx X) (hf : Frm (off B o) (CrtWindowFive.crtExpRanges wx) s.mem t.mem)
    (hz : (off B o).toNat + slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  have rN := CrtWindowFive.crtExpRanges_arr wx (j := Public.aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rO := CrtWindowFive.crtExpRanges_arr wx (j := Public.aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have lO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  exact ⟨by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact h.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega_arith) (by omega_arith)]; exact h.inv,
    by rw [hf.wv_eq (fun r hr => by have := rO r hr; omega_arith) (by omega_arith)]; exact h.one⟩

/-- From the modulus' workspace, `c G mod N` in its `Y` and `R_X mod X` in
the prime's: the prime's `Y := c^d R_X mod X` if `X` divides `N`, `d` the
bytes whose pointer and length are in the modulus' header slots `sd` and
`slen`. Ends in the prime's workspace. -/
theorem powPhase_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C : Nat}
    {sl o wx sd slen : Nat} {ep : Addr} {eb : List Byte}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes32 wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32) (hslv : word s.mem B (8 * sl) = off B o)
    (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hnY : wv s.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hyc : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (hsd : sd < 32) (hsln : slen < 32) (hep : word s.mem B (8 * sd) = ep)
    (hel : word s.mem B (8 * slen) = BitVec.ofNat 64 eb.length) (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024)
    (he : Src s B Z ep eb) :
    WP isa (seqs (([.block [ldh .x0 sl]] : List (Prog isa)) ++ redc M.mm Public.aY ++ [VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen])) s
      fun t => SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧
        wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
        (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = C ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
        word t.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX) ∧
        Frm B [xRange32 o wx] s.mem t.mem ∧ Keep (mmRegs ++ ([.x0] : List Reg)) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have ho64 : o < 2 ^ 64 := by omega_arith
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B o ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc hsl, hs.ld (d := 8 * sl) (by omega_arith), hslv]) rfl rfl rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_
  have hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.wr) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo (by
      have ht : tabBytes wx ≤ tabBytes32 wx := by unfold tabBytes tabBytes32; omega_arith
      omega_arith)
  have hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  refine wp_seqs_append (by simp [redc]) (by simp) ?_
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega_arith) hX1 (j := Public.aY) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, hv₂, f₂, k₂⟩ => ?_
  have fx₂ : Frm B [xRange32 o wx] s₁.mem s₂.mem := to_x32 f₂ (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hb₂ : ∀ d, d + 8 ≤ o → word s₂.mem B d = word s.mem B d := fun d hd => by
    rw [x_below32 fx₂ hd ho64, hm₁]
  have hY₂ : wv s₂.mem (off B o) (slot wx Public.aY) wx = wv s.mem (off B o) (slot wx Public.aY) wx := by
    have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hc₁.good.scr.nowrap
    rw [f₂.wv_eq (fun r hr => by have := rY r hr; omega_arith) (by omega_arith), hm₁]
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have hsrc₂ : Src s₂ B Z ep eb := he.congrK (rs := mmRegs ++ [.x0]) (by
    rw [← hm₁] at *
    exact InScr.of_frm fx₂ fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange32]; omega_arith)
    ((k₁.trans k₂).mono (by decide))
  -- The exponent's base and the start, in Montgomery form if `X` divides `N`.
  have hxc : X ∣ N → wv s₂.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X := fun hd => by
    apply VG.Proof.Bignum.redc_cancel hR
    rw [Nat.pow_mul] at hv₂
    rw [hv₂, hm₁, ← Nat.mod_mod_of_dvd _ hd, hnY, Nat.mod_mod_of_dvd _ hd, ← Nat.pow_mul]
  change WP isa (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen) s₂ _
  refine WP.mono (expLoop_ok W M S (Q := X ∣ N) hc₂ hhi hwx2 hwx (by omega_arith) hX₂.n hX₂.inv hXodd hlt₂ hxc
    (by rw [hY₂]; exact hyl) (fun hd => by rw [hY₂]; exact hyc hd) hsd hsln (by rw [hb₂ _ (by omega_arith)]; exact hep)
    (by rw [hb₂ _ (by omega_arith)]; exact hel) hL1 hL2 hsrc₂) fun t ⟨hc, hlt, hv, f₃, k₃⟩ => ?_
  refine ⟨hc, XVals.of_exp hX₂ f₃ (by have := hc₂.good.scr.nowrap; omega_arith), hlt, fun hd => ?_, ?_, ?_,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · exact hv hd
  · rw [f₃.word_eq (fun r hr => by
      simp only [CrtWindowFive.crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
      have := hdr_lt_slot wx aT (show 31 < 32 by decide)
      have := hdr_lt_slot wx 8 (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sMaskX, sExp, sExpLen, sI, sTab, sV, sBit, sNib, sEnt, sJ, sFn] <;> omega_arith)
      (by unfold sMaskX sFn; omega_arith), f₂.word_eq (sMaskX_redc wx) (by unfold sMaskX sFn; omega_arith), hm₁]
  · rw [← hm₁]
    exact fx₂.trans (to_xT32 f₃ (CrtWindowFive.crtExpRanges_ok wx) (by omega_arith) (List.mem_singleton_self _))

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-!
# RSA with the CRT on AArch64: `q`'s phase

`qPhase`: `m_q = c^dQ mod q` into `q`'s `Y`, if `q` divides
`n` and the modulus' `X_m ≡ c R`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (xRange32 tabBytes32 to_x32 x_below32)
open VG.Proof.MlKem.AArch64 (Keep)

/-- The start of a prime's phase (`unitPhase_ok`). -/
def unitSteps (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) : List (Prog isa) :=
  gPow mul sl ++ [.block [ldh .x0 sl]] ++ redc mul Public.aY ++ copyArr Public.aY aXc ++
    [.block [leave]]

/-- The power in a prime's phase (`powPhase_ok`). -/
def powSteps (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sl sd slen : Nat) : List (Prog isa) :=
  [.block [ldh .x0 sl]] ++ redc mul Public.aY ++ [VG.Impl.Rsa.AArch64.WindowFive.expLoop window mul select sd slen]

theorem qPhase_eq (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.AArch64.WindowFive.qPhase window mul select =
    unitSteps mul sWsQ ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps window select mul sWsQ sDq sQlen ++ [mul Public.aY Public.aY Public.aOne, .block [leave]])) := by
  simp only [VG.Impl.Rsa.AArch64.WindowFive.qPhase, unitSteps, powSteps, enterQ, List.append_assoc, List.cons_append, List.nil_append]

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.CrtWindowPRanges`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT: what `p`'s phase changes

`p`'s phase changes, in the modulus' workspace, `gPow`'s ranges and `X`
(`pRanges`), and the prime's workspace (`xRange32`); these are the words and
numbers it keeps.
-/

@[expose] public section

namespace VG.Proof.Bignum.CrtWindowFive

open VG VG.Impl.Bignum

theorem pxR_bound {w o wx : Nat} (hlo : slot w 8 ≤ o) :
    ∀ r ∈ pRanges w ++ [xRange32 o wx], 8 * 22 ≤ r.1 ∧ r.1 + r.2 ≤ o + slot wx 8 + tabBytes32 wx := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  have : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  intro r hr
  simp only [pRanges, gRanges, xRange32, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega_arith

theorem px_hdr {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange32 o wx]) m m')
    (hlo : slot w 8 ≤ o) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD) (h2 : i ≠ Public.sCnt) :
    word m' B (8 * i) = word m B (8 * i) := hf.word_eq (fun r hr => by
  have hb := pxR_bound hlo r hr
  have := hdr_lt_slot w Public.aAcc (show i < 32 from hi)
  have := hdr_lt_slot w Public.aTmp (show i < 32 from hi)
  have := hdr_lt_slot w Public.aY (show i < 32 from hi)
  have := hdr_lt_slot w Public.aX (show i < 32 from hi)
  have := slot_le (w := w) (show Public.aX < 8 by decide)
  simp only [pRanges, gRanges, xRange32, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by omega_arith)
  · exact Or.inl (by omega_arith)
  · exact Or.inl (by omega_arith)
  · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
    unfold Crt.sD sFn at h1 ⊢; omega_using [h1]
  · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
    unfold Public.sCnt sFn at h2 ⊢; omega_using [h2]
  · exact Or.inl (by omega_arith)
  · exact Or.inl (by simp only at hb ⊢; omega_arith)) (by omega_using [hi])

theorem px_above {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange32 o wx]) m m')
    (hlo : slot w 8 ≤ o) {d : Nat} (hd : o + slot wx 8 + tabBytes32 wx ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  hf.word_eq (fun r hr => Or.inr (by have := pxR_bound hlo r hr; omega_using [hd, this])) hd'

theorem px_wv {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (pRanges w ++ [xRange32 o wx]) m m')
    (hlo : slot w 8 ≤ o) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc)
    (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) (h4 : j ≠ Public.aX) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  have := hdr_lt_slot w j (show 31 < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  have s4 := slot_sep (w := w) h4
  refine hf.wv_eq (fun r hr => ?_) (by omega_arith)
  have hb := pxR_bound hlo r hr
  simp only [pRanges, gRanges, xRange32, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] at hb ⊢ <;> omega_arith

end VG.Proof.Bignum.CrtWindowFive

end

end

/-!
# RSA with the CRT on AArch64: `p`'s phase

`pPhase`: `m_p = c^dP mod p` as `pPhase`'s `qPhase` computes `m_q`, then
`m_q R_p mod p` (from `m_q G mod n`, `mqPart_ok`), and
`h = (m_p - m_q) qInv mod p` into `p`'s `Y` (`hPart_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (xRange32 tabBytes32 px_hdr px_above px_wv x_below32 pxR_bound)
open VG.Proof.MlKem.AArch64 (Keep)

theorem pPhase_eq (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : VG.Impl.Rsa.AArch64.WindowFive.pPhase window select mul =
    unitSteps mul sWsP ++ (mqSteps mul ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps window select mul sWsP sDp sPlen ++ (([.block [leave]] : List (Prog isa)) ++ hSteps mul)))) := by
  simp only [VG.Impl.Rsa.AArch64.WindowFive.pPhase, unitSteps, powSteps, mqSteps, hSteps, enterP, List.append_assoc, List.cons_append,
    List.nil_append]

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowBack`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowFront`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: up to the checks

From the header `entry` leaves, for a valid modulus: the modulus' setup (as
`vg_rsa_public`'s, then `c R mod n`), the primes' workspaces and the checks
(`front_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- After the checks: the three workspaces, the modulus' values, the mask
`M` and the primes `M ? p : 3`, `M ? q : 3`. -/
structure CrtReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  pxv : XVals t B (offP w) (wsWords pl) mp (if M then P else 3)
  pmask : word t.mem (off B (offP w)) (8 * sMaskX) = mask M
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  qxv : XVals t B (offQ32 w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

structure PReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q QI : Nat) : Prop
    where
  n : NReady s t B Z w minv N C
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  pv : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aN) (wsWords pl) = P
  qiv : wv t.mem (off B (offP w)) (slot (wsWords pl) aChunk) (wsWords pl) = QI
  qv : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = Q

/-- The primes' workspaces, from `n`'s setup. -/
theorem setupPart_ok {s t₃ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hr : NReady s t₃ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)) :
    WP isa (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) t₃ fun t => ∃ mp mq, PReady s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) :=
  -- `Crt.primesSetup`'s proof: the same code, and `offQ32` is `offQ`.
  WP.mono (VG.Proof.Bignum.AArch64.setupPart_ok h hr) fun _ ⟨mp, mq, r⟩ =>
    ⟨mp, mq, r.n, r.wsP, r.wsQ, r.pws, r.qws, r.pv, r.qiv, r.qv⟩


/-- The checks, from the primes' workspaces. -/
theorem checksPart_ok {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksOk C G)
    (hG : G (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)) :
    WP isa (seqs C) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  -- The checks' proof: the same code, and `offQ32` is `offQ`.
  WP.mono (VG.Proof.Bignum.AArch64.checksPart_ok h hv ⟨hr.n, hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.pv, hr.qiv, hr.qv⟩ hC hG)
    fun _ ⟨mp', mq', r⟩ => ⟨mp', mq', r.good, r.nv, r.xm, r.msk, r.wsP, r.wsQ, r.pws, r.pxv, r.pmask, r.qws, r.qxv,
      r.hfix, r.iscr, r.keep⟩


/-- Up to the checks, for a valid modulus. -/
theorem front_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksOk C G)
    (hG : G (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)) :
    WP isa (seqs (nSetup M.mm ++ VG.Impl.Rsa.AArch64.WindowFive.primesSetup ++ C)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetup]) hC.ne (wp_seqs_append (by simp [nSetup])
    (by decide) (WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ =>
      WP.mono (setupPart_ok h hwide hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (checksPart_ok h hwide hv hr' hC hG) fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

end VG.Proof.Bignum.AArch64.WindowFive

end

end


/-!
# RSA with the CRT on AArch64: from the checks to the result

`q`'s phase, `p`'s, and `m = m_q + q h` written out masked (`back_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (offQ32 tabBytes32 xRange32 px_hdr px_above)
open VG.Proof.MlKem.AArch64 (Keep)

/-- After `q`'s phase: as after the checks, and `m_q` in `q`'s `aY`. -/
structure QReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dqb : List Byte) (Mk : Bool) : Prop extends CrtReady s t B Z w pl ql minv mp mq N C P Q Mk where
  qlt : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q

/-- `q`'s phase, from the checks. -/
theorem qPart_ok (W : Window) (M : Mont) (S : Selector) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) t₀ fun t => QReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk := by
  -- `qPart_gen` with this exponentiation, on the same states (`offQ32` is `offQ`).
  rw [qPhase_eq]
  exact WP.mono (VG.Proof.Bignum.AArch64.qPart_gen M (fun sd slen => [VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen])
    (@powPhase_ok W M S) h hv ⟨hr.good, hr.nv, hr.xm, hr.msk, hr.wsP, hr.wsQ, hr.pws, hr.pxv, hr.pmask, hr.qws, hr.qxv, hr.hfix, hr.iscr,
      hr.keep⟩ hMk)
    fun _ r => ⟨⟨r.good, r.nv, r.xm, r.msk, r.wsP, r.wsQ, r.pws, r.pxv, r.pmask, r.qws, r.qxv, r.hfix, r.iscr, r.keep⟩, r.qlt, r.qval⟩


/-- After `p`'s phase: `h` in `p`'s `aY`, `m_q` in `q`'s. -/
structure PDone (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (C P Q QI : Nat)
    (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : Good t B Z w minv
  msk : word t.mem B (8 * Public.sMask) = mask Mk
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  qn : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = if Mk then Q else 3
  qlt : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aY) (wsWords pl) < if Mk then P else 3
  pval : Mk = true → ∃ a b, a % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * wsWords pl) % P ∧
    b % P = C ^ Spec.Rsa.os2ip dqb % Q * 2 ^ (64 * wsWords pl) % P ∧ b < P ∧
    wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aY) (wsWords pl) * 2 ^ (64 * wsWords pl) % P =
      (a + P - b) % P * QI % P
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- `p`'s phase, from `q`'s. -/
theorem pPart_ok (W : Window) (M : Mont) (S : Selector) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : QReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) t₁ fun t => PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk := by
  -- `pPart_gen` with this exponentiation, on the same states (`offQ32` is `offQ`).
  rw [pPhase_eq]
  exact WP.mono (VG.Proof.Bignum.AArch64.pPart_gen M (fun sd slen => [VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen])
    (@powPhase_ok W M S) h hv ⟨⟨hr.good, hr.nv, hr.xm, hr.msk, hr.wsP, hr.wsQ, hr.pws, hr.pxv, hr.pmask, hr.qws, hr.qxv, hr.hfix, hr.iscr,
      hr.keep⟩, hr.qlt, hr.qval⟩ hMk)
    fun _ r => ⟨r.good, r.msk, r.wsP, r.wsQ, r.pws, r.qws, r.qn, r.qlt, r.qval, r.plt, r.pval, r.hfix, r.iscr, r.keep⟩


/-- `m = m_q + q h` written out masked, from `p`'s phase. -/
theorem finPart_ok {s t₂ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PDone s t₂ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs finish) t₂ fun t => MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk :=
  -- `finish` and its proof are the same (`offQ32` is `offQ`).
  VG.Proof.Bignum.AArch64.finPart_ok h hv ⟨hr.good, hr.msk, hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.qn, hr.qlt, hr.qval,
    hr.plt, hr.pval, hr.hfix, hr.iscr, hr.keep⟩ hMk


/-- From the checks: both phases, and `m = m_q + q h` written out masked. -/
theorem back_ok (W : Window) (M : Mont) (S : Selector) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code ++ VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm ++ finish)) t₀ fun t => MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk := by
  rw [List.append_assoc]
  exact wp_seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (WP.mono (qPart_ok W M S h hwide hv hr hMk) fun _ hq =>
    wp_seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (by simp [finish]) (WP.mono (pPart_ok W M S h hwide hv hq hMk) fun _ hp =>
      finPart_ok h hwide hv hp hMk))

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-!
# RSA with the CRT on AArch64: the computation for a valid modulus

`main`, from the header `entry` leaves, for a valid modulus: `privateCrt`'s
result (zeros if it is `none`) to `out` and whether it is `some` returned
(`crtMain_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

theorem crtMain_eq (chk : List (Prog isa)) (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) :
    VG.Impl.Rsa.AArch64.WindowFive.mainWith chk window select mul = seqs ((nSetup mul ++ VG.Impl.Rsa.AArch64.WindowFive.primesSetup ++ chk) ++ (VG.Impl.Rsa.AArch64.WindowFive.qPhase window mul select ++ VG.Impl.Rsa.AArch64.WindowFive.pPhase window select mul ++ finish)) := by
  simp only [VG.Impl.Rsa.AArch64.WindowFive.mainWith, List.append_assoc]

/-- `main`, for a valid modulus: the result `r`, `some` exactly if the mask
is set. -/
theorem crtMain_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hk : 128 ≤ k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksOk C G)
    (hG : G (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.mainWith C W.code S.code M.mm) s fun t => ∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  have hwide : CrtWindowFive.offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + CrtWindowFive.tabBytes32 (wsWords ql) ≤ Z :=
    Nat.le_trans (CrtWindowFive.prime_scratch32_fits hk h.pl2 h.ql2) (by have := h.zk; omega_using [this])
  rw [crtMain_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (WP.mono (front_ok M h hwide hv hC hG)
    fun t₀ ⟨minv, mp, mq, hr⟩ => WP.mono (back_ok W M S h hwide hv hr rfl) fun t ht => ⟨_, ht, ?_⟩)
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Bignum.AArch64.WindowFive
