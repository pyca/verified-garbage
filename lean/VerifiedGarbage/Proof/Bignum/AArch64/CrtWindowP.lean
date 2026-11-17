module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowQ
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
public import VerifiedGarbage.Proof.Bignum.CrtPRanges
public import VerifiedGarbage.Proof.Bignum.CrtWindowFrameWide
import VerifiedGarbage.Proof.Framework.Omega

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
