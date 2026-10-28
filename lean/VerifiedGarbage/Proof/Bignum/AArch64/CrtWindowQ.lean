module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Proof.Bignum.CrtWindowFrameWide

import VerifiedGarbage.Proof.Bignum.AArch64.CrtQ
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow

/-!
# RSA with the CRT on AArch64: `q`'s phase

`qPhase`: `m_q = c^dQ mod q` into `q`'s `Y` (`qPhase_ok`), if `q` divides
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

theorem gx_wv32 {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (gRanges w ++ [xRange32 o wx]) m m')
    (hlo : slot w 8 ≤ o) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc)
    (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  have := hdr_lt_slot w j (show 31 < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  refine hf.wv_eq (fun r hr => ?_) (by omega)
  simp only [gRanges, xRange32, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem NVals.of_frm {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N o wx : Nat}
    (h : NVals s B w minv N) (hf : Frm B (gRanges w ++ [xRange32 o wx]) s.mem t.mem) (hlo : slot w 8 ≤ o)
    (hz : B.toNat + slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) : NVals t B w minv N := by
  have hr : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → j ≠ Public.aY →
      ∀ r ∈ gRanges w ++ [xRange32 o wx], slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj h1 h2 h3 r hr
    have := slot_le (w := w) hj
    have := hdr_lt_slot w j (show 31 < 32 by decide)
    have s1 := slot_sep (w := w) h1
    have s2 := slot_sep (w := w) h2
    have s3 := slot_sep (w := w) h3
    simp only [gRanges, xRange32, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sD, Public.sCnt, sFn] <;> omega_arith
  have lN := slot_le (w := w) (show Public.aN < 8 by decide)
  have lR := slot_le (w := w) (show Public.aR2 < 8 by decide)
  have lO := slot_le (w := w) (show Public.aOne < 8 by decide)
  have rN := hr Public.aN (by decide) (by decide) (by decide) (by decide)
  have rR := hr Public.aR2 (by decide) (by decide) (by decide) (by decide)
  have rO := hr Public.aOne (by decide) (by decide) (by decide) (by decide)
  exact ⟨by rw [hf.wv_eq (fun r h' => rN r h') (by omega_arith)]; exact h.n,
    by rw [hf.word_eq (fun r h' => by have := rN r h'; omega_arith) (by omega_arith)]; exact h.inv,
    by rw [hf.wv_eq (fun r h' => rR r h') (by omega_arith)]; exact h.r2,
    by rw [hf.wv_eq (fun r h' => rR r h') (by omega_arith)]; exact h.r2lt,
    by rw [hf.wv_eq (fun r h' => rO r h') (by omega_arith)]; exact h.one⟩

/-- `q`'s phase: `m_q = c^dQ mod q` into `q`'s `Y`, if `q` divides `N` and
`X_m ≡ c R (mod N)`. -/
theorem qPhase_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C o wx : Nat}
    {ep : Addr} {eb : List Byte}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes32 wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsQ) = off B o) (hws : WsAt s.mem B o wx mx)
    (hN : NVals s B w minv N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hep : word s.mem B (8 * sDq) = ep) (hel : word s.mem B (8 * sQlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = C ^ Spec.Rsa.os2ip eb % X) ∧
      Frm B (gRanges w ++ [xRange32 o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  -- `qPhase`'s proof with this exponentiation: `tabBytes32` is `wsTab`, `xRange32` is `xRange`.
  rw [qPhase_eq]
  exact qPhase_gen M (fun sd slen => [VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen])
    (@powPhase_ok W M S) hg hw hw28 hlo hhi hwx2 hwx hslv hws hN hodd hN1 hXm hX hX1 hXodd hep hel hL1 hL2 he

end VG.Proof.Bignum.AArch64.WindowFive
