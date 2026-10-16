module

public import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.FrameTrim

/-! The window helper preserves the packed exponent word. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Impl.Bignum VG.Impl.Bignum.Public

/-- A shared window touches four arithmetic arrays and four bookkeeping words. -/
def rawWindowRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
    (slot w Crt.aT, 8 * (w + 2)), (8 * Crt.sBit, 8), (8 * Crt.sNib, 8),
    (8 * Crt.sEnt, 8), (8 * Crt.sJ, 8)]

theorem Frm.window_tight {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B (crtWinRanges w) m m')
    (hv : word m' B (8 * Crt.sV) = word m B (8 * Crt.sV)) :
    Frm B (rawWindowRanges w) m m' := by
  apply Frm.drop_word (d := 8 * Crt.sV) _ hv
  exact h.mono (by simp [crtWinRanges, rawWindowRanges])

end VG.Proof.Bignum
