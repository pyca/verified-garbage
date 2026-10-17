module

public import VerifiedGarbage.Proof.X25519.AArch64.Word.Formula
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The `_alt` ladder's iteration is RFC 7748's

The slots after an iteration of `AltLadder.step`, in `GF(p)`: no swap, but
`mux_4` choosing the point to double (`(X₃, Z₃)` if the swap and the bit
differ, `Z` clear). The addition of the two points is symmetric, so this is
the ladder's step whichever point is doubled. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.AltLadder
open VG VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 (Slot)
open VG.Proof.Ed25519.AArch64 (Env)
open VG.Proof.X25519.AArch64.Word (Good)

/-! The iteration's updates of the slots, one per operation. -/
def gDm (e : Env) : Env := Function.update e 6 (e 3 - e 4)
def gSn (e : Env) : Env := Function.update e 5 (e 1 + e 2)
def gDn (e : Env) : Env := Function.update e 2 (e 1 - e 2)
def gSm (e : Env) : Env := Function.update e 4 (e 3 + e 4)
def gDmsn (e : Env) : Env := Function.update e 7 (e 5 * e 6)
def gD (zf : Bool) (e : Env) : Env := Function.update e 8 (if zf then e 2 else e 6)
def gS (zf : Bool) (e : Env) : Env := Function.update e 1 (if zf then e 5 else e 4)
def gDnsm (e : Env) : Env := Function.update e 3 (e 4 * e 2)
def gD2 (e : Env) : Env := Function.update e 8 (e 8 * e 8)
def gDpro (e : Env) : Env := Function.update e 4 (e 7 - e 3)
def gS2 (e : Env) : Env := Function.update e 1 (e 1 * e 1)
def gSpro (e : Env) : Env := Function.update e 3 (e 7 + e 3)
def gDpro2 (e : Env) : Env := Function.update e 4 (e 4 * e 4)
def gP (e : Env) : Env := Function.update e 7 (e 1 - e 8)
def gXm (e : Env) : Env := Function.update e 3 (e 3 * e 3)
def gE (e : Env) : Env := Function.update e 2 (toFe 121666 * e 7 + e 8)
def gXn (e : Env) : Env := Function.update e 1 (e 1 * e 8)
def gZm (e : Env) : Env := Function.update e 4 (e 4 * e 0)
def gZn (e : Env) : Env := Function.update e 2 (e 7 * e 2)

/-- The slots after an iteration, from those before it and the flag `Z`. -/
def altEnv (e : Env) (zf : Bool) : Env :=
  gZn (gZm (gXn (gE (gXm (gP (gDpro2 (gSpro (gS2 (gDpro (gD2 (gDnsm (gS zf (gD zf (gDmsn (gSm (gDn
  (gSn (gDm e))))))))))))))))))

theorem toFe_121666 : toFe 121666 = a24 + 1 := rfl

/-- What `altEnv` leaves in the slots `Good` reads. -/
theorem altEnv_vals (e : Env) (zf : Bool) :
    let dm := e 3 - e 4
    let sn := e 1 + e 2
    let dn := e 1 - e 2
    let sm := e 3 + e 4
    let dmsn := sn * dm
    let d := if zf then dn else dm
    let s := if zf then sn else sm
    let dnsm := sm * dn
    let d2 := d * d
    let s2 := s * s
    let p := s2 - d2
    altEnv e zf 0 = e 0 ∧ altEnv e zf 18 = e 18 ∧
    altEnv e zf 1 = s2 * d2 ∧ altEnv e zf 2 = p * (toFe 121666 * p + d2) ∧
    altEnv e zf 3 = (dmsn + dnsm) * (dmsn + dnsm) ∧
    altEnv e zf 4 = (dmsn - dnsm) * (dmsn - dnsm) * e 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem altEnv_ok (e : Env) (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) (hg : Good e x1 st)
    (hsw : st.swap ≤ 1) :
    Good (altEnv e (st.swap == bit k t)) x1 (ladderStep k x1 st t) := by
  obtain ⟨h0, h1, h2, h3, h4, hc⟩ := hg
  obtain ⟨v0, v18, v1, v2, v3, v4⟩ := altEnv_vals e (st.swap == bit k t)
  have hb := bit_le k t
  unfold Good
  rw [v0, v18, v1, v2, v3, v4, ladderStep_eq, h0, h1, h2, h3, h4, hc, toFe_121666]
  rcases (by omega : st.swap = 0 ∨ st.swap = 1) with hs | hs <;>
    rcases (by omega : bit k t = 0 ∨ bit k t = 1) with hk | hk <;>
    simp only [hs, hk, Spec.X25519.cswap] <;>
    refine ⟨trivial, ?_, ?_, ?_, ?_, trivial⟩ <;> grind

end VG.Proof.X25519.AArch64.AltLadder
