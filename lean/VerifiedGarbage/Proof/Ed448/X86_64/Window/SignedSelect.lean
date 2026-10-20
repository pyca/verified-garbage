module

import VerifiedGarbage.Proof.Ed448.X86_64.Window.Sign
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectBase
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectKey
import VerifiedGarbage.Proof.Framework.Sig

/-! Signed selection composes full scans with conditional point negation. -/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.X448.X86_64 (Scr E Keep)
open VG.Impl.X448.X86_64 (BITS)
open VG.Proof.Ed448 (pt)

theorem selectSignedBase_ok {s : State} {base : Addr} (hs : Scr s base) {k t : Nat}
    (ht : t + 5 ≤ 460) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base BITS k s) :
    WP isa selectSignedBase s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) = SignedWindow.signedEntry k t ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  rw [selectSignedBase]
  refine WP.seq (WP.mono (selectBase_ok hs ht hb bs) fun v ⟨kv, pv, fv⟩ => ?_)
  refine WP.mono (negateSelected_ok (kv.scr hs) (by decide) (by decide) ht
    ((kv.gpr _ (by decide)).trans hb) (bs.keep (by decide) (by decide) kv)) fun u ⟨ku, xu, fu⟩ => ?_
  refine ⟨kv.trans ku, ?_, fun j h3 h4 h8 h9 => (fu j h3 h8).trans (fv j h3 h4 h8 h9)⟩
  have hx := congrArg Prod.fst pv
  have hy := congrArg Prod.snd pv
  dsimp only at hx hy
  rw [xu, fu 9 (by decide) (by decide), hx, hy]
  rfl

theorem selectSignedKey_ok {s : State} {base : Addr} (hs : Scr s base) {o k t : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 460 ≤ 8192) (ht : t + 5 ≤ 460)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (selectSignedKey o) s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = SignedWindow.signedPoint (SignedWindow.negative k t)
        (tablePoint s.mem base (SignedWindow.magnitude k t)) ∧
      KeyKeeps (E s.mem base) (E u.mem base) := by
  rw [selectSignedKey]
  refine WP.seq (WP.mono (selectKey_ok hs ho hbnd ht hb bs) fun v ⟨kv, pv, fv⟩ => ?_)
  refine WP.mono (negateSelected_ok (kv.scr hs) ho hbnd ht
    ((kv.gpr _ (by decide)).trans hb) (bs.keep ho hbnd kv)) fun u ⟨ku, xu, fu⟩ => ?_
  refine ⟨kv.trans ku, ?_, fun j h3 h4 h5 h8 h9 h10 => (fu j h3 h8).trans (fv j h3 h4 h5 h8 h9 h10)⟩
  rw [← pv]
  simp only [pt, xu, fu 9 (by decide) (by decide), fu 10 (by decide) (by decide), SignedWindow.signedPoint,
    Proof.Ed448.negPoint, zero_sub]
  split <;> rfl

end VG.Proof.Ed448.X86_64.Window
