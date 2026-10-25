module

public import VerifiedGarbage.Proof.Ed448.SignedWindow
public import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister

/-! Expanded scalar bits preserved by verification's point operations. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep off ofs Outside clob mask contains_sc cswapE opSwap)
open VG.Impl.X448.X86_64 (BITS slot)

/-- The expanded scalar bits, beyond the slots every point operation modifies. -/
def Bits (base : Addr) (o k : Nat) (s : State) : Prop :=
  ∀ t < 461, s.mem (off base (o - 1 + t)) = BitVec.ofNat 8 (SignedWindow.carry k t)

theorem Bits.bit {base : Addr} {o k : Nat} {s : State} (h : Bits base o k s)
    (ho : 1 ≤ o) {t : Nat} (ht : t < 460) :
    s.mem (off base (o + t)) = BitVec.ofNat 8 (k / 2 ^ t % 2) := by
  have hh := h (t + 1) (by omega)
  simpa only [SignedWindow.carry, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel, show o - 1 + (t + 1) = o + t by omega] using hh

theorem Bits.keep {base : Addr} {o k : Nat} (ho : 2048 ≤ o) (hb : o + 460 ≤ 8192) {s u : State} (h : Bits base o k s) (f : Keep base s u) :
    Bits base o k u := by
  intro t ht
  have hout : ofs base (off base (o - 1 + t)) < 64 ∨
      64 + 1584 ≤ ofs base (off base (o - 1 + t)) := by
    rw [VG.Proof.X448.X86_64.ofs_off' base (by omega)]
    right; omega
  rw [f.mem _ hout]
  exact h t ht

end VG.Proof.Ed448.X86_64.Window
