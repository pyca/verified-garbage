module

public import VerifiedGarbage.Proof.Dsa.X86_64.MinusCore
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
import Mathlib.Tactic.Set

/-! # Modulus-minus constants in a linked DSA workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem minus_ok {s : State} {B : Addr} {Z o w wx m amount : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 31) (ham : amount ≤ m) :
    WP isa (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = m - amount ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (minusCore_ok hc.good (Nat.le_refl _) hw hw' ha (by rw [hm.modulus]; exact ham))
    fun t ⟨ht, hf, hk⟩ => ?_
  have harr : Arrays (off B o) wx [aY] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aY) hf (Nat.le_refl _) (by omega)
  have hct := arrays_context hc harr (by decide) hk
  have hz := hc.good.scr.nowrap
  have hn := (harr.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hm.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [harr.word0_of_not_mem (by decide) (by decide) hz (by omega)]
    exact hm.inverse
  rw [hm.modulus] at ht
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, arrays_work harr (by decide), hk⟩

end VG.Proof.Dsa.X86_64
