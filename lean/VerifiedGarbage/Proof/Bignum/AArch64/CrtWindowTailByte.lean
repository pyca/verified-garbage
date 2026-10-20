module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath

/-! Composition of tail bits into complete source bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (tailBits)

theorem tailBits_ok (W : Window) (n : Nat) {s : State} {P : Addr} {w b K V : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hp : Pending s P w X Q x b K) (hn : n ≤ 8) (hV : V < 256)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    WP isa (tailBits W.code n) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      Pending t P w X Q x ((b + n) % 5) (K * 2 ^ n + V / 2 ^ (8 - n)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  induction n with
  | zero =>
    have hb : b < 5 := by obtain ⟨_,_,hb,_⟩ := hp; exact hb
    apply WP.block_nil
    refine ⟨hc,ht,?_,Frm.refl _ _ _,Keep.refl _ _,fun _ _ _ _ _ _ => rfl⟩
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt hb, Nat.pow_zero, Nat.mul_one,
      Nat.sub_zero, show 2 ^ 8 = 256 from rfl, Nat.div_eq_of_lt hV] using hp
  | succ n ih =>
    unfold tailBits
    refine WP.seq (WP.mono (ih (by omega)) fun u ⟨cu,tu,pu,fu,ku,hu⟩ => ?_)
    have huV : word u.mem P (8 * Crt.sV) = BitVec.ofNat 64 V :=
      (hu _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbyte
    refine WP.mono (takeBit_pending W cu tu hw hw' hR pu (by omega) hV huV)
      fun t ⟨ct,tt,pt,ft,kt,hh⟩ => ?_
    refine ⟨ct,tt,?_,fu.trans ft,(ku.trans kt).mono (by decide),?_⟩
    · rw [tail_prefix_step K V (by omega)] at pt
      have hb' : ((b + n) % 5 + 1) % 5 = (b + (n + 1)) % 5 := by omega
      rw [hb'] at pt
      exact pt
    · intro k hk he hj hv hb
      exact (hh k hk he hj hv hb).trans (hu k hk he hj hv hb)

/-- Eight steps consume exactly one byte; no exponent padding is introduced. -/
theorem tailByte_ok (W : Window) {s : State} {P : Addr} {w b K V : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hp : Pending s P w X Q x b K) (hV : V < 256)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    WP isa (tailBits W.code 8) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      Pending t P w X Q x ((b + 8) % 5) (K * 256 + V) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  simpa using tailBits_ok W 8 hc ht hw hw' hR hp (by decide) hV hbyte

end VG.Proof.Bignum.AArch64.WindowFive
