module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPending
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailBit

/-! A tail bit either extends the pending digit or executes one complete window. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (takeBit)

def nextExponent (b E d : Nat) : Nat := if b = 4 then 32 * E + d else E
def nextPending (b : Nat) : Nat := if b = 4 then 0 else b + 1
def nextDigit (b d : Nat) : Nat := if b = 4 then 0 else d

theorem rawWindowRanges_sub (w : Nat) : ∀ r ∈ rawWindowRanges w, r ∈ crtWinRanges w := by
  simp [rawWindowRanges, crtWinRanges]

theorem takeBit_ok (W : Window) {s : State} {P : Addr} {w b v V i : Nat}
    {mi : BitVec 64} {X Xc x E : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hi : i < 8) (hb : b < 5) (hv : v < 16) (hV : V < 256)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hcbit : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    let d := 2 * v + V / 2 ^ (7 - i) % 2
    WP isa (takeBit W.code i) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ nextExponent b E d * 2 ^ (64 * w) % X) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (nextDigit b d) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (nextPending b) ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  dsimp only
  unfold takeBit
  refine WP.seq (WP.mono (prepareBit_state hc hi hv hV hn hcbit hbyte)
    fun u ⟨cu,yu,nu,bu,fu,ku,hu,flag⟩ => ?_)
  have tu := ht.of_win fu hc.scrT.nowrap
  have yu' : wv u.mem P (slot w aY) w < X := yu.symm ▸ hy
  have vu : Q → wv u.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X := by
    intro hQ; rw [yu]; exact hyv hQ
  by_cases h4 : b = 4
  · subst b
    refine WP.ite true (by change some (u.gpr .x3 == 0) = some true; rw [flag]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (W.ok cu tu hw hw' hR yu' vu (by omega) nu)
      fun t ⟨ct,tt,yt,vt,ft,kt,nt,bt,hh⟩ => ?_
    refine ⟨ct,tt,yt,vt,fu.trans (ft.mono (rawWindowRanges_sub w)),
      (ku.trans kt).mono (by decide),nt,bt,?_⟩
    intro k hk he hj hn hb
    exact (hh k hk he hj hn hb).trans (hu k hk hn hb)
  · have hz : BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5 ≠ 0 :=
      fun h => h4 ((pending_test hb).mp h)
    refine WP.ite false (by change some (u.gpr .x3 == 0) = some false; rw [flag]; exact congrArg some (beq_eq_false_iff_ne.mpr hz)) (by simp) (fun _ => ?_)
    apply WP.block_nil
    refine ⟨cu,tu,yu',?_,fu,ku.mono (by decide),?_,?_,?_⟩
    · simpa only [nextExponent, ite_eq_right h4] using vu
    · simpa only [nextDigit, ite_eq_right h4] using nu
    · simpa only [nextPending, ite_eq_right h4] using bu
    · intro k hk _ _ hn hb
      exact hu k hk hn hb

end VG.Proof.Bignum.AArch64.WindowFive
