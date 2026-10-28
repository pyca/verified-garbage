module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath

/-! The completed exponent prefix and bounded pending bits form one integer. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (takeBit)

def Pending (s : State) (P : Addr) (w X : Nat) (Q : Prop) (x b K : Nat) : Prop :=
  ∃ E v, b < 5 ∧ v < 2 ^ b ∧ E * 2 ^ b + v = K ∧
    wv s.mem P (slot w aY) w < X ∧
    (Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X) ∧
    word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v ∧
    word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b

theorem takeBit_pending (W : Window) {s : State} {P : Addr} {w b K V i : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hp : Pending s P w X Q x b K) (hi : i < 8) (hV : V < 256)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    WP isa (takeBit W.code i) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      Pending t P w X Q x ((b + 1) % 5) (2 * K + V / 2 ^ (7 - i) % 2) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  obtain ⟨E,v,hb,hv,hK,hy,hyv,hn,bc⟩ := hp
  refine WP.mono (takeBit_ok W hc ht hw hw' hR hy hyv hi hb
    (pending_lt16 hb hv) hV hn bc hbyte) fun t ⟨ct,tt,yt,vt,ft,kt,nt,bt,hh⟩ => ?_
  have bounds := pending_bounds hb hv (show V / 2 ^ (7 - i) % 2 < 2 by omega)
  have hpref := pending_prefix b E v (V / 2 ^ (7 - i) % 2)
  rw [hK] at hpref
  refine ⟨ct,tt,?_,ft,kt,hh⟩
  rw [← pending_count hb]
  exact ⟨_,_,bounds.1,bounds.2,hpref,yt,vt,nt,bt⟩

end VG.Proof.Bignum.AArch64.WindowFive
