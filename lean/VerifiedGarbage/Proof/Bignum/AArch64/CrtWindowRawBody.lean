module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
public import VerifiedGarbage.Proof.Bignum.CrtWindowFrame
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCore

/-! The complete window body, including reset and caller-state preservation. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (windowBody)

theorem windowBody_raw_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w v : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hy : wv s.mem P (slot w aY) w < X)
    (hv : v < 32) (hnib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (windowBody M.mm S.code) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2 ^ (64 * w)) ^ 32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8 + v)) w % X ∧
      word t.mem P (8 * Crt.sNib) = 0 ∧ word t.mem P (8 * Crt.sBit) = 0 ∧
      Frm P (rawWindowRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  unfold windowBody
  refine WP.seq (WP.mono (windowCore_raw_ok M S hc ht hw hw' hy hv hnib)
    fun u ⟨cu,yu,vu,fu,ku,hu⟩ => ?_)
  refine WP.mono (resetWindow_ok cu) fun t ⟨ct,yt,nt,bt,ft,kt,hh⟩ => ?_
  refine ⟨ct,yt.symm ▸ yu,?_,nt,bt,(fu.trans ft).window_tight ?_,(ku.trans kt).mono (by decide),?_⟩
  · rw [yt]; exact vu
  · exact (hh _ (by decide) (by decide) (by decide)).trans
      (hu _ (by decide) (by decide) (by decide))
  · intro k hk he hj hn hb
    exact (hh k hk hn hb).trans (hu k hk he hj)

theorem windowBody_raw_ct (M : Mont) (S : Selector) :
    RelCT isa (Two RawWindowPre) (windowBody M.mm S.code) (fun _ _ => True) := by
  unfold windowBody
  refine RelCT.seq (two_post (Ψ := fun (p : XPub) s => s.gpr .x0 = off p.B p.o)
    (windowCore_raw_ct M S) ?_)
    (two_map (fun p : XPub => off p.B p.o) (fun _ _ h => h) resetWindow_ct)
  rintro p s ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩
  exact WP.mono (windowCore_raw_ok M S hc ht hw hw' hy hv hn)
    fun t ⟨ct,_⟩ => ct.good.x0

end VG.Proof.Bignum.AArch64.WindowFive
