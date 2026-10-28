module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset

/-! Exponent-prefix semantics of a window, including its reset. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A complete window leaves its table and packed source exponent intact. -/
def WindowPost (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc : Nat)
    (Q : Prop) (x E v : Nat) (t : State) : Prop :=
  TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
  wv t.mem P (slot w aY) w < X ∧
  (Q → wv t.mem P (slot w aY) w % X = x ^ (32 * E + v) * 2 ^ (64 * w) % X) ∧
  Frm P (rawWindowRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
  word t.mem P (8 * Crt.sNib) = 0 ∧ word t.mem P (8 * Crt.sBit) = 0 ∧
  (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
    word t.mem P (8 * k) = word s.mem P (8 * k))

theorem windowBody_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x E v : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hv : v < 32) (hnib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.windowBody M.mm S.code) s
      (WindowPost s P w mi X Xc Q x E v) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.windowBody
  refine WP.seq (WP.mono (windowCore_ok M S hc ht hw hw' hR hy hyv hv hnib)
    fun u ⟨cu,tu,yu,vu,fu,ku,hu⟩ => ?_)
  refine WP.mono (resetWindow_ok cu) fun t ⟨ct,yt,nt,bt,ft,kt,hh⟩ => ?_
  refine ⟨ct,tu.of_win ft cu.scrT.nowrap,yt.symm ▸ yu,?_,(fu.trans ft).window_tight ?_,
    (ku.trans kt).mono (by decide),nt,bt,?_⟩
  · intro hQ; rw [yt]; exact vu hQ
  · exact (hh _ (by decide) (by decide) (by decide)).trans
      (hu _ (by decide) (by decide) (by decide))
  · intro k hk he hj hn hb
    exact (hh k hk hn hb).trans (hu k hk he hj)

/-- Internal proof interface for the inline or outlined arithmetic window. -/
structure Window where
  code : Prog isa
  ok : ∀ {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc x E v : Nat} {Q : Prop},
    TableCtx s P w mi X Xc → CrtWindowFive.CTab s.mem P w X Q x →
    2 ≤ w → w < 2 ^ 30 → Nat.Coprime (2 ^ (64 * w)) X →
    wv s.mem P (slot w aY) w < X →
    (Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X) →
    v < 32 → word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v →
    WP isa code s (WindowPost s P w mi X Xc Q x E v)
  ct : RelCT isa (Two RawWindowPre) code (fun _ _ => True)

def Window.inline (M : Mont) (S : Selector) : Window :=
  ⟨VG.Impl.Rsa.AArch64.WindowFive.windowBody M.mm S.code, windowBody_ok M S, windowBody_raw_ct M S⟩

end VG.Proof.Bignum.AArch64.WindowFive
