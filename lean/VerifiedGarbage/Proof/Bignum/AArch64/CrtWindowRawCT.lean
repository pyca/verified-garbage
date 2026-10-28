module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-! Constant time for the raw relation, without table-power assumptions. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum

def RawWindowPre (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc v, TableCtx s (off p.B p.o) p.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.B p.o) p.wx X False 0 ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 32 ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

theorem rawSquare_post (M : Mont) {p : XPub} {s : State} (h : RawWindowPre p s) :
    WP isa (M.mm aY aY aY) s (RawWindowPre p) := by
  obtain ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩ := h
  exact WP.mono (square_raw_ok M hc hw hw' hy) fun t ⟨ct,yt,_,hh,hf,_⟩ =>
    ⟨mi,X,Xc,v,ct,ht.of_win hf hc.scrT.nowrap,yt,hw,hw',hv,
      (hh _ (by decide)).trans hn⟩

theorem rawSquares_ct (M : Mont) (n : Nat) :
    RelCT isa (Two RawWindowPre)
      (seqs (List.replicate (n + 1) (M.mm aY aY aY))) (Two RawWindowPre) := by
  have one : RelCT isa (Two RawWindowPre) (M.mm aY aY aY) (Two RawWindowPre) :=
    two_post (Ψ := RawWindowPre)
      (two_map (fun p : XPub => p.ws)
        (fun _ _ ⟨mi,_,_,_,hc,_⟩ => ⟨mi,hc.good,Nat.le_refl _⟩)
        (M.ct (by simp [MmUse]))) (fun _ _ h => rawSquare_post M h)
  induction n with
  | zero => exact one
  | succ n ih => exact RelCT.seq one ih

theorem windowCore_raw_ct (M : Mont) (S : Selector) :
    RelCT isa (Two RawWindowPre)
      (VG.Impl.Rsa.AArch64.WindowFive.windowCore M.mm S.code) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.windowCore
  refine RelCT.seqs_append (by simp) (by simp) ?_
  refine RelCT.seq (rawSquares_ct M 4) ?_
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun p : XPub => GoodW p.ws)
    (two_map id ?_ S.ct) ?_)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h)
      (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide)))
  · rintro p s ⟨mi,X,Xc,v,hc,ht,_,hw,hw',hv,hn⟩
    exact ⟨mi,X,Xc,v,hc,hw,hw',hv,ht.tab,hn⟩
  · rintro p s ⟨mi,X,Xc,v,hc,ht,_,hw,hw',hv,hn⟩
    exact WP.mono (S.ok hc hw hw' hv ht.tab hn) fun t ⟨ct,_⟩ =>
      ⟨mi,ct.good,Nat.le_refl _⟩

end VG.Proof.Bignum.AArch64.WindowFive
