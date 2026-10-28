module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupCT
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDigit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep

/-! Constant-time composition of a full group. Its value remains secret. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowFive (groupDigit appliedGroup)

theorem appliedStep_ct (W : Window) (shift : Nat) (hs : shift < 64) :
    RelCT isa (Two GroupPre) (.seq (.block (groupDigit shift)) W.code)
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := WindowPre)
    (two_map (fun p : XPub => off p.B p.o) ?_ (groupDigit_ct shift))
    (fun _ _ h => digit_ready shift hs h)) (two_map id (fun _ _ ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',_,hv,hn⟩ =>
      ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩) W.ct)
  rintro p s ⟨_, _, _, _, hc, _⟩
  exact hc.good.x0

theorem appliedStep_post (W : Window) (shift : Nat) (hs : shift < 64)
    {p : XPub} {s : State} (h : GroupPre p s) :
    WP isa (.seq (.block (groupDigit shift)) W.code) s (GroupPre p) := by
  obtain ⟨mi, X, Xc, V, hc, ht, hy, hw, hw', hR, hV', hV⟩ := h
  exact WP.mono (appliedStep_ok W (Q := False) (x := 0) (E := 0)
    hc ht hw hw' hR hy False.elim hV hV' hs)
    fun t ⟨ct, tt, yt, _, hVt, _⟩ => ⟨mi, X, Xc, V, ct, tt, yt, hw, hw', hR, hV', hVt⟩

theorem appliedGroup_ct (W : Window) (n : Nat) (hn : n ≤ 8) :
    RelCT isa (Two GroupPre) (appliedGroup W.code n) (fun _ _ => True) := by
  induction n with
  | zero =>
    exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (hc := .block []) rfl
  | succ n ih =>
    exact RelCT.seq (two_post (appliedStep_ct W (5 * n) (by omega))
      (fun _ _ h => appliedStep_post W (5 * n) (by omega) h)) (ih (by omega))

end VG.Proof.Bignum.AArch64.WindowFive
