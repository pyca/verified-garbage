module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBitCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByte

/-! Constant time through all tail bits, with a public pending-bit counter. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.WindowFive (takeBit tailBits)

theorem takeBit_ready (W : Window) {i : Nat} (hi : i < 8) {p : XPub × Nat} {s : State}
    (h : TailPre p s) :
    WP isa (takeBit W.code i) s (TailPre (p.1, (p.2 + 1) % 5)) := by
  obtain ⟨mi,X,Xc,v,V,hc,ht,hy,hw,hw',hb,hv,hV,hn,bc,byc,hR⟩ := h
  refine WP.mono (takeBit_pending W hc ht hw hw' hR
    (b := p.2) (K := v) (x := 0) (Q := False)
    ⟨0,v,hb,hv,by simp,hy,fun h => h.elim,hn,bc⟩ hi hV byc)
    fun t ⟨ct,tt,pt,_,_,hh⟩ => ?_
  obtain ⟨E,v',hb',hv',_,hy',_,hn',bc'⟩ := pt
  exact ⟨mi,X,Xc,v',V,ct,tt,hy',hw,hw',hb',hv',hV,hn',bc',
    (hh _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans byc,hR⟩

theorem tailBits_ready (W : Window) (n : Nat) (hn : n ≤ 8) {p : XPub × Nat} {s : State}
    (h : TailPre p s) :
    WP isa (tailBits W.code n) s (TailPre (p.1, (p.2 + n) % 5)) := by
  induction n with
  | zero =>
    apply WP.block_nil
    have hb : p.2 < 5 := by obtain ⟨_,_,_,_,_,_,_,_,_,_,hb,_⟩ := h; exact hb
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt hb] using h
  | succ n ih =>
    unfold tailBits
    refine WP.seq (WP.mono (ih (by omega)) fun u hu => ?_)
    refine WP.mono (takeBit_ready W (by omega) hu) fun t ht => ?_
    have he : ((p.2 + n) % 5 + 1) % 5 = (p.2 + (n + 1)) % 5 := by omega
    simpa only [he] using ht

theorem tailBits_ct (W : Window) (n : Nat) (hn : n ≤ 8) :
    RelCT isa (Two TailPre) (tailBits W.code n) (fun _ _ => True) := by
  induction n with
  | zero =>
    apply two_taint [] (hc := .block [])
    · intro _ _ _ _ _ r hr; simp at hr
    · rfl
  | succ n ih =>
    unfold tailBits
    refine RelCT.seq (two_post (Ψ := fun p s => TailPre (p.1, (p.2 + n) % 5) s)
      (ih (by omega)) (fun _ _ h => tailBits_ready W n (by omega) h)) ?_
    exact two_map (fun p : XPub × Nat => (p.1, (p.2 + n) % 5))
      (fun _ _ h => h) (takeBit_ct W (by omega))

end VG.Proof.Bignum.AArch64.WindowFive
