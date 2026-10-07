import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafStep

/-! The sparse recoder of a scalar of `n` words terminates at index `64 n + 1` or later and
produces every required digit. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem fastDelta_bounds {w : Nat} (hw : FastNaf.Width w) (k j : Nat) :
    1≤fastDelta w k j ∧ fastDelta w k j≤7 := by
  unfold fastDelta
  split
  · decide
  · rcases hw with rfl|rfl <;> decide

theorem fastPrep_ok {s : State} {base : Addr} {size n src bits w : Nat} (hn : n=4 ∨ n=6)
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN n src bits w) s fun t =>
      (∃ j,64*n+1≤j ∧ j≤64*n+7 ∧ FastPrepState n base size bits w (wordsVal s.mem base src n) j t) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem := by
  let k := wordsVal s.mem base src n
  have hk : k<2^(64*n) := wordsVal_lt ..
  let I (m : Nat) (t : State) := FastPrepState n base size bits w k (64*n+1-m) t ∧
    KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem
  rw [Impl.Weierstrass.X86_64.FastNaf.prepN]
  refine WP.seq (WP.mono (fastPrepInit_ok (w:=w) hn hs hsrc hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤64*n+1 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    (64*n+1) a ⟨by omega,by omega,by simpa only [Nat.sub_self] using ia,ka,oa⟩
  have hj : 64*n+1-m<64*n+1 := by omega
  have hv : FastNaf.residual w k (64*n+1-m)≤2^(64*n) := by
    have h := FastNaf.residual_boundB w (Nat.le_of_lt hk) (j:=64*n+1-m) (by omega)
    exact Nat.le_trans h (Nat.pow_le_pow_right (by decide) (by omega))
  have hd := fastDelta_bounds hw k (64*n+1-m)
  refine WP.mono (fastPrepStep_ok hn hw hi.1 hb hj hv) fun u ⟨iu,cf,ku,ou⟩ => ?_
  have ki := hi.2.1.trans ku
  have oi := hi.2.2.trans ou
  by_cases he : 64*n+1≤64*n+1-m+fastDelta w k (64*n+1-m)
  · refine Or.inl ⟨?_,⟨_,he,by omega,iu⟩,ki,oi⟩
    change u.cf=some false
    rw [cf]
    congr 1
    exact decide_eq_false (by omega)
  · refine Or.inr ⟨?_,m-fastDelta w k (64*n+1-m),by omega,by omega,by omega,?_,ki,oi⟩
    · change u.cf=some true
      rw [cf]
      congr 1
      exact decide_eq_true (by omega)
    · rw [show 64*n+1-(m-fastDelta w k (64*n+1-m))=64*n+1-m+fastDelta w k (64*n+1-m) from by omega]
      exact iu

theorem fastPrepDigits_ok {s : State} {base : Addr} {size n src bits w : Nat} (hn : n=4 ∨ n=6)
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN n src bits w) s fun t =>
      (∀ i<64*n+1,t.mem (off base (bits+i))=FastNaf.byte w (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem := by
  refine WP.mono (fastPrep_ok hn hw hs hsrc hb) fun t ⟨⟨j,hj,_,hi⟩,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi'
  simpa only [show i<j from by omega,ite_true] using hi.digits i hi'

end VG.Proof.Weierstrass.X86_64
