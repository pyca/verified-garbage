import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafStep

/-! The sparse recoder terminates at index 257 or later and produces every required digit. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem fastDelta_bounds {w : Nat} (hw : FastNaf.Width w) (k j : Nat) :
    1≤fastDelta w k j ∧ fastDelta w k j≤7 := by
  unfold fastDelta
  split
  · decide
  · rcases hw with rfl|rfl <;> decide

theorem fastPrep_ok {s : State} {base : Addr} {size src bits w : Nat}
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+32≤size) (hb : bits+264≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prep src bits w) s fun t =>
      (∃ j,257≤j ∧ j≤263 ∧ FastPrepState base size bits w (wordsVal s.mem base src 4) j t) ∧
      KeepRegs nafPrepClob s t ∧ Outside base bits 264 s.mem t.mem := by
  let k := wordsVal s.mem base src 4
  have hk : k<2^256 := wordsVal_lt ..
  let I (m : Nat) (t : State) := FastPrepState base size bits w k (257-m) t ∧
    KeepRegs nafPrepClob s t ∧ Outside base bits 264 s.mem t.mem
  rw [Impl.Weierstrass.X86_64.FastNaf.prep]
  refine WP.seq (WP.mono (fastPrepInit_ok (w:=w) hs hsrc hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤257 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    257 a ⟨by decide,by decide,ia,ka,oa⟩
  have hj : 257-m<257 := by omega
  have hv : FastNaf.residual w k (257-m)≤2^256 := by
    have h := FastNaf.residual_bound w (Nat.le_of_lt hk) (j:=257-m) (by omega)
    exact Nat.le_trans h (Nat.pow_le_pow_right (by decide) (by omega))
  have hd := fastDelta_bounds hw k (257-m)
  refine WP.mono (fastPrepStep_ok hw hi.1 hb hj hv) fun u ⟨iu,cf,ku,ou⟩ => ?_
  have ki := hi.2.1.trans ku
  have oi := hi.2.2.trans ou
  by_cases he : 257≤257-m+fastDelta w k (257-m)
  · refine Or.inl ⟨?_,⟨_,he,by omega,iu⟩,ki,oi⟩
    change u.cf=some false
    rw [cf]
    congr 1
    exact decide_eq_false (by omega)
  · refine Or.inr ⟨?_,m-fastDelta w k (257-m),by omega,by omega,by omega,?_,ki,oi⟩
    · change u.cf=some true
      rw [cf]
      congr 1
      exact decide_eq_true (by omega)
    · rw [show 257-(m-fastDelta w k (257-m))=257-m+fastDelta w k (257-m) from by omega]
      exact iu

theorem fastPrepDigits_ok {s : State} {base : Addr} {size src bits w : Nat}
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+32≤size) (hb : bits+264≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prep src bits w) s fun t =>
      (∀ i<257,t.mem (off base (bits+i))=FastNaf.byte w (wordsVal s.mem base src 4) i) ∧
      KeepRegs nafPrepClob s t ∧ Outside base bits 264 s.mem t.mem := by
  refine WP.mono (fastPrep_ok hw hs hsrc hb) fun t ⟨⟨j,hj,_,hi⟩,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi'
  simpa only [show i<j from by omega,ite_true] using hi.digits i hi'

end VG.Proof.Weierstrass.X86_64
