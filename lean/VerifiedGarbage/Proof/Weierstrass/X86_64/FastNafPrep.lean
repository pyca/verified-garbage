module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafStep

/-! The sparse recoder of a scalar of `n` words terminates at index `64 n + 1` or later and
produces every required digit. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem fastDelta_bounds {w : Nat} (hw : FastNaf.Width w) (k j : Nat) :
    1≤fastDelta w k j ∧ fastDelta w k j≤7 := by
  unfold fastDelta
  split
  · decide
  · rcases hw with rfl|rfl <;> decide

/-- What a step of the recoder does: `stepN`'s (`fastPrepStep_ok`) and, for width five, `stepB`'s
(`fastPrepStepB_ok`). -/
def FastStepOk (n bits w : Nat) (step : Prog isa) : Prop :=
  ∀ {s : State} {base : Addr} {size k j : Nat},FastPrepState n base size bits w k j s →
    bits+64*n+8≤size → j<64*n+1 → FastNaf.residual w k j≤2^(64*n) →
    WP isa step s fun t =>
      FastPrepState n base size bits w k (j+fastDelta w k j) t ∧
      t.cf=some (decide (j+fastDelta w k j<64*n+1)) ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (64*n+8) s.mem t.mem

/-- The recoder's loop, of any step that does what `stepN` does. -/
theorem fastPrepOf_ok {step : Prog isa} {s : State} {base : Addr} {size n src bits w : Nat}
    (hn : n=4 ∨ n=6 ∨ n=9) (hw : FastNaf.Width w) (hS : FastStepOk n bits w step)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (.seq (.block (Naf.initN n src++setConst (8*n+1) bits 0)) (.loop step .b)) s fun t =>
      (∃ j,64*n+1≤j ∧ j≤64*n+7 ∧ FastPrepState n base size bits w (wordsVal s.mem base src n) j t) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem := by
  let k := wordsVal s.mem base src n
  have hk : k<2^(64*n) := wordsVal_lt ..
  let I (m : Nat) (t : State) := FastPrepState n base size bits w k (64*n+1-m) t ∧
    KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem
  refine WP.seq (WP.mono (fastPrepInit_ok (w:=w) hn hs hsrc hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤64*n+1 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    (64*n+1) a ⟨by omega_using [],by omega_using [],by simpa only [Nat.sub_self] using ia,ka,oa⟩
  have hj : 64*n+1-m<64*n+1 := by omega_using [hm]
  have hv : FastNaf.residual w k (64*n+1-m)≤2^(64*n) := by
    have h := FastNaf.residual_boundB w (Nat.le_of_lt hk) (j:=64*n+1-m) (by omega_using [hm])
    exact Nat.le_trans h (Nat.pow_le_pow_right (by decide) (by omega_using []))
  have hd := fastDelta_bounds hw k (64*n+1-m)
  refine WP.mono (hS hi.1 hb hj hv) fun u ⟨iu,cf,ku,ou⟩ => ?_
  have ki := hi.2.1.trans ku
  have oi := hi.2.2.trans ou
  by_cases he : 64*n+1≤64*n+1-m+fastDelta w k (64*n+1-m)
  · refine Or.inl ⟨?_,⟨_,he,by omega_using [hm, hd],iu⟩,ki,oi⟩
    change u.cf=some false
    rw [cf]
    congr 1
    exact decide_eq_false (by omega_using [he])
  · refine Or.inr ⟨?_,m-fastDelta w k (64*n+1-m),by omega_using [hm, hd],by omega_using [he],by omega_using [hm'],?_,ki,oi⟩
    · change u.cf=some true
      rw [cf]
      congr 1
      exact decide_eq_true (by omega_using [he])
    · rw [show 64*n+1-(m-fastDelta w k (64*n+1-m))=64*n+1-m+fastDelta w k (64*n+1-m) from by omega_using [hm', he]]
      exact iu

theorem fastPrep_ok {s : State} {base : Addr} {size n src bits w : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN n src bits w) s fun t =>
      (∃ j,64*n+1≤j ∧ j≤64*n+7 ∧ FastPrepState n base size bits w (wordsVal s.mem base src n) j t) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem :=
  fastPrepOf_ok hn hw (fun hI hb hj hv => fastPrepStep_ok hn hw hI hb hj hv) hs hsrc hb

theorem fastPrepDigitsOf_ok {step : Prog isa} {s : State} {base : Addr} {size n src bits w : Nat}
    (hn : n=4 ∨ n=6 ∨ n=9) (hw : FastNaf.Width w) (hS : FastStepOk n bits w step)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (.seq (.block (Naf.initN n src++setConst (8*n+1) bits 0)) (.loop step .b)) s fun t =>
      (∀ i<64*n+1,t.mem (off base (bits+i))=FastNaf.byte w (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem := by
  refine WP.mono (fastPrepOf_ok hn hw hS hs hsrc hb) fun t ⟨⟨j,hj,_,hi⟩,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi'
  simpa only [show i<j from by omega_using [hj, hi'],ite_true] using hi.digits i hi'

theorem fastPrepDigits_ok {s : State} {base : Addr} {size n src bits w : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN n src bits w) s fun t =>
      (∀ i<64*n+1,t.mem (off base (bits+i))=FastNaf.byte w (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem :=
  fastPrepDigitsOf_ok hn hw (fun hI hb hj hv => fastPrepStep_ok hn hw hI hb hj hv) hs hsrc hb

/-- `fastPrepDigits_ok` for the recoder of width five without branches on the scalar's bits. -/
theorem fastPrepDigitsB_ok {s : State} {base : Addr} {size n src bits : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepB n src bits) s fun t =>
      (∀ i<64*n+1,t.mem (off base (bits+i))=FastNaf.byte 5 (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem :=
  fastPrepDigitsOf_ok hn (Or.inl rfl) (fun hI hb hj hv => fastPrepStepB_ok hn hI hb hj hv) hs hsrc hb

end VG.Proof.Weierstrass.X86_64
