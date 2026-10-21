module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming

/-! The width-nine recoder's branches depend on the public scalar and its public digit index. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

structure FastPrepChecks16 (n src bits : Nat) : Prop where
  init : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
    (.block (Naf.initN n src++setConst (16*n+1) bits 0))
  step : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs (nafPrepPublicN n)))
    (Impl.Weierstrass.X86_64.FastNaf.stepN16 n bits)

abbrev FastPrepPair16 (n : Nat) (base : Addr) (size bits k j : Nat) (s t : State) : Prop :=
  FastPrepState16 n base size bits k j s ∧ FastPrepState16 n base size bits k j t

theorem FastPrepPair16.public {n : Nat} {base : Addr} {size bits k j : Nat} {s t : State}
    (h : FastPrepPair16 n base size bits k j s t) :
    X86_64.Taint.Agree (Taint.ofRegs (nafPrepPublicN n)) s t := by
  have hv := regsVal_inj (h.1.value.trans h.2.value.symm)
  apply Taint.agree_ofRegs
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.1.scr.rdi.trans h.2.scr.rdi.symm
    · exact h.1.count.trans h.2.count.symm
  · exact hv r hr

theorem fastPrepStep16_relCT {n src bits : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hc : FastPrepChecks16 n src bits)
    {base : Addr} {size k j : Nat} (hb : bits+128*n+8≤size) (hj : j<64*n+1)
    (hv : FastNaf.residual 9 k j≤2^(64*n)) :
    RelCT isa (FastPrepPair16 n base size bits k j) (Impl.Weierstrass.X86_64.FastNaf.stepN16 n bits)
      (fun s t =>
      FastPrepPair16 n base size bits k (j+fastDelta16 k j) s t ∧
      s.cf=some (decide (j+fastDelta16 k j<64*n+1)) ∧ t.cf=some (decide (j+fastDelta16 k j<64*n+1))) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,fs,_,_⟩ := fastPrepStep16_ok hn hp.1 hb hj hv
  obtain ⟨_,_,xt,it,ft,_,_⟩ := fastPrepStep16_ok hn hp.2 hb hj hv
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hc.step _ _ _ _ _ _ trivial trivial hp.public es et,⟨is,it⟩,fs,ft⟩

theorem fastPrepLoop16_relCT {n src bits : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hc : FastPrepChecks16 n src bits)
    {base : Addr} {size k : Nat} (hb : bits+128*n+8≤size) (hk : k<2^(64*n)) :
    RelCT isa (FastPrepPair16 n base size bits k 0)
      (.loop (Impl.Weierstrass.X86_64.FastNaf.stepN16 n bits) .b) (fun _ _ => True) := by
  let I := fun m s t => 1≤m ∧ m≤64*n+1 ∧ FastPrepPair16 n base size bits k (64*n+1-m) s t
  have step : ∀ m,RelCT isa (I m) (Impl.Weierstrass.X86_64.FastNaf.stepN16 n bits) (fun s t =>
      eval .b s=eval .b t ∧ (eval .b s=some false → True) ∧
      (eval .b s=some true → ∃ n'<m,I n' s t)) := by
    intro m
    by_cases hm : 1≤m ∧ m≤64*n+1
    · have hv := FastNaf.residual_boundB 9 (Nat.le_of_lt hk) (j:=64*n+1-m) (by omega)
      have hv' : FastNaf.residual 9 k (64*n+1-m)≤2^(64*n) := Nat.le_trans hv
        (Nat.pow_le_pow_right (by decide) (by omega))
      refine (fastPrepStep16_relCT hn hc hb (j:=64*n+1-m) (by omega) hv').mono
        (P':=I m) (fun _ _ h => h.2.2) ?_
      intro s t ⟨hp,fs,ft⟩
      refine ⟨fs.trans ft.symm,fun _ => trivial,fun he => ?_⟩
      have hn' : 64*n+1-m+fastDelta16 k (64*n+1-m)<64*n+1 := by
        change s.cf=some true at he
        rw [fs] at he
        exact of_decide_eq_true (Option.some.inj he)
      have hd : 1≤fastDelta16 k (64*n+1-m) ∧ fastDelta16 k (64*n+1-m)≤9 := by
        unfold fastDelta16; split <;> decide
      refine ⟨m-fastDelta16 k (64*n+1-m),by omega,by omega,by omega,?_⟩
      rw [show 64*n+1-(m-fastDelta16 k (64*n+1-m))=64*n+1-m+fastDelta16 k (64*n+1-m) from by omega]
      exact hp
    · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)
  exact (RelCT.loop I step (64*n+1)).mono (fun _ _ h => ⟨by omega,by omega,by simpa only [Nat.sub_self] using h⟩)
    (fun _ _ h => h)

theorem fastPrep16_relCT {n src bits : Nat} {base : Addr} {size : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hsrc : src+8*n≤size) (hb : bits+128*n+8≤size)
    (hc : FastPrepChecks16 n src bits) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base src n=wordsVal t.mem base src n)
      (Impl.Weierstrass.X86_64.FastNaf.prepN16 n src bits) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  have hi : RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧
      wordsVal a.mem base src n=wordsVal s.mem base src n ∧
      wordsVal b.mem base src n=wordsVal s.mem base src n)
      (.block (Naf.initN n src++setConst (16*n+1) bits 0))
      (FastPrepPair16 n base size bits (wordsVal s.mem base src n) 0) := by
    intro a b ta tb a' b' hab ea eb
    obtain ⟨_,_,xa,ia,_,_⟩ := fastPrepInit16_ok hn hab.1 hsrc hb
    obtain ⟨_,_,xb,ib,_,_⟩ := fastPrepInit16_ok hn hab.2.1 hsrc hb
    obtain ⟨_,rfl⟩ := Exec.det ea xa
    obtain ⟨_,rfl⟩ := Exec.det eb xb
    rw [hab.2.2.1] at ia
    rw [hab.2.2.2] at ib
    have pub : X86_64.Taint.Agree (Taint.ofRegs [.rdi]) a b := by
      apply Taint.agree_ofRegs
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hab.1.rdi.trans hab.2.1.rdi.symm
    exact ⟨hc.init _ _ _ _ _ _ trivial trivial pub ea eb,ia,ib⟩
  rw [Impl.Weierstrass.X86_64.FastNaf.prepN16] at es et
  exact (RelCT.seq hi (fastPrepLoop16_relCT hn hc hb (wordsVal_lt ..))) _ _ _ _ _ _
    ⟨hp.1,hp.2.1,rfl,hp.2.2.symm⟩ es et

end VG.Proof.Weierstrass.X86_64
