module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16

/-! ### `Weierstrass.X86_64.FastNaf16Timing`, which this module and modules that import it used -/

section

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

theorem fastPrepStep16Of_relCT {step : Prog isa} {n bits : Nat} (hS : FastStepOk16 n bits step)
    (hc : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs (nafPrepPublicN n))) step)
    {base : Addr} {size k j : Nat} (hb : bits+128*n+8≤size) (hj : j<64*n+1)
    (hv : FastNaf.residual 9 k j≤2^(64*n)) :
    RelCT isa (FastPrepPair16 n base size bits k j) step
      (fun s t =>
      FastPrepPair16 n base size bits k (j+fastDelta16 k j) s t ∧
      s.cf=some (decide (j+fastDelta16 k j<64*n+1)) ∧ t.cf=some (decide (j+fastDelta16 k j<64*n+1))) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,_,xs,is,fs,_,_⟩ := hS hp.1 hb hj hv
  obtain ⟨_,_,xt,it,ft,_,_⟩ := hS hp.2 hb hj hv
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨hc _ _ _ _ _ _ trivial trivial hp.public es et,⟨is,it⟩,fs,ft⟩

theorem fastPrepLoop16Of_relCT {step : Prog isa} {n bits : Nat} (hS : FastStepOk16 n bits step)
    (hc : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs (nafPrepPublicN n))) step)
    {base : Addr} {size k : Nat} (hb : bits+128*n+8≤size) (hk : k<2^(64*n)) :
    RelCT isa (FastPrepPair16 n base size bits k 0) (.loop step .b) (fun _ _ => True) := by
  let I := fun m s t => 1≤m ∧ m≤64*n+1 ∧ FastPrepPair16 n base size bits k (64*n+1-m) s t
  have step : ∀ m,RelCT isa (I m) step (fun s t =>
      eval .b s=eval .b t ∧ (eval .b s=some false → True) ∧
      (eval .b s=some true → ∃ n'<m,I n' s t)) := by
    intro m
    by_cases hm : 1≤m ∧ m≤64*n+1
    · have hv := FastNaf.residual_boundB 9 (Nat.le_of_lt hk) (j:=64*n+1-m) (by omega_using [hm])
      have hv' : FastNaf.residual 9 k (64*n+1-m)≤2^(64*n) := Nat.le_trans hv
        (Nat.pow_le_pow_right (by decide) (by omega_using []))
      refine (fastPrepStep16Of_relCT hS hc hb (j:=64*n+1-m) (by omega_using [hm]) hv').mono
        (P':=I m) (fun _ _ h => h.2.2) ?_
      intro s t ⟨hp,fs,ft⟩
      refine ⟨fs.trans ft.symm,fun _ => trivial,fun he => ?_⟩
      have hn' : 64*n+1-m+fastDelta16 k (64*n+1-m)<64*n+1 := by
        change s.cf=some true at he
        rw [fs] at he
        exact of_decide_eq_true (Option.some.inj he)
      have hd : 1≤fastDelta16 k (64*n+1-m) ∧ fastDelta16 k (64*n+1-m)≤9 := by
        unfold fastDelta16; split <;> decide
      refine ⟨m-fastDelta16 k (64*n+1-m),by omega_using [hm, hd],by omega_using [hn'],by omega_using [hm],?_⟩
      rw [show 64*n+1-(m-fastDelta16 k (64*n+1-m))=64*n+1-m+fastDelta16 k (64*n+1-m) from by omega_using [hm, hn']]
      exact hp
    · exact RelCT.of_false (fun _ _ h => hm ⟨h.1,h.2.1⟩)
  exact (RelCT.loop I step (64*n+1)).mono (fun _ _ h => ⟨by omega_using [],by omega_using [],by simpa only [Nat.sub_self] using h⟩)
    (fun _ _ h => h)

/-- The width-nine recoder's timing, of any step that does what `stepN16` does. -/
theorem fastPrep16Of_relCT {step : Prog isa} {n src bits : Nat} {base : Addr} {size : Nat}
    (hn : n=4 ∨ n=6 ∨ n=9) (hS : FastStepOk16 n bits step)
    (hsrc : src+8*n≤size) (hb : bits+128*n+8≤size)
    (hci : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (.block (Naf.initN n src++setConst (16*n+1) bits 0)))
    (hcs : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs (nafPrepPublicN n))) step) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base src n=wordsVal t.mem base src n)
      (.seq (.block (Naf.initN n src++setConst (16*n+1) bits 0)) (.loop step .b)) (fun _ _ => True) := by
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
    exact ⟨hci _ _ _ _ _ _ trivial trivial pub ea eb,ia,ib⟩
  exact (RelCT.seq hi (fastPrepLoop16Of_relCT hS hcs hb (wordsVal_lt ..))) _ _ _ _ _ _
    ⟨hp.1,hp.2.1,rfl,hp.2.2.symm⟩ es et

theorem fastPrep16_relCT {n src bits : Nat} {base : Addr} {size : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hsrc : src+8*n≤size) (hb : bits+128*n+8≤size)
    (hc : FastPrepChecks16 n src bits) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base src n=wordsVal t.mem base src n)
      (Impl.Weierstrass.X86_64.FastNaf.prepN16 n src bits) (fun _ _ => True) :=
  fastPrep16Of_relCT hn (fun hI hb hj hv => fastPrepStep16_ok hn hI hb hj hv) hsrc hb hc.init hc.step

/-- `FastPrepChecks16` for the recoder without branches on the scalar's bits. -/
structure FastPrepChecksB16 (n src bits : Nat) : Prop where
  init : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
    (.block (Naf.initN n src++setConst (16*n+1) bits 0))
  step : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs (nafPrepPublicN n)))
    (Impl.Weierstrass.X86_64.FastNaf.stepB16 n bits)

theorem fastPrepB16_relCT {n src bits : Nat} {base : Addr} {size : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hsrc : src+8*n≤size) (hb : bits+128*n+8≤size) (hc : FastPrepChecksB16 n src bits) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base src n=wordsVal t.mem base src n)
      (Impl.Weierstrass.X86_64.FastNaf.prepB16 n src bits) (fun _ _ => True) :=
  fastPrep16Of_relCT hn (fun hI hb hj hv => fastPrepStepB16_ok hn hI hb hj hv) hsrc hb hc.init hc.step

end VG.Proof.Weierstrass.X86_64

end

end

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

/-- The timing checks of the generator's recoder: of its width (`Joint.Cfg.gw`), or of the one
without branches on the scalar's bits (`Joint.Cfg.recodeB`). -/
def JointPrepGChecks (c : Joint.Cfg) (u : Nat) : Prop :=
  if c.recodeB then FastPrepChecksB16 c.K.M.n u c.gBits else
  if c.gw=9 then FastPrepChecks16 c.K.M.n u c.gBits else FastPrepChecks c.K.M.n u c.gBits 7

/-- The timing checks of the peer's recoder. -/
def JointPrepQChecks (c : Joint.Cfg) (v : Nat) : Prop :=
  if c.recodeB then FastPrepChecksB c.K.M.n v c.K.bits else FastPrepChecks c.K.M.n v c.K.bits 5

/-- The generator's recoder and then the peer's, of each one's timing, and of what the first keeps. -/
theorem jointPrepOf_relCT {c : Joint.Cfg} {base : Addr} {size u v : Nat} {pG pQ : Prog isa}
    (gen : RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n) pG (fun _ _ => True))
    (stage : ∀ a : State,Scr a base size → WP isa pG a (fun b =>
      Scr b base size ∧ wordsVal b.mem base v c.K.M.n=wordsVal a.mem base v c.K.M.n))
    (peer : RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n) pQ (fun _ _ => True)) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
      (.seq pG pQ) (fun _ _ => True) := by
  have first := gen.mono
    (P':=fun (s t : State) => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
    (fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩) (fun _ _ h => h)
  have framed := first.wpDep (F:=fun (s t : State) => Scr t base size ∧
    wordsVal t.mem base v c.K.M.n=wordsVal s.mem base v c.K.M.n) (by
      intro s t ⟨ss,st,_,_⟩
      exact ⟨stage s ss,stage t st⟩)
  apply RelCT.seq (framed.mono
    (Q':=fun (s t : State) => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
    (fun _ _ h => h)
    (fun _ _ ⟨_,_,_,hp,ps,pt⟩ => ⟨ps.1,pt.1,ps.2.trans (hp.2.2.2.trans pt.2.symm)⟩))
  exact peer

/-- The timing of `Joint.prepB`, the recoders without branches on the scalars' bits. -/
theorem jointPrepB_relCT {c : Joint.Cfg} {base : Addr} {size u v : Nat}
    (hn : c.K.M.n=4 ∨ c.K.M.n=6 ∨ c.K.M.n=9) (h9 : c.gw=9)
    (hu : u+8*c.K.M.n≤size) (hv : v+8*c.K.M.n≤size) (hg : c.gBits+jointGSpan c≤size)
    (hq : c.K.bits+64*c.K.M.n+8≤size)
    (hvs : v+8*c.K.M.n≤c.gBits ∨ c.gBits+jointGSpan c≤v)
    (hcG : FastPrepChecksB16 c.K.M.n u c.gBits) (hcQ : FastPrepChecksB c.K.M.n v c.K.bits) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
      (Joint.prepB c u v) (fun _ _ => True) := by
  simp only [jointGSpan,h9,ite_true] at hg hvs
  exact jointPrepOf_relCT (fastPrepB16_relCT (base:=base) hn hu hg hcG)
    (fun a sa => WP.mono (fastPrepDigitsB16_ok hn sa hu hg) (fun _ ⟨_,hk,ho⟩ =>
      ⟨sa.of_keepRegs hk (notin_clobN (by decide) (by decide)),
        ho.wordsVal hvs (by have := sa.nowrap; omega_using [hv, this])⟩))
    (fastPrepB_relCT hn hv hq hcQ)

theorem jointPrep_relCT {c : Joint.Cfg} {base : Addr} {size u v : Nat} (hn : c.K.M.n=4 ∨ c.K.M.n=6 ∨ c.K.M.n=9)
    (hu : u+8*c.K.M.n≤size) (hv : v+8*c.K.M.n≤size) (hg : c.gBits+jointGSpan c≤size)
    (hq : c.K.bits+64*c.K.M.n+8≤size)
    (hvs : v+8*c.K.M.n≤c.gBits ∨ c.gBits+jointGSpan c≤v) (hB : c.recodeB=true → c.gw=9)
    (hcG : JointPrepGChecks c u) (hcQ : JointPrepQChecks c v) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
      (Joint.prep c u v) (fun _ _ => True) := by
  rw [Joint.prep]
  by_cases hr : c.recodeB=true
  · simp only [JointPrepGChecks,JointPrepQChecks,hr,ite_true] at hcG hcQ
    simp only [hr,ite_true]
    exact jointPrepB_relCT hn (hB hr) hu hv hg hq hvs hcG hcQ
  simp only [JointPrepGChecks,JointPrepQChecks,hr,Bool.false_eq_true,ite_false] at hcG hcQ
  simp only [hr,Bool.false_eq_true,ite_false]
  have gen : RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n)
      (if c.gw=9 then Impl.Weierstrass.X86_64.FastNaf.prepN16 c.K.M.n u c.gBits else
        Impl.Weierstrass.X86_64.FastNaf.prepN c.K.M.n u c.gBits 7) (fun _ _ => True) := by
    by_cases h9 : c.gw=9
    · simp only [jointGSpan,h9,ite_true] at hg
      simp only [h9,ite_true] at hcG
      simpa only [h9,ite_true] using fastPrep16_relCT (base:=base) hn hu hg hcG
    · simp only [jointGSpan,h9,ite_false] at hg
      simp only [h9,ite_false] at hcG
      simpa only [h9,ite_false] using fastPrep_relCT (base:=base) hn (Or.inr rfl) hu hg hcG
  have hgs := hg
  have stage (a : State) (sa : Scr a base size) :
      WP isa (if c.gw=9 then Impl.Weierstrass.X86_64.FastNaf.prepN16 c.K.M.n u c.gBits else
        Impl.Weierstrass.X86_64.FastNaf.prepN c.K.M.n u c.gBits 7) a (fun b =>
        Scr b base size ∧ wordsVal b.mem base v c.K.M.n=wordsVal a.mem base v c.K.M.n) := by
    by_cases h9 : c.gw=9
    · simp only [jointGSpan,h9,ite_true] at hgs hvs
      simpa only [h9,ite_true] using
        WP.mono (fastPrepDigits16_ok hn sa hu hgs) (fun _ ⟨_,hk,ho⟩ =>
          ⟨sa.of_keepRegs hk (notin_clobN (by decide) (by decide)),
            ho.wordsVal hvs (by have := sa.nowrap; omega_using [hv, this])⟩)
    · simp only [jointGSpan,h9,ite_false] at hgs hvs
      simpa only [h9,ite_false] using
        WP.mono (fastPrepDigits_ok hn (Or.inr rfl) sa hu hgs) (fun _ ⟨_,hk,ho⟩ =>
          ⟨sa.of_keepRegs hk (notin_clobN (by decide) (by decide)),
            ho.wordsVal hvs (by have := sa.nowrap; omega_using [hv, this])⟩)
  exact jointPrepOf_relCT gen stage (fastPrep_relCT hn (Or.inl rfl) hv hq hcQ)

end VG.Proof.Weierstrass.X86_64
