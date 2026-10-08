import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.Joint

/-! The carry digit followed by `64 n` shared doubles computes the two-scalar sum. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

structure JointLoopKeep (M : Mod) (base : Addr) (W : List Nat) (s t : State) : Prop where
  regs : KeepRegs (.rbx::clob M.n) s t
  unch : Unch base (W.map (·,8*M.n)++[(M.tmp,8*M.n)]) s.mem t.mem

theorem JointLoopKeep.refl (M : Mod) (base : Addr) (W : List Nat) (s : State) :
    JointLoopKeep M base W s s := ⟨⟨fun _ _ => rfl,rfl,rfl⟩,fun _ _ => rfl⟩

theorem JointLoopKeep.trans {M : Mod} {base : Addr} {W : List Nat} {s t u : State}
    (h : JointLoopKeep M base W s t) (h' : JointLoopKeep M base W t u) :
    JointLoopKeep M base W s u := ⟨h.regs.trans h'.regs,fun x hx => (h'.unch x hx).trans (h.unch x hx)⟩

theorem JointLoopKeep.of_prog {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : ProgKeep M base W s t) : JointLoopKeep M base W s t :=
  ⟨(⟨h.gpr,h.rd,h.wr⟩ : KeepRegs (clob M.n) s t).mono (fun _ hr => List.mem_cons_of_mem _ hr),h.unch⟩

theorem JointLoopKeep.of_keeps {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : Keeps [.rbx] s t) : JointLoopKeep M base W s t :=
  ⟨(⟨h.1,h.2.2.1,h.2.2.2⟩ : KeepRegs [.rbx] s t).mono (by simp),fun x _ => congrFun h.2.1 x⟩

section
variable {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p)
    (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)

include hL hm hC ha hOne hOneVal hG hQ

theorem jointDigits_core_ok {j : Nat} {A : Point C} {s : State}
    (hA : onCurve C A=true)
    (hs : JointCore c C base size Q u v (JointGenerator c C base T size row) A s)
    (hj : j<64*c.K.M.n+1) (hb : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (Joint.digits c).inline s fun t => ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row)
        (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C G 7 u j)) t := by
  rw [Joint.digits]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono (jointCachedDigit_ok hL hm hC ha hOne hQ hA hs
    (JointGenerator.workKeep hL.lookup.layout hs.field.mod.tmp) hj hb) fun a ⟨ka,ca⟩ => ?_
  refine WP.mono (jointFixedDigit_ok hL hm hC ha hOne hOneVal hG
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) ca hj
    ((ka.gpr _ (rbx_not_clob _)).trans hb)) fun t ⟨kt,ct⟩ => ⟨ka.trans kt,ct⟩

variable {double : Prog isa}
    (hdouble : ∀ A s,onCurve C A=true →
      JointCore c C base size Q u v (JointGenerator c C base T size row) A s →
      WP isa double.inline s fun t => ProgKeep c.K.M base (jointWork c) s t ∧
        JointCore c C base size Q u v (JointGenerator c C base T size row) (add A A) t)

include hdouble

theorem jointStep_core_ok {j : Nat} {s : State} (hj : j<64*c.K.M.n)
    (hs : JointCore c C base size Q u v (JointGenerator c C base T size row) (jointPoint G Q u v (j+1)) s)
    (hb : s.gpr .rbx=BitVec.ofNat 64 (j+1)) :
    WP isa (Joint.step c double).inline s fun t => JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (jointPoint G Q u v j) t ∧
      t.gpr .rbx=BitVec.ofNat 64 j ∧ t.zf=some (decide (j=0)) := by
  have := hL.lookup.layout.n
  rw [Joint.step]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono_syms (decRbx_ok s (by omega) (by omega) hb) fun a ⟨ab,ka⟩ sa => ?_
  have ca := hs.of_keeps ka (by decide) (fun n hn hn' ho => (hs.external n hn hn' ho).of_keeps ka sa)
  apply WP.seq
  refine WP.mono (hdouble _ a (jointPoint_curve hC hG hQ u v (j+1)) ca) fun b ⟨kb,cb⟩ => ?_
  have bb : b.gpr .rbx=BitVec.ofNat 64 j := by
    rw [kb.gpr _ (rbx_not_clob _),ab,Nat.add_sub_cancel]
  apply WP.seq
  refine WP.mono (jointDigits_core_ok hL hm hC ha hOne hOneVal hG hQ
    (hC.onCurve_add (jointPoint_curve hC hG hQ u v (j+1)) (jointPoint_curve hC hG hQ u v (j+1)))
    cb (by omega) bb) fun d ⟨kd,cd⟩ => ?_
  rw [jointPoint_step hC hG hQ] at cd
  have db : d.gpr .rbx=BitVec.ofNat 64 j := (kd.gpr _ (rbx_not_clob _)).trans bb
  refine WP.mono_syms (testRbx_ok d (by omega) db) fun t ⟨tz,kt⟩ st => ?_
  have ct := cd.of_keeps kt (by decide) (fun n hn hn' ho => (cd.external n hn hn' ho).of_keeps kt st)
  have kp : ProgKeep c.K.M base (jointWork c) d t := jointKeeps_prog kt (by simp)
  exact ⟨(JointLoopKeep.of_keeps ka).trans (JointLoopKeep.of_prog (kb.trans (kd.trans kp))),
    ct,(kt.1 .rbx (by simp)).trans db,tz⟩

theorem jointLoop_core_ok {s : State}
    (hs : JointCore c C base size Q u v (JointGenerator c C base T size row)
      (jointPoint G Q u v (64*c.K.M.n)) s)
    (hb : s.gpr .rbx=BitVec.ofNat 64 (64*c.K.M.n)) :
    WP isa (Code.loop (Joint.step c double) .ne).inline s fun t => JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 := by
  let I := fun j t => JointLoopKeep c.K.M base (jointWork c) s t ∧
    JointCore c C base size Q u v (JointGenerator c C base T size row) (jointPoint G Q u v j) t ∧
    t.gpr .rbx=BitVec.ofNat 64 j
  have := hL.lookup.layout.n
  apply countLoop_ok (Inv:=I) (n:=64*c.K.M.n)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,ab⟩ := hi
    have he : j-1+1=j := by omega
    refine WP.mono (jointStep_core_ok hL hm hC ha hOne hOneVal hG hQ hdouble
      (by omega) (he.symm ▸ ca) (he.symm ▸ ab)) fun t ⟨kt,ct,tb,tz⟩ => ⟨⟨ka.trans kt,ct,tb⟩,tz⟩
  · intro t ht
    obtain ⟨kt,ct,tb⟩ := ht
    rw [jointPoint_zero] at ct
    exact ⟨kt,ct,tb⟩
  · omega
  · exact ⟨JointLoopKeep.refl _ _ _ _,hs,hb⟩

theorem jointRun_core_ok {s : State} (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n))
    (hs : JointCore c C base size Q u v (JointGenerator c C base T size row) .infinity s)
    (hb : s.gpr .rbx=BitVec.ofNat 64 (64*c.K.M.n)) :
    WP isa (Joint.run c double).inline s fun t => JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 := by
  rw [Joint.run]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono (jointDigits_core_ok hL hm hC ha hOne hOneVal hG hQ (A:=.infinity)
    rfl hs (by omega) hb) fun a ⟨ka,ca⟩ => ?_
  have he := jointPoint_step hC hG hQ u v (64*c.K.M.n)
  rw [jointPoint_topB G Q hu hv] at he
  change add (add .infinity (FastNaf.point C Q 5 v (64*c.K.M.n)))
    (FastNaf.point C G 7 u (64*c.K.M.n))=jointPoint G Q u v (64*c.K.M.n) at he
  rw [he] at ca
  refine WP.mono (jointLoop_core_ok hL hm hC ha hOne hOneVal hG hQ hdouble ca
    ((ka.gpr _ (rbx_not_clob _)).trans hb)) fun t ⟨kt,ct,tb⟩ =>
    ⟨(JointLoopKeep.of_prog ka).trans kt,ct,tb⟩
end
end VG.Proof.Weierstrass.X86_64
