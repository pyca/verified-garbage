module

import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoopTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The carry digit followed by `64 n` shared doubles computes the two-scalar sum. -/

@[expose] public section

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
  ⟨(⟨h.1,h.2.2.1,h.2.2.2⟩ : KeepRegs [.rbx] s t).mono (by regions_sub),fun x _ => congrFun h.2.1 x⟩

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

theorem jointStep_core_ok (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) {j : Nat} {s : State}
    (hj : j<Joint.top c)
    (hs : JointCore c C base size Q u v (JointGenerator c C base T size row) (jointPoint G Q u v (j+1)) s)
    (hb : s.gpr .rbx=BitVec.ofNat 64 (j+1)) :
    WP isa (Joint.step c double).inline s fun t => JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (jointPoint G Q u v j) t ∧
      t.gpr .rbx=BitVec.ofNat 64 j ∧ t.zf=some (decide (j=0)) := by
  have := hL.lookup.layout.n
  have ht := joint_top_le c
  have hA := jointPoint_curve hC hG hQ u v (j+1)
  rw [Joint.step]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono_syms (decRbx_ok s (by omega) (by omega) hb) fun a ⟨ab,ka⟩ sa => ?_
  have ab' : a.gpr .rbx=BitVec.ofNat 64 j := by rw [ab, Nat.add_sub_cancel]
  have ca := hs.of_keeps ka (by decide) (fun n hn hn' ho => (hs.external n hn hn' ho).of_keeps ka sa)
  -- The doubling, but where `R` is `O` (`j = 64 n`, the first iteration).
  have hg : WP isa (Joint.guardDouble c double).inline a fun b =>
      ProgKeep c.K.M base (jointWork c) a b ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row)
        (add (jointPoint G Q u v (j+1)) (jointPoint G Q u v (j+1))) b ∧
      b.gpr .rbx=BitVec.ofNat 64 j := by
    rw [Joint.guardDouble]
    split
    · exact WP.mono (hdouble _ a hA ca) fun b ⟨kb,cb⟩ =>
        ⟨kb,cb,(kb.gpr _ (rbx_not_clob _)).trans ab'⟩
    simp only [Code.inline]
    refine WP.seq (WP.mono_syms (cmpRbxImm_ok a (k:=64*c.K.M.n) (by omega) (by omega) ab')
      fun a' ⟨az,ka'⟩ sa' => ?_)
    have ca' := ca.of_keeps ka' (by decide) (fun n hn hn' ho => (ca.external n hn hn' ho).of_keeps ka' sa')
    have kp' : ProgKeep c.K.M base (jointWork c) a a' := jointKeeps_prog ka' (by simp)
    have ab'' : a'.gpr .rbx=BitVec.ofNat 64 j := (ka'.1 .rbx (by simp)).trans ab'
    refine WP.ite (decide (j=64*c.K.M.n)) az (fun h => ?_) (fun _ => ?_)
    · apply WP.block_nil
      have hj' : j=64*c.K.M.n := of_decide_eq_true h
      have e : add (jointPoint G Q u v (j+1)) (jointPoint G Q u v (j+1))=jointPoint G Q u v (j+1) := by
        rw [hj', jointPoint_topB G Q hu hv]; rfl
      exact ⟨kp', by rw [e]; exact ca', ab''⟩
    · exact WP.mono (hdouble _ a' hA ca') fun b ⟨kb,cb⟩ =>
        ⟨kp'.trans kb, cb, (kb.gpr _ (rbx_not_clob _)).trans ab''⟩
  apply WP.seq
  refine WP.mono hg fun b ⟨kb,cb,bb⟩ => ?_
  apply WP.seq
  refine WP.mono (jointDigits_core_ok hL hm hC ha hOne hOneVal hG hQ
    (hC.onCurve_add hA hA) cb (by omega) bb) fun d ⟨kd,cd⟩ => ?_
  rw [jointPoint_step hC hG hQ] at cd
  have db : d.gpr .rbx=BitVec.ofNat 64 j := (kd.gpr _ (rbx_not_clob _)).trans bb
  refine WP.mono_syms (testRbx_ok d (by omega) db) fun t ⟨tz,kt⟩ st => ?_
  have ct := cd.of_keeps kt (by decide) (fun n hn hn' ho => (cd.external n hn hn' ho).of_keeps kt st)
  have kp : ProgKeep c.K.M base (jointWork c) d t := jointKeeps_prog kt (by simp)
  exact ⟨(JointLoopKeep.of_keeps ka).trans (JointLoopKeep.of_prog (kb.trans (kd.trans kp))),
    ct,(kt.1 .rbx (by simp)).trans db,tz⟩

theorem jointLoop_core_ok (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) {s : State}
    (hs : JointCore c C base size Q u v (JointGenerator c C base T size row)
      (jointPoint G Q u v (Joint.top c)) s)
    (hb : s.gpr .rbx=BitVec.ofNat 64 (Joint.top c)) :
    WP isa (Code.loop (Joint.step c double) .ne).inline s fun t => JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 := by
  let I := fun j t => JointLoopKeep c.K.M base (jointWork c) s t ∧
    JointCore c C base size Q u v (JointGenerator c C base T size row) (jointPoint G Q u v j) t ∧
    t.gpr .rbx=BitVec.ofNat 64 j
  have := hL.lookup.layout.n
  have := joint_top_le c
  apply countLoop_ok (Inv:=I) (n:=Joint.top c)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,ab⟩ := hi
    have he : j-1+1=j := by omega
    refine WP.mono (jointStep_core_ok hL hm hC ha hOne hOneVal hG hQ hdouble hu hv
      (by omega) (he.symm ▸ ca) (he.symm ▸ ab)) fun t ⟨kt,ct,tb,tz⟩ => ⟨⟨ka.trans kt,ct,tb⟩,tz⟩
  · intro t ht
    obtain ⟨kt,ct,tb⟩ := ht
    rw [jointPoint_zero] at ct
    exact ⟨kt,ct,tb⟩
  · omega
  · exact ⟨JointLoopKeep.refl _ _ _ _,hs,hb⟩

theorem jointRun_core_ok {s : State} (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n))
    (hs : JointCore c C base size Q u v (JointGenerator c C base T size row) .infinity s)
    (hb : s.gpr .rbx=BitVec.ofNat 64 (Joint.top c)) :
    WP isa (Joint.run c double).inline s fun t => JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 := by
  rw [Joint.run]
  split
  · rename_i hp
    rw [joint_top_peel hp] at hb
    simp only [Code.inline]
    apply WP.seq
    refine WP.mono (jointDigits_core_ok hL hm hC ha hOne hOneVal hG hQ (A:=.infinity)
      rfl hs (by omega) hb) fun a ⟨ka,ca⟩ => ?_
    have he := jointPoint_step hC hG hQ u v (64*c.K.M.n)
    rw [jointPoint_topB G Q hu hv] at he
    change add (add .infinity (FastNaf.point C Q 5 v (64*c.K.M.n)))
      (FastNaf.point C G 7 u (64*c.K.M.n))=jointPoint G Q u v (64*c.K.M.n) at he
    rw [he,← joint_top_peel hp] at ca
    refine WP.mono (jointLoop_core_ok hL hm hC ha hOne hOneVal hG hQ hdouble hu hv ca
      ((ka.gpr _ (rbx_not_clob _)).trans (hb.trans (by rw [joint_top_peel hp])))) fun t ⟨kt,ct,tb⟩ =>
      ⟨(JointLoopKeep.of_prog ka).trans kt,ct,tb⟩
  · rename_i hp
    have hp' : c.peel=false := by simpa using hp
    rw [← jointPoint_topB G Q hu hv,← joint_top_guard hp'] at hs
    exact jointLoop_core_ok hL hm hC ha hOne hOneVal hG hQ hdouble hu hv hs hb
end
end VG.Proof.Weierstrass.X86_64
