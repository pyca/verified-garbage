import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator

/-! The recoders preserve the field inputs and the external generator table. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

structure JointPrepLayout (c : Joint.Cfg) (size u v : Nat) : Prop where
  n : c.K.M.n=4 ∨ c.K.M.n=6
  sourceU : u+8*c.K.M.n≤size
  sourceV : v+8*c.K.M.n≤size
  generator : c.gBits+64*c.K.M.n+8≤size
  peer : c.K.bits+64*c.K.M.n+8≤size
  separate : c.gBits+64*c.K.M.n+8≤c.K.bits ∨ c.K.bits+64*c.K.M.n+8≤c.gBits
  keepV : v+8*c.K.M.n≤c.gBits ∨ c.gBits+64*c.K.M.n+8≤v
  field : ∀ x∈winRo c.K,∀ w∈jointPrepRanges c,x+8*c.K.M.n≤w.1 ∨ w.1+w.2≤x
  modulus : ∀ w∈jointPrepRanges c,c.K.M.mo+8*c.K.M.n≤w.1 ∨ w.1+w.2≤c.K.M.mo

theorem Inv.of_unch {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State} {W : List (Nat×Nat)}
    (h : Inv M base size m Sl V E s) (hs : Scr t base size) (hu : Unch base W s.mem t.mem)
    (hb : ∀ x∈V,x+8*M.n≤size)
    (hf : ∀ x∈V,∀ w∈W,x+8*M.n≤w.1 ∨ w.1+w.2≤x)
    (hm : ∀ w∈W,M.mo+8*M.n≤w.1 ∨ w.1+w.2≤M.mo) : Inv M base size m Sl V E t := by
  have same (x : Nat) (hx : x∈V) : wordsVal t.mem base x M.n=wordsVal s.mem base x M.n :=
    hu.wordsVal (hf x hx) (by have := hb x hx; have := h.scr.nowrap; omega)
  exact ⟨hs,h.mod.unch hu hm h.scr.nowrap,h.sl,
    fun x hx => (same x hx) ▸ h.lt x hx,fun x hx => by rw [same x hx]; exact h.val x hx⟩

theorem JointGenerator.keep_prep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat}
    {G : Point C} {row : JointGeneratorRow c.K.M.n C G} {s t : State}
    (h : JointGenerator c C base T size row s) (hL : JointPrepLayout c size u v)
    (hk : KeepRegs (nafPrepClobN c.K.M.n) s t) (hu : Unch base (jointPrepRanges c) s.mem t.mem)
    (hs : t.syms=s.syms) : JointGenerator c C base T size row t := by
  intro a ha hb ho
  apply (h a ha hb ho).keep_of_mem hs hk.rd hk.wr
  intro z hz
  apply hu.far
  intro w hw
  simp only [jointPrepRanges,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · exact Nat.le_trans hL.generator hz
  · exact Nat.le_trans hL.peer hz

theorem jointPrepFields_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat}
    {G : Point C} {row : JointGeneratorRow c.K.M.n C G} {E : Nat → Fe C} {s : State}
    (hL : JointPrepLayout c size u v) (hF : Lay c.K.M size (·∈nafSlots c.K))
    (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s)
    (he : JointGenerator c C base T size row s) :
    WP isa (Joint.prep c u v) s fun t =>
      Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E t ∧
      (∀ j<64*c.K.M.n+1,t.mem (off base (c.gBits+j))=
        FastNaf.byte 7 (wordsVal s.mem base u c.K.M.n) j) ∧
      (∀ j<64*c.K.M.n+1,t.mem (off base (c.K.bits+j))=
        FastNaf.byte 5 (wordsVal s.mem base v c.K.M.n) j) ∧
      JointGenerator c C base T size row t ∧ KeepRegs (nafPrepClobN c.K.M.n) s t ∧
      Unch base (jointPrepRanges c) s.mem t.mem := by
  refine WP.mono_syms (jointPrep_ok hL.n hi.scr hL.sourceU hL.sourceV hL.generator hL.peer hL.separate hL.keepV)
    fun t ⟨st,dg,dq,hk,hu⟩ sy => ?_
  exact ⟨hi.of_unch st hu (fun x hx => hF.le x (hi.sl x hx)) hL.field hL.modulus,
    dg,dq,he.keep_prep hL hk hu sy,hk,hu⟩

end VG.Proof.Weierstrass.X86_64
