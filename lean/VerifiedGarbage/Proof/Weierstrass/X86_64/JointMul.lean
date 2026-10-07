import VerifiedGarbage.Proof.Weierstrass.X86_64.JointDoubler
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields

/-!
# The joint two-scalar multiplication

`[u]G + [v]Q` by the joint loop, from the scalars' words: both recoders, the
table of odd multiples of `Q` with its cached `Z²`, `Z³`, then the loop with
the curve's doubler (`JointDoubler`), for any curve and number of words.
-/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open Spec.Weierstrass

/-- The loop's input after both recoders: `Q` in `P`, zero, both tables of
digits and the generator's row. -/
structure JointWindowInput (c : Joint.Cfg) (C : Curve) (base T : Addr) (size u v : Nat)
    {G : Point C} (Q : Point C) (row : JointGeneratorRow c.K.M.n C G) (s : State) : Prop where
  point : InvJ C (tmv C c.K.M.n base s c.K.P.x)
    (tmv C c.K.M.n base s c.K.P.y) (tmv C c.K.M.n base s c.K.P.z) Q
  zero : tmv C c.K.M.n base s c.K.zero=0
  peer : ∀ i<64*c.K.M.n+1,s.mem (off base (c.K.bits+i))=FastNaf.byte 5 v i
  generator : ∀ i<64*c.K.M.n+1,s.mem (off base (c.gBits+i))=FastNaf.byte 7 u i
  external : JointGenerator c C base T size row s

theorem jointMulRun_ok {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n))
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) .infinity s)
    (hb : s.gpr .rbx=BitVec.ofNat 64 (64*c.K.M.n)) :
    WP isa (Joint.run c double) s fun t =>
      JointLoopKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 :=
  jointRun_core_ok hL hm hC ha hOne hOneVal hG hQ
    (fun _ _ hp hi => hD.ok (JointGenerator.workKeep hL.lookup.layout hi.field.mod.tmp) hp hi) hu hv h hb

theorem jointMulWindow_ok {c : Joint.Cfg} {C : Curve} {double : Prog isa} {base T : Addr} {size u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G} {s : State}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (ha : AM3 C) (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n))
    (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) (tmv C c.K.M.n base s) s)
    (hw : JointWindowInput c C base T size u v Q row s) :
    WP isa (Joint.window c double) s fun t =>
      JointLoopKeep c.K.M base (jointInitWork c++jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add (mul u G) (mul v Q)) t ∧
      t.gpr .rbx=0 := by
  rw [Joint.window]
  apply WP.assoc
  apply WP.seq
  refine WP.mono (jointTables_ok hInit hm hC ha hOne hQ hi hw.point hw.zero hw.peer hw.generator hw.external)
    fun a ⟨ka,ia,sa,ea⟩ => ?_
  apply WP.seq
  refine WP.mono (jointSeed_ok hL.lookup.layout hOne ia sa ea) fun b ⟨kb,cb,bb⟩ => ?_
  refine WP.mono (jointMulRun_ok hL hm hC ha hD hOne hOneVal hG hQ hu hv cb bb)
    fun t ⟨kt,ct,tb⟩ => ?_
  exact ⟨(ka.mono (fun _ h => List.mem_append_left _ h)).trans
    ((kb.trans kt).mono (fun _ h => List.mem_append_right _ h)),ct,tb⟩

theorem jointMulPrep_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size srcU srcV u v : Nat}
    {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G}
    {E : Nat → Fin C.p} {s : State}
    (hL : JointPrepLayout c size srcU srcV) (hF : Lay c.K.M size (·∈nafSlots c.K))
    (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s)
    (hp : InvJ C (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q)
    (hz : E c.K.zero=0) (he : JointGenerator c C base T size row s)
    (hu : wordsVal s.mem base srcU c.K.M.n=u) (hv : wordsVal s.mem base srcV c.K.M.n=v) :
    WP isa (Joint.prep c srcU srcV) s fun t =>
      Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E t ∧
      JointWindowInput c C base T size u v Q row t ∧ KeepRegs (nafPrepClobN c.K.M.n) s t ∧
      Unch base (jointPrepRanges c) s.mem t.mem := by
  refine WP.mono (jointPrepFields_ok (C:=C) hL hF hi he)
    fun t ⟨it,dg,dq,gt,hk,ht⟩ => ?_
  rw [hu] at dg
  rw [hv] at dq
  have pv : ∀ x∈jacCoords c.K.P,x∈winRo c.K := by
    intro x hx
    simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact ⟨it,⟨it.point_tmv pv hp,(it.val _ (by simp [winRo])).trans hz,dq,dg,gt⟩,hk,ht⟩

theorem jointMul_ok {C : Curve} {c : Joint.Cfg} {double : Prog isa} {base T : Addr}
    {size srcU srcV u v : Nat} {G Q : Point C} {row : JointGeneratorRow c.K.M.n C G}
    {E : Nat → Fin C.p}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hPrep : JointPrepLayout c size srcU srcV)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (ha : AM3 C)
    (hD : JointDoubler c C size double)
    (hOne : c.K.one<C.p) (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hQ : onCurve C Q=true)
    (hp : InvJ C (E c.K.P.x) (E c.K.P.y) (E c.K.P.z) Q) (hz : E c.K.zero=0)
    (hu : u<2^(64*c.K.M.n)) (hv : v<2^(64*c.K.M.n)) {s : State}
    (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E s)
    (he : JointGenerator c C base T size row s)
    (hU : wordsVal s.mem base srcU c.K.M.n=u) (hV : wordsVal s.mem base srcV c.K.M.n=v) :
    WP isa (.seq (Joint.prep c srcU srcV) (Joint.window c double)) s fun t =>
      JointCore c C base size Q u v (JointGenerator c C base T size row)
        (add (mul u G) (mul v Q)) t ∧ t.gpr .rbx=0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      Unch base (jointPrepRanges c++((jointInitWork c++jointWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)]))
        s.mem t.mem := by
  apply WP.seq
  refine WP.mono (jointMulPrep_ok hPrep hInit.naf.lay hi hp hz he hU hV)
    fun a ⟨ia,pa,ka,ua⟩ => ?_
  refine WP.mono (jointMulWindow_ok hL hInit hm hC ha hD hOne hOneVal hG hQ hu hv
    (ia.to_tmv (C:=C)) pa) fun t ⟨kt,ct,tb⟩ => ?_
  exact ⟨ct,tb,kt.regs.rd.trans ka.rd,kt.regs.wr.trans ka.wr,ua.trans kt.unch⟩

end VG.Proof.Weierstrass.X86_64
