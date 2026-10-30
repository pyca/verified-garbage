module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16State
public import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead

/-! A fixed-generator digit updates the same accumulator and preserves the external row. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

/-- `R = R + E` for the affine point `E` (`Joint.fixedAdd`). -/
theorem jointFixedAdd_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A P : Point C} {External : State → Prop} {E : Nat → Fe C} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (hd : JDblOk C c.dbl) (hOne : c.K.one<C.p) (hA : onCurve C A=true) (hP : onCurve C P=true)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (h : JointCore c C base size Q u v External A s)
    (hI : Inv c.K.M base size C.p (·∈jointSlots c) (jacCoords c.K.E++jointLive c) E s)
    (hJ : InvJ C (E c.K.R.x) (E c.K.R.y) (E c.K.R.z) A)
    (hJE : InvJ C (E c.K.E.x) (E c.K.E.y) (E c.K.E.z) P) (hz : E c.K.E.z=1) :
    WP isa (Joint.fixedAdd c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧ JointCore c C base size Q u v External (add A P) t := by
  refine jointAdd_dispatch (body := PointOps.addAffineBody c.K c.dbl) rfl (fun _ => rfl)
    (fun C' hp => (hL.calls.ok C' hp).2.1) (fun C' hp => (hL.calls.ok C' hp).2.2) hExternal ⟨h, hI⟩
    fun b ⟨cb, ib⟩ => ?_
  rw [PointOps.addAffineBody]
  simp only [Code.inline]
  apply WP.seq
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by
    intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈jacCoords c.K.E++jointLive c := by
    intro x hx; jslots
  refine WP.mono_syms (jacMixedForward_ok hL.lookup.layout.lay hm hC hd
    hL.addApart sl ib vr hOne hA hP hJ hJE hz)
    fun d ⟨ed,kd,id,jd⟩ sd => ?_
  have wd : ∀ x∈rcbW c.K.S c.K.D,x∈jointWork c := by intro x hx; jslots
  have edExt := hExternal b d (kd.mono wd) sd cb.external
  have rs : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by intro x hx; jslots
  refine WP.mono_syms (copyPointFields_ok hL.lookup.layout.lay hL.accumNodup hL.copyApart rs id
    (fun _ hx => List.mem_append_left _ hx)) fun t ⟨et,kt,it,jt⟩ st => ?_
  have wr : ∀ x∈jacCoords c.K.R,x∈jointWork c := by intro x hx; jslots
  have kt' := kt.mono wr
  have kw := (kd.mono wd).trans kt'
  have ie := it.sub (fun x hx => List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ hx)))
  have jp : InvJ C (et c.K.R.x) (et c.K.R.y) (et c.K.R.z) (add A P) := by
    simp only [Prod.mk.injEq] at jt
    rw [jt.1,jt.2.1,jt.2.2]
    exact jd
  exact ⟨kw,cb.next hL.lookup.layout kw ie jp (hExternal d t kt' st edExt)⟩

/-- The read of the generator's digit `j`: the cell of either width, and its zero test. -/
theorem jointFixedRead_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q A : Point C} {Gen : State → Prop} {s : State}
    (hL : JointLayout c size) (h : JointCore c C base size Q u v Gen A s)
    (hj : j<64*c.K.M.n+1) (hb : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block (Joint.fixedRead c)) s fun a =>
      a.gpr .r8=jointGCell c u j ∧ a.zf=some (decide (FastNaf.magnitude c.gw u j=0)) ∧
        VG.Proof.X25519.X86_64.Keeps [.r8] s a := by
  have hh := hL.stableBounds (c.gBits,jointGLen c) (by simp [jointStableRanges])
  dsimp only at hh
  by_cases h9 : c.gw=9
  · rw [Joint.fixedRead,ite_eq_left h9]
    have hl : jointGLen c=2*(64*c.K.M.n+1) := by rw [jointGLen,ite_eq_left h9]
    have g0 := h.stable.generator (2*j) (by omega)
    have g1 := h.stable.generator (2*j+1) (by omega)
    rw [jointGByte,ite_eq_left h9,FastNaf.wbyte] at g0 g1
    rw [show 2*j/2=j by omega,show 2*j%2=0 by omega,Nat.mul_zero] at g0
    rw [show (2*j+1)/2=j by omega,show (2*j+1)%2=1 by omega,Nat.mul_one,← Nat.add_assoc] at g1
    refine WP.mono (nafRead16_ok h.field.scr (by omega) hb g0 g1) fun a ⟨a8,az,ka⟩ => ⟨?_,?_,ka⟩
    · rw [a8,jointGCell,ite_eq_left h9]
    · rw [az,h9]
      congr 1
      exact decide_eq_decide.mpr (FastNaf.word_zero_iff u j)
  · have h7 : c.gw=7 := hL.gw.resolve_right h9
    rw [Joint.fixedRead,ite_eq_right h9]
    have hl : jointGLen c=64*c.K.M.n+1 := by rw [jointGLen,ite_eq_right h9]
    have g := h.stable.generator j (by omega)
    rw [jointGByte,ite_eq_right h9] at g
    refine WP.mono (nafRead_ok (K:={c.K with bits:=c.gBits}) h.field.scr (by dsimp only; omega) hb g)
      fun a ⟨a8,az,ka⟩ => ⟨?_,?_,ka⟩
    · rw [a8,jointGCell,ite_eq_right h9]
    · rw [az,h7]
      congr 1
      exact decide_eq_decide.mpr (FastNaf.byte_zero_iff 7 u j)

theorem jointFixedDigit_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (hd : JDblOk C c.dbl) (hOne : c.K.one<C.p)
    (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hA : onCurve C A=true)
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) A s)
    (hj : j<64*c.K.M.n+1) (hb : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (Joint.fixedDigit c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add A (FastNaf.point C G c.gw u j)) t := by
  have hExternal := JointGenerator.workKeep (base:=base) (row:=row) (T:=T) hL.lookup.layout h.field.mod.tmp
  have read := jointFixedRead_ok hL.lookup.layout h hj hb
  rw [Joint.fixedDigit]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono_syms read fun a ⟨a8,az,ka⟩ sa => ?_
  have kp : ProgKeep c.K.M base (jointWork c) s a := jointKeeps_prog ka (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    simp [clob,VG.Impl.Mont.X86_64.acc])
  have ca := h.of_keeps ka (by decide) (hExternal s a kp sa h.external)
  refine WP.ite (decide (FastNaf.magnitude c.gw u j=0)) az (fun hz => ?_) (fun hn => ?_)
  · have hz' := of_decide_eq_true hz
    have ep : FastNaf.point C G c.gw u j=Point.infinity := by
      unfold FastNaf.point
      have h0 : mul 0 G=Point.infinity := by rw [Spec.Weierstrass.mul]; rfl
      rw [hz',h0]
      split <;> rfl
    have ea : add A (FastNaf.point C G c.gw u j)=A := by rw [ep]; cases A <;> rfl
    rw [ea]
    exact WP.block_nil ⟨kp,ca⟩
  · have hmag : FastNaf.magnitude c.gw u j≠0 := of_decide_eq_false hn
    apply WP.seq
    have e := jointFixedEntry_core_ok hL.lookup hm hOne hOneVal ca hmag a8
    have e' : WP isa (if c.gw=9 then Joint.fixedEntryW c.K c.tsym else Joint.fixedEntry c.K c.tsym).inline a
        fun t => ProgKeep c.K.M base (jointWork c) a t ∧
          JointCore c C base size Q u v (JointGenerator c C base T size row) A t ∧
          Inv c.K.M base size C.p (·∈jointSlots c) (jacCoords c.K.E++jointLive c) (tmv C c.K.M.n base t) t ∧
          InvJ C (tmv C c.K.M.n base t c.K.E.x) (tmv C c.K.M.n base t c.K.E.y)
            (tmv C c.K.M.n base t c.K.E.z) (FastNaf.point C G c.gw u j) ∧
          tmv C c.K.M.n base t c.K.E.z=1 := by
      split
      · next h9 => rw [ite_eq_left h9] at e; exact e
      · next h9 => rw [ite_eq_right h9] at e; exact e
    refine WP.mono e' fun b ⟨kb,cb,ib,jb,zb⟩ => ?_
    refine WP.mono (jointFixedAdd_ok hL hm hC hd hOne hA (FastNaf.onCurve_point hC hG c.gw u j)
      hExternal cb ib cb.point jb zb) fun t ⟨kt,ct⟩ => ⟨(kp.trans kb).trans kt,ct⟩

end VG.Proof.Weierstrass.X86_64
