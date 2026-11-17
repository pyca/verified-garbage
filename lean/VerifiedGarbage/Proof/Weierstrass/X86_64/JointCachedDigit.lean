module

public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsWrap
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.CombLay
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
public import VerifiedGarbage.Impl.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Mont.X86_64.OpsReg
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
public import VerifiedGarbage.Proof.X25519.X86_64.Step
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacDoubleForward
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField

/-! ### `Weierstrass.X86_64.CachedJacAdd`, which this module and modules that import it used -/

section

/-! Complete public addition with cached Z powers, including all exceptional cases. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass

/-- Complete Jacobian addition on public data, including all exceptional cases. -/
theorem cachedJacAdd_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) {dbl : RcbSlots → Pt → Pt → List FOp} (hd : JDblOk C dbl)
    {p q o : Pt} {dst : Nat} (hA : RcbApart K.S p q o)
    (h2a : dst∉rcbW K.S o) (h3a : dst+8*K.M.n∉rcbW K.S o)
    (hCacheSl : Sl dst ∧ Sl (dst+8*K.M.n))
    (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V)
    (hCacheV : dst∈V ∧ dst+8*K.M.n∈V)
    (h2 : E dst=E q.z*E q.z) (h3 : E (dst+8*K.M.n)=E dst*E q.z)
    (hOne : K.one < C.p) {P Q : Point C} (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q) :
    WP isa (Impl.Weierstrass.X86_64.CachedJac.add K p q o dst dbl).inline s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  have hSlC : ∀ x∈(rcbW K.S o++rcbR K.S p q)++[dst,dst+8*K.M.n],Sl x := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hSl x hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact hCacheSl.1
      · exact hCacheSl.2
  have hVC : ∀ x∈rcbR K.S p q++[dst,dst+8*K.M.n],x∈V := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hV x hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact hCacheV.1
      · exact hCacheV.2
  rw [Impl.Weierstrass.X86_64.CachedJac.add]
  apply fieldBranch_ok hL hm hI (hV p.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hA hSl ia hV hJQ)
      (fun t ht => ht.prefix (ka.mono (by regions_sub)))
  · intro a ia ka hpz
    apply fieldBranch_ok hL hm ia (hV q.z (by simp [rcbR]))
    · intro b ib kb hz
      have hq := (hJQ.z_zero_iff hC).mp hz
      have hs : ∀ x ∈ rcbW K.S o ++ rcbR K.S q p, Sl x := by
        intro x hx
        rw [List.mem_append,rcbR_swap_mem] at hx
        exact hSl x (List.mem_append.mpr hx)
      have hv : ∀ x ∈ rcbR K.S q p, x ∈ V := fun x hx => hV x ((rcbR_swap_mem _ _ _ _).mp hx)
      have hadd : Spec.Weierstrass.add P Q = P := by rw [hq]; cases P <;> rfl
      rw [hadd]
      exact WP.mono (copyPointJ_ok hL (rcbApart_swap hA) hs ib hv hJP)
        (fun t ht => (ht.prefix (kb.mono (by regions_sub))).prefix (ka.mono (by regions_sub)))
    · intro b ib kb hqz
      apply WP.seq
      refine WP.mono (CachedJac.head_ok hL hm hA h2a h3a hSlC ib hVC h2 h3) fun c ⟨kc,ic,eh,er⟩ => ?_
      let EH := runOps (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S p q dst) E
      have hkeep := (ka.mono (W' := rcbW K.S o) (by simp)).trans
        ((kb.mono (by regions_sub)).trans kc)
      have hpkeep : ∀ x ∈ rcbR K.S p q, EH x = E x := fun x hx => CachedJac.head_readonly hA E hx
      have jp : InvJ C (EH p.x) (EH p.y) (EH p.z) P := by
        rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
        exact hJP
      have oldV : ∀ x ∈ V, x ∈ validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S p q dst) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have hv : ∀ x ∈ rcbR K.S p p, x ∈ validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S p q dst) V :=
        fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
      apply fieldBranch_ok hL hm ic (a := K.S.t3) (by
        rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head,FOp.out])
      · intro d id kd hz
        have hx : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)=0 := eh.symm.trans hz
        apply fieldBranch_ok hL hm id (a := K.S.t5) (by
          rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head,FOp.out])
        · intro e ie ke hrz
          have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)=0 := er.symm.trans hrz
          have hpq := hJP.same hC hJQ hpz hqz hx hy
          have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hdSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, Sl x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hSl x (List.mem_append_left _ hx)
            · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
          rw [←hpq]
          refine WP.mono (jacDoubleForward_ok hL hm hd hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
          exact (JacPost.sub ⟨_,kt,it,jt⟩ oldV).prefix
            (hkeep.trans ((kd.mono (by regions_sub)).trans (ke.mono (by regions_sub))))
        · intro e ie ke hrz
          have hy : E q.y*E p.z*(E p.z*E p.z)-E p.y*E q.z*(E q.z*E q.z)≠0 := fun he => hrz (er.trans he)
          have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
          rw [hadd]
          refine WP.mono (infinityPoint_ok hL
            (fun x hx => hSl x (by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
              rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
          exact (JacPost.sub ht oldV).prefix
            (hkeep.trans ((kd.mono (by regions_sub)).trans (ke.mono (by regions_sub))))
      · intro d id kd hz
        have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := fun he => hz (eh.trans he)
        refine WP.mono (CachedJac.tail_ok hL hm hA h2a h3a hSlC id hVC h2 h3) fun t ⟨kt,it,ht⟩ => ?_
        have jt := hJP.add_ne' hC hP hQ hJQ hpz hqz hh
        dsimp only at jt
        rw [←ht] at jt
        exact JacPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (kd.mono (by regions_sub)))

end VG.Proof.Weierstrass.X86_64

end

end

/-! A public peer digit either leaves the accumulator alone or adds its cached odd multiple. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
                   List.not_mem_nil,or_false] at * <;> grind))

/-- If the digits' additions are calls (`Joint.Cfg.pts`), the functions'
bodies call nothing, and the registers their wrappers keep are among those
the field arithmetic may write. -/
structure JointCalls (c : Joint.Cfg) : Prop where
  ok : ∀ C', c.pts = some C' → (PointOps.addCachedBody c.K c.selected c.dbl).noCalls = true ∧
    (PointOps.addAffineBody c.K c.dbl).noCalls = true ∧
    ∀ r ∈ Proof.Weierstrass.X86_64.PointOps.keptRegs, r ∈ clob c.K.M.n

structure JointAddLayout (c : Joint.Cfg) (size : Nat) : Prop where
  lookup : JointLookupLayout c size
  addApart : RcbApart c.K.S c.K.R c.K.E c.K.D
  cache2Apart : c.selected∉rcbW c.K.S c.K.D
  cache3Apart : c.selected+8*c.K.M.n∉rcbW c.K.S c.K.D
  accumNodup : (jacCoords c.K.R).Nodup
  copyApart : ∀ x∈jacCoords c.K.D,∀ y∈jacCoords c.K.R,x≠y
  calls : JointCalls c

/-- The joint invariant and the field values `E` of the slots `V`, which
`saves` and `restores` keep. -/
theorem jointCore_inv_keeps {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A : Point C} {External : State → Prop} {V : List Nat} {E : Nat → Fe C} {x y : State}
    {rs : List Reg} (hr : Reg.rdi ∉ rs)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (pk : ProgKeep c.K.M base (jointWork c) x y) (k : VG.Proof.X25519.X86_64.Keeps rs x y)
    (sy : y.syms = x.syms)
    (h : JointCore c C base size Q u v External A x ∧ Inv c.K.M base size C.p (·∈jointSlots c) V E x) :
    JointCore c C base size Q u v External A y ∧ Inv c.K.M base size C.p (·∈jointSlots c) V E y :=
  ⟨h.1.of_keeps k hr (hExternal x y pk sy h.1.external), h.2.of_keeps k hr⟩

/-- A digit's addition, `D = R + E` copied back to `R`, inline or as a call
of `body` (`Joint.Cfg.pts`): a run of `body` (which calls nothing) is a run of
the call, from a state the wrapper keeps the joint invariant in. -/
theorem jointAdd_dispatch {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A B : Point C} {External : State → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    {body : Prog isa} {call : Impl.Weierstrass.PointOps.Curve → Prog isa} {prog : Prog isa}
    (hprog : prog = match c.pts with | some C' => call C' | none => body)
    (hcall : ∀ C', (call C').inline = PointOps.wrap body)
    (hnc : ∀ C', c.pts = some C' → body.noCalls = true)
    (hclob : ∀ C', c.pts = some C' → ∀ r ∈ Proof.Weierstrass.X86_64.PointOps.keptRegs, r ∈ clob c.K.M.n)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (h : JointCore c C base size Q u v External A s ∧ Inv c.K.M base size C.p (·∈jointSlots c) V E s)
    (hb : ∀ x, JointCore c C base size Q u v External A x ∧
        Inv c.K.M base size C.p (·∈jointSlots c) V E x →
      WP isa body.inline x fun t => ProgKeep c.K.M base (jointWork c) x t ∧
        JointCore c C base size Q u v External B t) :
    WP isa prog.inline s fun t => ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v External B t := by
  subst hprog
  split
  · next C' hp =>
    rw [hcall C']
    refine Proof.Weierstrass.X86_64.PointOps.wrap_keep_ok (hclob C' hp)
      (fun x y pk k sy hx => jointCore_inv_keeps (by simp) hExternal pk k sy hx)
      (fun x y pk k sy hx => hx.of_keeps k (by decide) (hExternal x y pk sy hx.external)) h
      fun x hx => ?_
    rw [← Code.inline_of_noCalls (hnc C' hp)]
    exact hb x hx
  · exact hb s h

/-- A digit's addition, inline or as a call of `body`, is constant time if
`body` is. -/
theorem jointAdd_relCT_dispatch {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat}
    {V W : List Nat} {E : Nat → Fe C}
    {body : Prog isa} {call : Impl.Weierstrass.PointOps.Curve → Prog isa} {prog : Prog isa}
    (hprog : prog = match c.pts with | some C' => call C' | none => body)
    (hcall : ∀ C', (call C').inline = PointOps.wrap body)
    (hnc : ∀ C', c.pts = some C' → body.noCalls = true)
    (hb : RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) V E) body.inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) W E' s t)) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) V E) prog.inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) W E' s t) := by
  subst hprog
  split
  · next C' hp =>
    rw [hcall C']
    rw [Code.inline_of_noCalls (hnc C' hp)] at hb
    exact Proof.Weierstrass.X86_64.PointOps.wrap_relCT hb
  · exact hb

/-- `R = R + E` for the cached point `E` (`Joint.cachedAdd`). -/
theorem jointCachedAdd_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A P : Point C} {External : State → Prop} {E : Nat → Fe C} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (hd : JDblOk C c.dbl) (hOne : c.K.one<C.p) (hA : onCurve C A=true) (hP : onCurve C P=true)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (h : JointCore c C base size Q u v External A s)
    (hI : Inv c.K.M base size C.p (·∈jointSlots c) (cachedSlots c.K.M.n c.K.E c.selected++jointLive c) E s)
    (hJ : InvJ C (E c.K.R.x) (E c.K.R.y) (E c.K.R.z) A)
    (hc : CachedPoint c.K.M.n C E c.K.E c.selected P) :
    WP isa (Joint.cachedAdd c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧ JointCore c C base size Q u v External (add A P) t := by
  refine jointAdd_dispatch (body := PointOps.addCachedBody c.K c.selected c.dbl) rfl (fun _ => rfl)
    (fun C' hp => (hL.calls.ok C' hp).1) (fun C' hp => (hL.calls.ok C' hp).2.2) hExternal ⟨h, hI⟩
    fun b ⟨cb, ib⟩ => ?_
  rw [PointOps.addCachedBody]
  simp only [Code.inline]
  apply WP.seq
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by
    intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈cachedSlots c.K.M.n c.K.E c.selected++jointLive c := by
    intro x hx; jslots
  refine WP.mono_syms (cachedJacAdd_ok hL.lookup.layout.lay hm hC hd
    hL.addApart hL.cache2Apart hL.cache3Apart (by constructor <;> simp [jointSlots])
    sl ib vr (by constructor <;> simp [cachedSlots]) hc.2.1 hc.2.2 hOne hA
    hP hJ hc.1) fun d ⟨ed,kd,id,jd⟩ sd => ?_
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

theorem jointCachedDigit_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q A : Point C} {External : State → Prop} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (hd : JDblOk C c.dbl) (hOne : c.K.one<C.p)
    (hQ : onCurve C Q=true) (hA : onCurve C A=true)
    (h : JointCore c C base size Q u v External A s)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (hj : j<64*c.K.M.n+1) (hb : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (Joint.cachedDigit c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v External (add A (FastNaf.point C Q 5 v j)) t := by
  have hbytes : c.K.bits+j<size := by
    have hh := hL.lookup.layout.stableBounds (c.K.bits,64*c.K.M.n+1) (by simp [jointStableRanges])
    dsimp only at hh
    omega_using [hj, hh]
  rw [Joint.cachedDigit]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono_syms (nafRead_ok h.field.scr hbytes hb (h.stable.peer j hj)) fun a ⟨a8,az,ka⟩ sa => ?_
  have kp : ProgKeep c.K.M base (jointWork c) s a := jointKeeps_prog ka (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    simp [clob,VG.Impl.Mont.X86_64.acc])
  have ca := h.of_keeps ka (by decide) (hExternal s a kp sa h.external)
  refine WP.ite (decide (FastNaf.byte 5 v j=0)) az (fun hz => ?_) (fun hn => ?_)
  · have hz' := (FastNaf.byte_zero_iff 5 v j).mp (of_decide_eq_true hz)
    have ep : FastNaf.point C Q 5 v j=Point.infinity := by
      unfold FastNaf.point
      have h0 : mul 0 Q=Point.infinity := by rw [Spec.Weierstrass.mul]; rfl
      rw [hz',h0]
      split <;> rfl
    have ea : add A (FastNaf.point C Q 5 v j)=A := by rw [ep]; cases A <;> rfl
    rw [ea]
    exact WP.block_nil ⟨kp,ca⟩
  · have hmag : FastNaf.magnitude 5 v j≠0 := fun he =>
      (of_decide_eq_false hn) ((FastNaf.byte_zero_iff 5 v j).mpr he)
    apply WP.seq
    refine WP.mono (jointCachedEntry_ok hL.lookup hm ca hExternal hmag a8)
      fun b ⟨kb,cb,ib,jb⟩ => ?_
    refine WP.mono (jointCachedAdd_ok hL hm hC hd hOne hA (FastNaf.onCurve_point hC hQ 5 v j)
      hExternal cb ib cb.point jb) fun t ⟨kt,ct⟩ => ⟨(kp.trans kb).trans kt,ct⟩

end VG.Proof.Weierstrass.X86_64
