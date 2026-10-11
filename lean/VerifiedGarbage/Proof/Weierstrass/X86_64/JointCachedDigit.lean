import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsWrap

/-! A public peer digit either leaves the accumulator alone or adds its cached odd multiple. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
  List.not_mem_nil,or_false] at * <;> grind))

/-- If the digits' additions are calls (`Joint.Cfg.pts`), the functions'
bodies call nothing, and the registers their wrappers keep are among those
the field arithmetic may write. -/
structure JointCalls (c : Joint.Cfg) : Prop where
  ok : ∀ C', c.pts = some C' → (PointOps.addCachedBody c.K c.selected).noCalls = true ∧
    (PointOps.addAffineBody c.K).noCalls = true ∧
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
    {body : Prog isa} {call : Spec.Weierstrass.PointOps.Curve → Prog isa} {prog : Prog isa}
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
    {body : Prog isa} {call : Spec.Weierstrass.PointOps.Curve → Prog isa} {prog : Prog isa}
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
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p) (hA : onCurve C A=true) (hP : onCurve C P=true)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (h : JointCore c C base size Q u v External A s)
    (hI : Inv c.K.M base size C.p (·∈jointSlots c) (cachedSlots c.K.M.n c.K.E c.selected++jointLive c) E s)
    (hJ : InvJ C (E c.K.R.x) (E c.K.R.y) (E c.K.R.z) A)
    (hc : CachedPoint c.K.M.n C E c.K.E c.selected P) :
    WP isa (Joint.cachedAdd c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧ JointCore c C base size Q u v External (add A P) t := by
  refine jointAdd_dispatch (body := PointOps.addCachedBody c.K c.selected) rfl (fun _ => rfl)
    (fun C' hp => (hL.calls.ok C' hp).1) (fun C' hp => (hL.calls.ok C' hp).2.2) hExternal ⟨h, hI⟩
    fun b ⟨cb, ib⟩ => ?_
  rw [PointOps.addCachedBody]
  simp only [Code.inline]
  apply WP.seq
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by
    intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈cachedSlots c.K.M.n c.K.E c.selected++jointLive c := by
    intro x hx; jslots
  refine WP.mono_syms (cachedJacAdd_ok hL.lookup.layout.lay hm hC ha
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
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p)
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
    omega
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
    refine WP.mono (jointCachedAdd_ok hL hm hC ha hOne hA (FastNaf.onCurve_point hC hQ 5 v j)
      hExternal cb ib cb.point jb) fun t ⟨kt,ct⟩ => ⟨(kp.trans kb).trans kt,ct⟩

end VG.Proof.Weierstrass.X86_64
