import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJacMasked
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointMask
import VerifiedGarbage.Proof.Weierstrass.JacSecret

/-! Execution of the two infinity masks, including its exact field environment. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def infinityMaskEnv {F : Type} [Zero F] [DecidableEq F] (E : Nat → F) (p q o : Pt) : Nat → F :=
  pointMaskEnv (pointMaskEnv E o q p.z) o p q.z

theorem infinityMasks_ok {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4) (hm : UnitMod m (2^(64*K.M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl V E s)
    {p q o : Pt} (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (hV : ∀ x∈jacCoords o++jacCoords p++jacCoords q,x∈V)
    (hap : ∀ x∈jacCoords o,∀ y∈jacCoords p++jacCoords q,x≠y) :
    WP isa (.block (Impl.Weierstrass.X86_64.CachedJac.infinityMasks K p q o)) s fun t =>
      ProgKeep K.M base (jacCoords o) s t ∧
      Inv K.M base size m Sl (jacCoords o++V) (infinityMaskEnv E p q o) t := by
  have hOp : ∀ x∈jacCoords o++jacCoords p,x∈V := by
    intro x hx
    exact hV x (List.mem_append_left _ hx)
  have hOq : ∀ x∈jacCoords o++jacCoords q,x∈V := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hV x (List.mem_append_left _ (List.mem_append_left _ hx))
    · exact hV x (List.mem_append_right _ hx)
  have hpz : p.z∈V := hOp _ (by simp [jacCoords])
  have hqz : q.z∈V := hOq _ (by simp [jacCoords])
  rw [Impl.Weierstrass.X86_64.CachedJac.infinityMasks,WP.block_append_iff]
  refine WP.mono (pointMask_ok hL hn hm hI hy hz hOq hpz
    (fun x hx y hy => hap x hx y (List.mem_append_right _ hy))) fun u ⟨ku,iu⟩ => ?_
  refine WP.mono (pointMask_ok hL hn hm iu hy hz
    (fun x hx => List.mem_append_right _ (hOp x hx)) (List.mem_append_right _ hqz)
    (fun x hx y hy => hap x hx y (List.mem_append_left _ hy))) fun t ⟨kt,it⟩ => ?_
  refine ⟨ku.trans kt,it.sub ?_⟩
  exact fun x hx => List.mem_append_right _ hx

theorem pointMaskEnv_values {F : Type} [Zero F] [DecidableEq F]
    (E : Nat → F) (o a : Pt) (z : Nat) (hy : o.y=o.x+32) (hz : o.z=o.x+64) :
    (pointMaskEnv E o a z o.x,pointMaskEnv E o a z o.y,pointMaskEnv E o a z o.z)=
      if E z=0 then (E a.x,E a.y,E a.z) else (E o.x,E o.y,E o.z) := by
  unfold pointMaskEnv
  rw [pointTransferEnv_values E o _ hy hz]
  split <;> rfl

theorem infinityMaskEnv_values {F : Type} [Zero F] [DecidableEq F]
    (E : Nat → F) (p q o : Pt) (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (hap : ∀ x∈jacCoords p++jacCoords q,x∉jacCoords o) :
    (infinityMaskEnv E p q o o.x,infinityMaskEnv E p q o o.y,infinityMaskEnv E p q o o.z)=
      if E q.z=0 then (E p.x,E p.y,E p.z)
      else if E p.z=0 then (E q.x,E q.y,E q.z) else (E o.x,E o.y,E o.z) := by
  have hp : ∀ x∈jacCoords p++jacCoords q, pointMaskEnv E o q p.z x=E x :=
    fun x hx => pointMaskEnv_readonly E o q p.z (hap x hx)
  unfold infinityMaskEnv
  rw [pointMaskEnv_values _ o p q.z hy hz, hp _ (by simp [jacCoords])]
  split
  · rw [hp _ (by simp [jacCoords]),hp _ (by simp [jacCoords]),hp _ (by simp [jacCoords])]
  · exact pointMaskEnv_values E o q p.z hy hz

theorem CachedJac.full_readonly {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p q o : Pt} {dst : Nat} (hA : RcbApart S p q o)
    (E : Nat → F) {x : Nat} (hx : x∈rcbR S p q) :
    runOps (Impl.Weierstrass.X86_64.CachedJac.head S p q dst++jacTail S p q o) E x=E x := by
  apply runOps_of_not_out
  intro op hop he
  rw [CachedJac.head_eq S p q o dst,CachedJac.tail_eq S p q o dst,←List.map_append] at hop
  exact hA.apart x hx (he ▸ CachedJac.out
    (show ∀ op∈CachedJac.headN++jacTailN,op.out<9 by decide) hop)

/-- Field execution is unconditional, including scalar inputs rejected by ECDH. -/
theorem cachedJacMaskedField_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n)))
    {p q o : Pt} {dst : Nat} (hA : RcbApart K.S p q o)
    (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (h2a : dst∉rcbW K.S o) (h3a : dst+32∉rcbW K.S o)
    (hSl : ∀ x∈(rcbW K.S o++rcbR K.S p q)++[dst,dst+32],Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR K.S p q++[dst,dst+32],x∈V)
    (h2 : E dst=E q.z*E q.z) (h3 : E (dst+32)=E dst*E q.z) :
    WP isa (Impl.Weierstrass.X86_64.CachedJac.maskedAdd K p q o dst) s fun t =>
      let EF := runOps (Impl.Weierstrass.X86_64.CachedJac.head K.S p q dst++jacTail K.S p q o) E
      let EM := infinityMaskEnv EF p q o
      ProgKeep K.M base (rcbW K.S o) s t ∧
      Inv K.M base size C.p Sl (jacCoords o++V) EM t ∧
      (EM o.x,EM o.y,EM o.z)=jacAddMasked (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  have hw : ∀ x∈jacCoords o,x∈rcbW K.S o := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [rcbW]
  have hr : ∀ x∈jacCoords p++jacCoords q,x∈rcbR K.S p q := by
    intro x hx
    simp only [jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (rfl|rfl|rfl)|(rfl|rfl|rfl) <;> simp [rcbR]
  have hap : ∀ x∈jacCoords o,∀ y∈jacCoords p++jacCoords q,x≠y := by
    intro x hx y hy he
    exact hA.apart y (hr y hy) (he ▸ hw x hx)
  rw [Impl.Weierstrass.X86_64.CachedJac.maskedAdd]
  apply WP.seq
  refine WP.mono (CachedJac.head_ok hn hL hm hA h2a h3a hSl hI hV h2 h3) fun u ⟨ku,iu,_,_⟩ => ?_
  apply WP.seq
  refine WP.mono (CachedJac.tail_ok hn hL hm hA h2a h3a hSl iu hV h2 h3) fun v ⟨kv,iv,hf⟩ => ?_
  have hv : ∀ x∈jacCoords o++jacCoords p++jacCoords q,x∈jacCoords o++V := by
    intro x hx
    rw [List.append_assoc] at hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (hV x (List.mem_append_left _ (hr x hx)))
  refine WP.mono (infinityMasks_ok hL hn hm iv hy hz hv hap) fun t ⟨kt,it⟩ => ?_
  refine ⟨ku.trans (kv.trans (kt.mono hw)),it.sub ?_,?_⟩
  · exact fun x hx => List.mem_append_right _ hx
  · rw [infinityMaskEnv_values _ p q o hy hz (fun x hx ho => hA.apart x (hr x hx) (hw x ho))]
    have he : ∀ x∈rcbR K.S p q,
        runOps (Impl.Weierstrass.X86_64.CachedJac.head K.S p q dst++jacTail K.S p q o) E x=E x :=
      fun x hx => CachedJac.full_readonly hA E hx
    rw [he _ (by simp [rcbR]),he _ (by simp [rcbR]),he _ (by simp [rcbR]),
      he _ (by simp [rcbR]),he _ (by simp [rcbR]),he _ (by simp [rcbR]),hf]
    rfl

/-- The scalar-window noncollision bound discharges the only excluded point case. -/
theorem cachedJacMasked_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    {p q o : Pt} {dst : Nat} (hA : RcbApart K.S p q o)
    (hy : o.y=o.x+32) (hz : o.z=o.x+64)
    (h2a : dst∉rcbW K.S o) (h3a : dst+32∉rcbW K.S o)
    (hSl : ∀ x∈(rcbW K.S o++rcbR K.S p q)++[dst,dst+32],Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈rcbR K.S p q++[dst,dst+32],x∈V)
    (h2 : E dst=E q.z*E q.z) (h3 : E (dst+32)=E dst*E q.z)
    {P Q : Point C} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q)
    (hne : P≠.infinity → Q≠.infinity → P≠Q) :
    WP isa (Impl.Weierstrass.X86_64.CachedJac.maskedAdd K p q o dst) s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  refine WP.mono (cachedJacMaskedField_ok hn hL hm hA hy hz h2a h3a hSl hI hV h2 h3)
    fun t ⟨kt,it,ht⟩ => ?_
  have jt := hJP.add_masked hC ha hP hQ hJQ hne
  dsimp only at jt
  rw [←ht] at jt
  exact ⟨_,kt,it,jt⟩

end VG.Proof.Weierstrass.X86_64
