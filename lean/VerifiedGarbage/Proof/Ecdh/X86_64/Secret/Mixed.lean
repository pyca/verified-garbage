import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Proof.Weierstrass.PeerTable

/-! Field execution and point correctness for the table's mixed addition. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem mixed_fields_ok {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt}
    (hA : RcbApart K.S p q o) (hSl : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl V E s) (hV : ∀ x∈rcbR K.S p q,x∈V) :
    WP isa (Impl.Ecdh.X86_64.Window5.mixed K p q o) s fun t =>
      let EF := runOps (jacMixedHead K.S p q++jacMixedTail K.S p q o) (jacMixedInit K.S p E)
      ProgKeep K.M base (rcbW K.S o) s t ∧
      Inv K.M base size m Sl ([o.x,o.y,o.z]++V) EF t ∧
      (EF o.x,EF o.y,EF o.z)=jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) 1 := by
  rw [Impl.Ecdh.X86_64.Window5.mixed,←hn]
  apply WP.seq
  refine WP.mono (jacMixedInit_ok hL hSl hI hV) fun u ⟨ku,iu⟩ => ?_
  let N := jacMixedHeadN++jacMixedTailN
  have he : jacMixedHead K.S p q++jacMixedTail K.S p q o=ofN N K.S p q o := by
    rw [jacMixedHead_eq K.S p q o,jacMixedTail_eq]
    simp only [N,ofN,List.map_append]
  have hN : ∀ op∈N,op.out<9 := by decide
  have hr := readsOk_rename (rcbσ K.S p q o)
    (show readsOk N [4,2,9,10,11,12,13,14,15,16]=true by decide)
  have hr' : readsOk (ofN N K.S p q o) (K.S.t4::K.S.t2::V)=true := readsOk_mono hr (by
    intro x hx
    change x∈K.S.t4::K.S.t2::rcbR K.S p q at hx
    simp only [List.mem_cons] at hx ⊢
    rcases hx with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hV x h)))
  change WP isa (ForwardField.programB K.M _) u _
  rw [he]
  refine WP.mono (ofN_forward_partial_ok hL hm hN hA hSl iu hr') fun t ⟨kt,it,hval⟩ => ?_
  refine ⟨ku.trans kt,it.sub ?_,?_⟩
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      rw [←he]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;> simp [jacMixedTail,jacTail,FOp.out]
    · exact Or.inl (by simp [hx])
  · have hx := hval 6
    have hy := hval 7
    have hz := hval 8
    rw [jacMixedInit_rename hA] at hx hy hz
    exact (congrArg₂ Prod.mk hx (congrArg₂ Prod.mk hy hz)).trans
      (jacMixedN_run (fun i => E (rcbσ K.S p q o i)))

theorem mixed_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) {p q o : Pt}
    (hA : RcbApart K.S p q o) (hSl : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x∈rcbR K.S p q,x∈V)
    {P Q : Point C} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) P) (hJQ : InvJ C (E q.x) (E q.y) (E q.z) Q)
    (hpz : E p.z≠0) (hAff : E q.z=1)
    (hx : E q.x*(E p.z*E p.z)-E p.x≠0) :
    WP isa (Impl.Ecdh.X86_64.Window5.mixed K p q o) s
      (JacPost K.M K.S base size C Sl V o (Spec.Weierstrass.add P Q) s) := by
  refine WP.mono (mixed_fields_ok hn hL hm hA hSl hI hV) fun t ⟨kt,it,ht⟩ => ?_
  have hqz : E q.z≠0 := by rw [hAff]; exact hC.one_ne_zero
  have hh : E q.x*(E p.z*E p.z)-E p.x*(E q.z*E q.z)≠0 := by
    simpa only [hAff,Lean.Grind.Semiring.mul_one] using hx
  have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
  dsimp only at jt
  rw [hAff,←ht] at jt
  exact ⟨_,kt,it,jt⟩

/-- The actual table step, with its exceptional cases ruled out by peer order. -/
theorem table_mixed_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hO : PeerOrder C)
    {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o++rcbR K.S p q,Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hV : ∀ x∈rcbR K.S p q,x∈V)
    {P : Point C} (hP : onCurve C P=true) (hne : P≠.infinity)
    {i : Nat} (hi : 1<i) (hin : i+1<C.n)
    (hJP : InvJ C (E p.x) (E p.y) (E p.z) (mul i P))
    (hJQ : InvJ C (E q.x) (E q.y) (E q.z) P) (hAff : E q.z=1) :
    WP isa (Impl.Ecdh.X86_64.Window5.mixed K p q o) s
      (JacPost K.M K.S base size C Sl V o (mul (i+1) P) s) := by
  have hh := hO.table_mixed_inputs hC hP hne hi hin hJP hJQ hAff
  have he := hC.add_mul_mul hP i 1
  rw [mul_one_pt] at he
  rw [←he]
  exact mixed_ok hn hL hm hC ha hA hSl hI hV (hC.onCurve_mul hP i) hP hJP hJQ hh.1 hAff hh.2

end VG.Proof.Ecdh.X86_64.Secret
