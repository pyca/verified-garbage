import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfForward
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfWP
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField

/-! Functional correctness of point doubling with register forwarding across every field boundary. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.P256.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Spec.Weierstrass

theorem half_forward_ok {M : Mod} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) {V : List Nat} {E : Nat → Fin Spec.P256.p}
    {s : State} (hI : Inv M base size Spec.P256.p Sl V E s) {o a : Nat}
    (ho : Sl o) (ha : a∈V) {cs : Forward.Cache} (hc : Forward.Valid cs s) :
    WP isa (.block (Forward.block cs (half o a))) s fun t =>
      (OpKeep M base o s t ∧
        Inv M base size Spec.P256.p Sl (o::V) (Function.update E o (halfFe (E a))) t) ∧
      Forward.Valid (Forward.ofStores [.r8,.r9,.r10,.r11] o) t := by
  apply Forward.block_wp hc
  exact Forward.block_stores_valid (half_inv_ok hn hL hI ho ha) (fun _ ht => ht.2.scr)
    (by change o+8*4≤size; have h := hL.le o ho; simpa only [hn] using h) (by decide)

theorem doubleHalfForward_ok {M : Mod} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) (hm : UnitMod Spec.P256.p (2^(64*M.n)))
    (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    {S : RcbSlots} {p : Pt} (hd : (doubleSlots S p).Nodup)
    (hSl : ∀ x∈doubleSlots S p,Sl x)
    {V : List Nat} {E : Nat → Fin Spec.P256.p} {s : State}
    (hI : Inv M base size Spec.P256.p Sl V E s)
    (hV : ∀ x∈[p.x,p.y,p.z],x∈V) {P : Point Spec.P256.curve}
    (hP : onCurve Spec.P256.curve P=true)
    (hJ : InvJ Spec.P256.curve (E p.x) (E p.y) (E p.z) P) :
    WP isa (doubleHalfForward M S p) s fun t =>
      ProgKeep M base (doubleSlots S p) s t ∧
      Inv M base size Spec.P256.p Sl ([p.x,p.y,p.z]++V) (doubleHalfEnv S p E) t ∧
      InvJ Spec.P256.curve (doubleHalfEnv S p E p.x) (doubleHalfEnv S p E p.y)
        (doubleHalfEnv S p E p.z) (Spec.Weierstrass.add P P) := by
  rw [doubleHalfForward]
  apply WP.seq
  refine WP.mono (ForwardField.program_ok hn hL hm _ hI (doubleHalf_before_slots hSl)
    (readsOk_mono (doubleHalf_before_reads S p) hV) (fun _ h => by cases h))
    fun u ⟨ku,hu,hcu⟩ => ?_
  apply WP.seq
  have hs1 : Sl S.t1 := hSl _ (by simp [doubleSlots])
  have hv1 : S.t1∈validAfter (DoubleHalf.before S p) V := by
    simp [DoubleHalf.before,validAfter,FOp.out]
  refine WP.mono (half_forward_ok hn hL hu hs1 hv1 hcu) fun v ⟨⟨kv,hv⟩,hcv⟩ => ?_
  refine WP.mono (ForwardField.program_ok hn hL hm _ hv (doubleHalf_after_slots hSl)
    (doubleHalf_after_reads S p V) hcv) fun t ⟨kt,ht,_⟩ => ?_
  have kb : ProgKeep M base (doubleSlots S p) s u := ku.mono (by
    intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    exact doubleHalf_before_slots (fun _ h => h) op hop op.out (List.mem_cons_self ..))
  have ka : ProgKeep M base (doubleSlots S p) v t := kt.mono (by
    intro x hx
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
    exact doubleHalf_after_slots (fun _ h => h) op hop op.out (List.mem_cons_self ..))
  refine ⟨kb.trans ((progKeep_of_op kv (by simp [doubleSlots])).trans ka),
    ht.sub ?_,InvJ.dbl' hC ha hP hJ (doubleHalfEnv_run S p E hd)⟩
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with (rfl|rfl|rfl)|hx <;>
    simp [DoubleHalf.before,DoubleHalf.after,validAfter,FOp.out, *]

end VG.Proof.P256.X86_64
