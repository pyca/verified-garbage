import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass

theorem tmv_keep {M : Mod} {base : Addr} {size : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay M size Sl) {s t : State} {W : List Nat}
    (hk : ProgKeep M base W s t) (hn : base.toNat+size≤2^64)
    (hW : ∀ w∈W,Sl w) {x : Nat} (hx : Sl x) (hne : x∉W) :
    tmv C M.n base t x=tmv C M.n base s x := by
  unfold tmv
  rw [hk.unch.wordsVal (fun q hq => ?_) (by have := hL.le x hx; omega)]
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hq
  rcases hq with ⟨w,hw,rfl⟩ | rfl
  · exact hL.apart x w hx (hW w hw) (fun he => hne (he ▸ hw))
  · exact hL.tmp x hx

def entryWrites : List Nat := [K.E.x,K.E.y,K.E.z,5400,5432]
def entryLive (V : List Nat) : List Nat := [K.E.x,K.E.y,K.E.z]++([5400,5432]++V)

theorem entryLoad_ok {base : Addr} {size a : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hi : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ha : 1≤a) (ha8 : a≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z,
      6000+64*(a-1),6032+64*(a-1)],x∈V)
    (hz2 : E (6000+64*(a-1))=E (Jacobian.tablePt K a).z*E (Jacobian.tablePt K a).z)
    (hz3 : E (6032+64*(a-1))=E (Jacobian.tablePt K a).z*(E (Jacobian.tablePt K a).z*E (Jacobian.tablePt K a).z))
    {P : Point C} (hJ : InvJ C (E (Jacobian.tablePt K a).x) (E (Jacobian.tablePt K a).y)
      (E (Jacobian.tablePt K a).z) P) :
    WP isa (.block (CachedJac.load++Jacobian.publicEntry K)) s fun t =>
      ProgKeep K.M base entryWrites s t ∧
      Inv K.M base size C.p Sl (entryLive V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z) P ∧
      tmv C K.M.n base t 5400=tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z ∧
      tmv C K.M.n base t 5432=tmv C K.M.n base t K.E.z*(tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z) := by
  have dc : ∀ x∈[5400,5432],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have de : ∀ x∈[K.E.x,K.E.y,K.E.z],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have st : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],x∈V :=
    fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  rw [WP.block_append_iff]
  refine WP.mono (cachedLoadField_ok hL (by rfl) hi h2 ha ha8 hsize dc
    (fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)))
    fun b ⟨kb,ib,b2,b3,bidx0⟩ => ?_
  have bt : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      tmv C K.M.n base b x=E x := by
    intro x hx
    rw [tmv_keep hL kb hi.scr.nowrap dc (hi.sl x (st x hx)) ?_]
    exact hi.val x (st x hx)
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rw [not_or]
    have ht : K.tbl=2848 := rfl
    rw [ht] at hx
    omega
  have bidx : b.gpr .x2=BitVec.ofNat 64 a := bidx0.trans h2
  refine WP.mono (jacPublicFields_ok hL hAl (by rfl) (by rfl) (by rfl) ib bidx ha (by decide)
    de (fun x hx => List.mem_append_right _ (st x hx)) (Or.inl (by change 704+96≤2848+96*(a-1); omega)))
    fun t ⟨kt,it,vt⟩ => ?_
  have vals : (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
      (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) := by
    rw [vt,bt _ (by simp),bt _ (by simp),bt _ (by simp)]
  have kc : ∀ x∈[5400,5432],tmv C K.M.n base t x=tmv C K.M.n base b x := by
    intro x hx
    exact tmv_keep hL kt ib.scr.nowrap de (dc x hx) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have vz : tmv C K.M.n base t K.E.z=E (Jacobian.tablePt K a).z := congrArg (fun z => z.2.2) vals
  refine ⟨(kb.mono (by simp [entryWrites])).trans (kt.mono (by simp [entryWrites])),it,?_,?_,?_⟩
  · simp only [Prod.mk.injEq] at vals
    rw [vals.1,vals.2.1,vals.2.2]; exact hJ
  · rw [kc _ (by simp),b2,hz2,vz]
  · rw [kc _ (by simp),b3,hz3,vz]

theorem entryLoadFields_ok {base : Addr} {size a : Nat} {C : Curve} {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hsize : 6512≤size)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hi : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2=BitVec.ofNat 64 a) (ha : 1≤a) (ha8 : a≤8)
    (hD : ∀ x∈entryWrites,Sl x)
    (hT : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z,
      6000+64*(a-1),6032+64*(a-1)],x∈V)
    :
    WP isa (.block (CachedJac.load++Jacobian.publicEntry K)) s fun t =>
      ProgKeep K.M base entryWrites s t ∧
      Inv K.M base size C.p Sl (entryLive V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
        (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) ∧
      tmv C K.M.n base t 5400=E (6000+64*(a-1)) ∧
      tmv C K.M.n base t 5432=E (6032+64*(a-1)) := by
  have dc : ∀ x∈[5400,5432],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have de : ∀ x∈[K.E.x,K.E.y,K.E.z],Sl x := fun x hx => hD x (by
    simp only [entryWrites,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  have st : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],x∈V :=
    fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)
  rw [WP.block_append_iff]
  refine WP.mono (cachedLoadField_ok hL (by rfl) hi h2 ha ha8 hsize dc
    (fun x hx => hT x (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)))
    fun b ⟨kb,ib,b2,b3,bidx0⟩ => ?_
  have bt : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      tmv C K.M.n base b x=E x := by
    intro x hx
    rw [tmv_keep hL kb hi.scr.nowrap dc (hi.sl x (st x hx)) ?_]
    exact hi.val x (st x hx)
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rw [not_or]
    have ht : K.tbl=2848 := rfl
    rw [ht] at hx
    omega
  have bidx : b.gpr .x2=BitVec.ofNat 64 a := bidx0.trans h2
  refine WP.mono (jacPublicFields_ok hL hAl (by rfl) (by rfl) (by rfl) ib bidx ha (by decide)
    de (fun x hx => List.mem_append_right _ (st x hx)) (Or.inl (by change 704+96≤2848+96*(a-1); omega)))
    fun t ⟨kt,it,vt⟩ => ?_
  have vals : (tmv C K.M.n base t K.E.x,tmv C K.M.n base t K.E.y,tmv C K.M.n base t K.E.z)=
      (E (Jacobian.tablePt K a).x,E (Jacobian.tablePt K a).y,E (Jacobian.tablePt K a).z) := by
    rw [vt,bt _ (by simp),bt _ (by simp),bt _ (by simp)]
  have kc : ∀ x∈[5400,5432],tmv C K.M.n base t x=tmv C K.M.n base b x := by
    intro x hx
    exact tmv_keep hL kt ib.scr.nowrap de (dc x hx) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  exact ⟨(kb.mono (by simp [entryWrites])).trans (kt.mono (by simp [entryWrites])),it,
    vals,(kc _ (by simp)).trans b2,(kc _ (by simp)).trans b3⟩

end VG.Proof.Weierstrass.AArch64.CachedField
