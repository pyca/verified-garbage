import VerifiedGarbage.Proof.P256.EcdhJac.CopyD

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

 theorem storeCoZ_ok {base : Addr} {P : Point C} {k m : Nat} {s : State}
    (hm : 1≤m) (hm16 : m≤16) (hf : Fixed base P k s)
    (ht : TblOk base P (m-1) s) (hp : JPt base s selectedSlot (mul m P))
    (hl : ∀x∈[K.D.x,K.D.y],wordsVal s.mem base x 4<C.p)
    (hd : InvJ C (tmv C 4 base s K.D.x) (tmv C 4 base s K.D.y) (tmv C 4 base s K.E.z) P)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block Impl.P256.EcdhJac.storeEntry) s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k m t := by
  refine WP.mono (storePoint_ok hf.field.scr hm hm16 h19 hp) fun t ⟨kt,ot,pt,ct⟩ => ?_
  have old := table_store ht (by omega) ot
  have selected := selected_store hp hm hm16 ot
  have hv : ∀x∈[K.D.x,K.D.y,K.E.z],wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    intro x hx
    exact ot.wordsVal (by
      have h : x=608∨x=640∨x=768 := by
        simpa only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,show K.E.z=768 from rfl,List.mem_cons,List.not_mem_nil,or_false] using hx
      rcases h with rfl|rfl|rfl <;> omega) (by
      have h : x=608∨x=640∨x=768 := by
        simpa only [show K.D.x=608 from rfl,show K.D.y=640 from rfl,show K.E.z=768 from rfl,List.mem_cons,List.not_mem_nil,or_false] using hx
      rcases h with rfl|rfl|rfl <;> omega)
  refine ⟨kt,⟨⟨hf.keep kt,?_,selected,ct.trans h19⟩,?_,?_⟩⟩
  · intro a ha ham
    by_cases h : a=m
    · subst a; exact pt
    · exact old a ha (by omega)
  · intro x hx
    rw [hv x (by
      rcases List.mem_cons.mp hx with rfl|hx
      · decide
      · rw [List.mem_singleton.mp hx]; decide)]
    exact hl x hx
  · have vx := congrArg (fun x => toM C.p (2^256) x) (hv K.D.x (by decide))
    have vy := congrArg (fun x => toM C.p (2^256) x) (hv K.D.y (by decide))
    have vz := congrArg (fun x => toM C.p (2^256) x) (hv K.E.z (by decide))
    change tmv C 4 base t K.D.x=tmv C 4 base s K.D.x at vx
    change tmv C 4 base t K.D.y=tmv C 4 base s K.D.y at vy
    change tmv C 4 base t K.E.z=tmv C 4 base s K.E.z at vz
    rw [vx,vy,vz]
    exact hd

end VG.Proof.P256.EcdhJac
