module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryEnv

/-! Lift arithmetic postconditions to updates of ordinary-field slot environments. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

section
variable {base : Addr} {p : Nat} [NeZero p] {loc : Nat → Nat} {V : List Nat}
  {E : Nat → Fin p} {caps : Nat → Nat} {s t : State} {o cap a b : Nat}
  (h : OrdinaryInv base p loc V E caps s) (ha : a∈V) (hb : b∈V)
  (outside : Outside base (loc o) 72 s.mem t.mem)
  (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) (fits : ∀x∈V,loc x+72≤2^64)
  (bound : wordsVal t.mem base (loc o) 9<cap*p)

include h ha hb outside apart fits bound

theorem OrdinaryInv.mul_update
    (value : wordsVal t.mem base (loc o) 9%p=wordsVal s.mem base (loc a) 9*wordsVal s.mem base (loc b) 9%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (E a*E b)) (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  have e : Fin.ofNat p (wordsVal t.mem base (loc o) 9)=Fin.ofNat p (wordsVal s.mem base (loc a) 9*wordsVal s.mem base (loc b) 9) :=
    ofNat_eq_ofNat.mpr value
  rw [ofNat_mul',h.value a ha,h.value b hb] at e
  exact e

theorem OrdinaryInv.add_update
    (value : wordsVal t.mem base (loc o) 9=(wordsVal s.mem base (loc a) 9+wordsVal s.mem base (loc b) 9)%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (E a+E b)) (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  rw [value,ordinary_add,h.value a ha,h.value b hb]

theorem OrdinaryInv.sub_update
    (bBound : wordsVal s.mem base (loc b) 9≤wordsVal s.mem base (loc a) 9+p)
    (value : wordsVal t.mem base (loc o) 9=(wordsVal s.mem base (loc a) 9+p-wordsVal s.mem base (loc b) 9)%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (E a-E b)) (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  rw [value,ordinary_sub bBound,h.value a ha,h.value b hb]

theorem OrdinaryInv.cms_update (C D : Nat) (bBound : wordsVal s.mem base (loc b) 9≤p)
    (value : wordsVal t.mem base (loc o) 9=(C*wordsVal s.mem base (loc a) 9+D*(p-wordsVal s.mem base (loc b) 9))%p) :
    OrdinaryInv base p loc (o::V) (Function.update E o (Cms.smulN C (E a)-Cms.smulN D (E b)))
      (Function.update caps o cap) t := by
  refine h.update outside apart fits bound ?_
  rw [value,ordinary_cms C _ D _ bBound,h.value a ha,h.value b hb]

end
end VG.Proof.Mont.AArch64.P521Field
